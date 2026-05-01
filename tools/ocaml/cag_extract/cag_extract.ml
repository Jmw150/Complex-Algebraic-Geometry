(** cag-extract — one-command extraction of a Rocq Definition to runnable OCaml.
    Mirrors the Python prototype (cli.py) in user-visible behaviour.

    Usage:
      cag_extract NAME [--root PATH] [--output-dir DIR] [--build] [--run "body"]

    Steps:
      1. Locate NAME in the project via Cag_lib.Rocq_parse.walk_theories.
      2. Generate a .v stub at <output-dir>/_extract_NAME.v.
      3. Run `rocq compile -Q theories CAG <stub>` from the project root.
      4. Optionally compile the produced .ml with ocamlfind/ocamlc.
      5. Optionally link + run a tiny driver. *)

open Cag_lib
open Cmdliner

(* ------------------------------------------------------------------ *)
(* Helpers                                                             *)
(* ------------------------------------------------------------------ *)

(** Walk up from [start] looking for _CoqProject. *)
let detect_root start =
  let rec walk p =
    if Sys.file_exists (Filename.concat p "_CoqProject") then Some p
    else
      let parent = Filename.dirname p in
      if parent = p then None else walk parent
  in
  match walk start with
  | Some r -> r
  | None ->
      Printf.eprintf "error: no _CoqProject found above %s\n" start;
      exit 1

(** Given an absolute [file] path under [theories_root], derive the CAG.*
    module path.  E.g. .../theories/Algebra/Foo.v -> "CAG.Algebra.Foo". *)
let file_to_module theories_root file =
  (* Normalise: strip trailing slash *)
  let root =
    let n = String.length theories_root in
    if n > 0 && theories_root.[n-1] = '/' then String.sub theories_root 0 (n-1)
    else theories_root
  in
  let rlen = String.length root in
  let flen = String.length file in
  if flen <= rlen + 1 then None
  else if String.sub file 0 rlen <> root then None
  else begin
    (* strip root/ prefix *)
    let rel = String.sub file (rlen + 1) (flen - rlen - 1) in
    (* strip .v suffix *)
    let rel =
      if Filename.check_suffix rel ".v"
      then Filename.chop_suffix rel ".v"
      else rel
    in
    (* replace '/' with '.' *)
    let parts = String.split_on_char '/' rel in
    Some ("CAG." ^ String.concat "." parts)
  end

(** Search walk_theories for a declaration named [name]; return its CAG module. *)
let find_module root name =
  let theories_dir = Filename.concat root "theories" in
  let result = ref None in
  (try
    Rocq_parse.walk_theories theories_dir
    |> Seq.iter (fun (d : Rocq_parse.declaration) ->
         if d.name = name then begin
           (match file_to_module theories_dir d.file with
            | Some m -> result := Some m
            | None   -> ());
           raise Exit
         end)
  with Exit -> ());
  !result

(** Ensure a directory exists (mkdir -p equivalent, one level). *)
let ensure_dir path =
  if not (Sys.file_exists path) then
    Unix.mkdir path 0o755

let ensure_dir_p path =
  (* Split on '/' and rebuild, creating missing components *)
  let parts = String.split_on_char '/' path in
  let _ = List.fold_left (fun acc part ->
    if part = "" then acc
    else begin
      let p = if acc = "" then part else acc ^ "/" ^ part in
      if not (Sys.file_exists p) then
        (try Unix.mkdir p 0o755 with Unix.Unix_error (Unix.EEXIST, _, _) -> ());
      p
    end
  ) "" parts in
  ()

(** Write a string to a file, overwriting if it exists. *)
let write_file path content =
  let oc = open_out path in
  output_string oc content;
  close_out oc

(** Run a command, printing it first.  Returns (exit_code, stdout, stderr). *)
let run_cmd ?(cwd=None) argv =
  let cmd = String.concat " " (Array.to_list argv) in
  Printf.printf "$ %s\n%!" cmd;
  (* Use Unix.create_process_env with pipes to capture output *)
  let (out_r, out_w) = Unix.pipe () in
  let (err_r, err_w) = Unix.pipe () in
  let pid =
    let old_cwd = Sys.getcwd () in
    (match cwd with Some d -> Unix.chdir d | None -> ());
    let p = Unix.create_process argv.(0) argv Unix.stdin out_w err_w in
    (match cwd with Some _ -> Unix.chdir old_cwd | None -> ());
    p
  in
  Unix.close out_w;
  Unix.close err_w;
  let read_all fd =
    let buf = Buffer.create 256 in
    let chunk = Bytes.create 4096 in
    let rec loop () =
      let n = Unix.read fd chunk 0 4096 in
      if n > 0 then begin
        Buffer.add_subbytes buf chunk 0 n;
        loop ()
      end
    in
    (try loop () with End_of_file -> ());
    Buffer.contents buf
  in
  let stdout_str = read_all out_r in
  let stderr_str = read_all err_r in
  Unix.close out_r;
  Unix.close err_r;
  let (_, status) = Unix.waitpid [] pid in
  let code = match status with
    | Unix.WEXITED n -> n
    | Unix.WSIGNALED _ -> 130
    | Unix.WSTOPPED  _ -> 130
  in
  (code, stdout_str, stderr_str)

(** Check if a program is on PATH. *)
let have prog =
  let (code, _, _) = run_cmd [| "which"; prog |] in
  code = 0

(* ------------------------------------------------------------------ *)
(* Main logic                                                          *)
(* ------------------------------------------------------------------ *)

let cmd_extract name root_opt output_dir_opt build_flag run_body_opt =
  let root = match root_opt with
    | Some r -> r
    | None   -> detect_root (Sys.getcwd ())
  in
  let module_ = find_module root name in
  let module_ = match module_ with
    | Some m -> m
    | None ->
        Printf.eprintf "error: no declaration named '%s' found\n" name;
        exit 2
  in

  let out_dir = match output_dir_opt with
    | Some d -> d
    | None   -> Filename.concat (Filename.concat root ".cag") "extract"
  in
  ensure_dir_p out_dir;

  (* Write the .v stub *)
  let stub_path = Filename.concat out_dir (Printf.sprintf "_extract_%s.v" name) in
  let stub_content =
    Printf.sprintf
      "Require Import %s.\n\
       Require Coq.extraction.Extraction.\n\
       Extraction Language OCaml.\n\
       Cd \"%s\".\n\
       Extraction \"%s\" %s.\n"
      module_ out_dir name name
  in
  write_file stub_path stub_content;

  (* Run rocq compile *)
  let rocq = (try Sys.getenv "ROCQ" with Not_found -> "rocq") in
  let compile_argv = [| rocq; "compile"; "-Q"; "theories"; "CAG"; stub_path |] in
  let (rc, stdout_str, stderr_str) = run_cmd ~cwd:(Some root) compile_argv in
  if rc <> 0 then begin
    if stderr_str <> "" then Printf.eprintf "%s" stderr_str;
    if stdout_str <> "" then Printf.eprintf "%s" stdout_str;
    exit rc
  end;

  (* Check the .ml was produced *)
  let ml_path  = Filename.concat out_dir (name ^ ".ml") in
  let mli_path = Filename.concat out_dir (name ^ ".mli") in
  if not (Sys.file_exists ml_path) then begin
    Printf.eprintf "error: extraction did not produce %s\n" ml_path;
    exit 3
  end;
  Printf.printf "extracted: %s\n" ml_path;
  if Sys.file_exists mli_path then
    Printf.printf "           %s\n" mli_path;

  (* --build / --run *)
  if build_flag || run_body_opt <> None then begin
    if not (have "ocamlfind") then begin
      Printf.eprintf "warn: ocamlfind not found; skipping build\n";
      exit 0
    end;
    (* Compile the .ml *)
    let build_argv = [| "ocamlfind"; "ocamlc"; "-package"; "str"; "-c"; ml_path |] in
    let (brc, _, bstderr) = run_cmd ~cwd:(Some out_dir) build_argv in
    if brc <> 0 then begin
      if bstderr <> "" then Printf.eprintf "%s" bstderr;
      exit brc
    end;

    (match run_body_opt with
     | None -> ()
     | Some body ->
         (* Write a tiny driver *)
         let driver_path = Filename.concat out_dir (Printf.sprintf "_run_%s.ml" name) in
         let cap = String.capitalize_ascii name in
         let driver_content =
           Printf.sprintf "open %s\nlet () =\n  %s\n" cap body
         in
         write_file driver_path driver_content;
         (* Link *)
         let cmo = name ^ ".cmo" in
         let link_argv = [|
           "ocamlfind"; "ocamlc"; "-package"; "str"; "-linkpkg";
           cmo; driver_path; "-o"; Printf.sprintf "_run_%s" name
         |] in
         let (lrc, _, lstderr) = run_cmd ~cwd:(Some out_dir) link_argv in
         if lrc <> 0 then begin
           if lstderr <> "" then Printf.eprintf "%s" lstderr;
           exit lrc
         end;
         (* Run *)
         let exe = Filename.concat out_dir (Printf.sprintf "_run_%s" name) in
         let (rrc, rout, rerr) = run_cmd [| exe |] in
         if rout <> "" then print_string rout;
         if rerr <> "" then Printf.eprintf "%s" rerr;
         if rrc <> 0 then exit rrc)
  end;
  0

(* ------------------------------------------------------------------ *)
(* Cmdliner wiring                                                     *)
(* ------------------------------------------------------------------ *)

let () =
  let name_arg =
    Arg.(required & pos 0 (some string) None
         & info [] ~docv:"NAME"
             ~doc:"Name of the Definition / Fixpoint to extract")
  in
  let root_opt =
    Arg.(value & opt (some string) None
         & info ["root"] ~docv:"PATH"
             ~doc:"Project root (default: walk up from CWD for _CoqProject)")
  in
  let output_dir_opt =
    Arg.(value & opt (some string) None
         & info ["output-dir"] ~docv:"DIR"
             ~doc:"Where to put the generated .ml (default: .cag/extract/)")
  in
  let build_flag =
    Arg.(value & flag
         & info ["build"]
             ~doc:"Compile the generated .ml with ocamlc after extraction")
  in
  let run_opt =
    Arg.(value & opt (some string) None
         & info ["run"] ~docv:"BODY"
             ~doc:"OCaml driver body to compile and run (implies --build)")
  in
  let run main name root out_dir build run_body =
    exit (main name root out_dir build run_body)
  in
  let term =
    Term.(const run $ const cmd_extract $ name_arg $ root_opt
          $ output_dir_opt $ build_flag $ run_opt)
  in
  let info_ = Cmd.info "cag-extract" ~version:"0.1"
    ~doc:"Extract a Rocq definition to runnable OCaml via Rocq's Extraction mechanism"
  in
  exit (Cmd.eval' (Cmd.v info_ term))
