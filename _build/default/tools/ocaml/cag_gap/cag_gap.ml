(** cag-gap — bridge to the GAP computer algebra system.
    Mirrors the Python prototype (cli.py) in user-visible behaviour.

    Subcommands:
      eval EXPR          Evaluate a GAP expression and print the result.
      run  SCRIPT        Run a GAP script file.
      q15  [options]     Run the bundled Q1.5 candidate-search script.

    GAP binary: $GAP env-var, or `which gap`, or /usr/bin/gap. *)

open Cmdliner

(* ------------------------------------------------------------------ *)
(* Helpers                                                             *)
(* ------------------------------------------------------------------ *)

(** Find the project root by walking up from [start] looking for _CoqProject. *)
let detect_root start =
  let rec walk p =
    if Sys.file_exists (Filename.concat p "_CoqProject") then Some p
    else
      let parent = Filename.dirname p in
      if parent = p then None else walk parent
  in
  walk start

(** Return the GAP binary path. Checks $GAP, then `which gap`, then /usr/bin/gap. *)
let gap_bin () =
  match (try Some (Sys.getenv "GAP") with Not_found -> None) with
  | Some g -> g
  | None ->
      (* Try `which gap` *)
      let ic = Unix.open_process_in "which gap 2>/dev/null" in
      let line = (try String.trim (input_line ic) with End_of_file -> "") in
      let _ = Unix.close_process_in ic in
      if line <> "" then line else "/usr/bin/gap"

(** Write a temporary GAP script and return its path. *)
let write_tmp_script content =
  let tmp = Filename.temp_file "cag_gap_" ".g" in
  let oc = open_out tmp in
  output_string oc content;
  close_out oc;
  tmp

(** Run [argv] as a subprocess, streaming stdout to our stdout, stderr to our
    stderr.  Returns the exit code. *)
let run_process argv =
  let pid = Unix.create_process argv.(0) argv Unix.stdin Unix.stdout Unix.stderr in
  let (_, status) = Unix.waitpid [] pid in
  match status with
  | Unix.WEXITED n  -> n
  | Unix.WSIGNALED _ -> 130
  | Unix.WSTOPPED  _ -> 130

(** Run [argv], capturing stdout + stderr separately.  Returns (code, out, err). *)
let run_process_capture argv =
  let (out_r, out_w) = Unix.pipe () in
  let (err_r, err_w) = Unix.pipe () in
  let pid = Unix.create_process argv.(0) argv Unix.stdin out_w err_w in
  Unix.close out_w;
  Unix.close err_w;
  let read_all fd =
    let buf = Buffer.create 512 in
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
  let out_str = read_all out_r in
  let err_str = read_all err_r in
  Unix.close out_r;
  Unix.close err_r;
  let (_, status) = Unix.waitpid [] pid in
  let code = match status with
    | Unix.WEXITED n  -> n
    | Unix.WSIGNALED _ -> 130
    | Unix.WSTOPPED  _ -> 130
  in
  (code, out_str, err_str)

(* ------------------------------------------------------------------ *)
(* Subcommand: eval                                                    *)
(* ------------------------------------------------------------------ *)

let cmd_eval expr =
  let gap = gap_bin () in
  if not (Sys.file_exists gap) then begin
    Printf.eprintf "error: GAP not found at %s; install with apt or set GAP=...\n" gap;
    exit 2
  end;
  (* Strip trailing semicolons and whitespace, matching the Python behaviour *)
  let expr = String.trim (
    let s = ref expr in
    while String.length !s > 0 && !s.[String.length !s - 1] = ';' do
      s := String.sub !s 0 (String.length !s - 1)
    done;
    !s) in
  let script_body = Printf.sprintf "Print(%s, \"\\n\");\nQUIT;\n" expr in
  let tmp = write_tmp_script script_body in
  let rc =
    (try
      let argv = [| gap; "-q"; "-b"; tmp |] in
      run_process argv
    with e ->
      (try Sys.remove tmp with _ -> ());
      raise e)
  in
  (try Sys.remove tmp with _ -> ());
  rc

(* ------------------------------------------------------------------ *)
(* Subcommand: run                                                     *)
(* ------------------------------------------------------------------ *)

let cmd_run script =
  let gap = gap_bin () in
  if not (Sys.file_exists gap) then begin
    Printf.eprintf "error: GAP not found at %s; install with apt or set GAP=...\n" gap;
    exit 2
  end;
  if not (Sys.file_exists script) then begin
    Printf.eprintf "error: script not found: %s\n" script;
    exit 2
  end;
  let argv = [| gap; "-q"; "-b"; script |] in
  run_process argv

(* ------------------------------------------------------------------ *)
(* Subcommand: q15                                                     *)
(* ------------------------------------------------------------------ *)

(** Try to find the q15_search.g script.  We look relative to the executable
    location first, then walk up for _CoqProject and use tools/cag_gap/ there. *)
let find_q15_script () =
  (* Strategy 1: walk up from cwd for _CoqProject *)
  (match detect_root (Sys.getcwd ()) with
   | Some root ->
       let p = Filename.concat root
                 (Filename.concat "tools"
                   (Filename.concat "cag_gap" "q15_search.g")) in
       if Sys.file_exists p then Some p else None
   | None -> None)

let cmd_q15 min_order max_order =
  let gap = gap_bin () in
  if not (Sys.file_exists gap) then begin
    Printf.eprintf "error: GAP not found at %s; install with apt or set GAP=...\n" gap;
    exit 2
  end;
  let script_path = match find_q15_script () with
    | Some p -> p
    | None ->
        Printf.eprintf "error: bundled q15_search.g not found; run from inside the project\n";
        exit 2
  in
  let init_code =
    Printf.sprintf "MIN_ORD := %d; MAX_ORD := %d;" min_order max_order
  in
  Printf.eprintf "# scanning small groups of order %d..%d\n%!" min_order max_order;
  let argv = [| gap; "-q"; "-b"; "--norepl"; "-c"; init_code; script_path |] in
  let (rc, out_str, err_str) = run_process_capture argv in
  if rc <> 0 then begin
    if err_str <> "" then Printf.eprintf "%s" err_str;
    exit rc
  end;
  (* Print all stdout *)
  if out_str <> "" then print_string out_str;
  (* Count JSON candidate lines *)
  let lines = String.split_on_char '\n' out_str in
  let candidates = List.filter (fun line ->
    let line = String.trim line in
    String.length line > 0 && line.[0] = '{'
  ) lines in
  let n_cands = List.length candidates in
  Printf.eprintf "---\ncandidates found: %d\n" n_cands;
  (* Count non-iso by looking for "iso":false in each candidate line *)
  let re_noniso =
    (* Simple string search for "iso":false *)
    let s = {|"iso":false|} in
    let slen = String.length s in
    fun line ->
      let llen = String.length line in
      let found = ref false in
      for i = 0 to llen - slen do
        if String.sub line i slen = s then found := true
      done;
      !found
  in
  let nonisos = List.filter re_noniso candidates in
  if nonisos <> [] then begin
    Printf.eprintf "NON-ISOMORPHIC candidates (potential Q1.5 leads): %d\n"
      (List.length nonisos);
    List.iter (fun line ->
      Printf.eprintf "  %s\n" (String.trim line)
    ) nonisos
  end else begin
    Printf.eprintf "no non-isomorphic candidate in this range\n"
  end;
  0

(* ------------------------------------------------------------------ *)
(* Cmdliner wiring                                                     *)
(* ------------------------------------------------------------------ *)

(* ---------- eval ---------------------------------------------------- *)

let eval_cmd =
  let expr_arg =
    Arg.(required & pos 0 (some string) None
         & info [] ~docv:"EXPR"
             ~doc:"GAP expression to evaluate (semicolons optional)")
  in
  let run expr = exit (cmd_eval expr) in
  let term = Term.(const run $ expr_arg) in
  let info_ = Cmd.info "eval" ~doc:"Evaluate a single GAP expression and print the result" in
  Cmd.v info_ term

(* ---------- run ---------------------------------------------------- *)

let run_cmd_ =
  let script_arg =
    Arg.(required & pos 0 (some string) None
         & info [] ~docv:"SCRIPT"
             ~doc:"Path to a GAP script file to run")
  in
  let run script = exit (cmd_run script) in
  let term = Term.(const run $ script_arg) in
  let info_ = Cmd.info "run" ~doc:"Run a GAP script file" in
  Cmd.v info_ term

(* ---------- q15 ---------------------------------------------------- *)

let q15_cmd =
  let min_order_opt =
    Arg.(value & opt int 1
         & info ["min-order"] ~docv:"N"
             ~doc:"Minimum group order to search (default: 1)")
  in
  let max_order_opt =
    Arg.(value & opt int 63
         & info ["max-order"] ~docv:"N"
             ~doc:"Maximum group order to search (default: 63)")
  in
  let run min max = exit (cmd_q15 min max) in
  let term = Term.(const run $ min_order_opt $ max_order_opt) in
  let info_ = Cmd.info "q15"
    ~doc:"Run the bundled Q1.5 candidate-search script against GAP's small-groups library" in
  Cmd.v info_ term

(* ---------- top-level group --------------------------------------- *)

let () =
  let info_ = Cmd.info "cag-gap" ~version:"0.1"
    ~doc:"Bridge to the GAP computer algebra system" in
  let default_term =
    let run () =
      Printf.printf "Usage: cag-gap {eval EXPR | run SCRIPT | q15 [--min-order N] [--max-order N]}\n";
      Printf.printf "  eval EXPR      Evaluate a GAP expression\n";
      Printf.printf "  run  SCRIPT    Run a GAP script file\n";
      Printf.printf "  q15            Run Q1.5 candidate search\n";
      exit 0
    in
    Term.(const run $ const ())
  in
  exit (Cmd.eval (Cmd.group ~default:default_term info_
    [ eval_cmd; run_cmd_; q15_cmd ]))
