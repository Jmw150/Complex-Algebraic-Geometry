(** cag-audit — axiom/parameter monitoring for the Complex-Algebraic-Geometry
    project.  Mirrors the Python prototype (cli.py) in user-visible behaviour.

    Subcommands:
      list      — list all Axioms / Parameters, with optional filters
      snapshot  — write JSON snapshot to .cag/audit-snapshot.json
      diff      — compare current state vs snapshot
      suspect   — flag suspicious-shape declarations
    (check subcommand intentionally omitted; it shells out to rocq compile.) *)

open Cag_lib
open Cmdliner

(* ------------------------------------------------------------------ *)
(* Helpers                                                             *)
(* ------------------------------------------------------------------ *)

let snapshot_rel = Filename.concat ".cag" "audit-snapshot.json"

(** Walk up from [start] looking for a directory that contains _CoqProject. *)
let detect_root start =
  let rec walk p =
    if Sys.file_exists (Filename.concat p "_CoqProject") then Some p
    else
      let parent = Filename.dirname p in
      if parent = p then None else walk parent
  in
  match walk (Filename.concat start "" |> String.trim) with
  | Some r -> r
  | None ->
      Printf.eprintf "error: no _CoqProject found above %s\n" start;
      exit 1

(** Collect every Axiom / Parameter under [root]/theories. *)
let collect root =
  let theories_dir = Filename.concat root "theories" in
  Rocq_parse.walk_theories theories_dir
  |> Seq.filter (fun (d : Rocq_parse.declaration) ->
       d.kind = Rocq_parse.Axiom || d.kind = Rocq_parse.Parameter)
  |> List.of_seq

(** Return a path relative to [root] if possible, otherwise the original path. *)
let rel_to root path =
  (* Normalise: strip trailing slash from root *)
  let root =
    let n = String.length root in
    if n > 0 && root.[n-1] = '/' then String.sub root 0 (n-1) else root
  in
  let rlen = String.length root in
  let flen = String.length path in
  if flen > rlen + 1
     && String.sub path 0 rlen = root
     && path.[rlen] = '/'
  then String.sub path (rlen + 1) (flen - rlen - 1)
  else path

(** First line of a (possibly multi-line) string. *)
let first_line s =
  match String.index_opt s '\n' with
  | None -> s
  | Some k -> String.sub s 0 k

(** Truncate a string to at most [n] chars. *)
let trunc n s =
  if String.length s > n then String.sub s 0 n ^ "..." else s

(* ------------------------------------------------------------------ *)
(* Terminal colour helpers (same pattern as cag_search)               *)
(* ------------------------------------------------------------------ *)

let isatty = Unix.isatty Unix.stdout
let no_color = (try Sys.getenv "NO_COLOR" <> "" with Not_found -> false)

let color code text =
  if isatty && not no_color
  then Printf.sprintf "\027[%sm%s\027[0m" code text
  else text

(* ------------------------------------------------------------------ *)
(* JSON serialisation (manual, no dependency)                         *)
(* ------------------------------------------------------------------ *)

(** Escape a string for JSON. *)
let json_escape s =
  let buf = Buffer.create (String.length s + 8) in
  String.iter (fun c ->
    match c with
    | '"'  -> Buffer.add_string buf "\\\""
    | '\\' -> Buffer.add_string buf "\\\\"
    | '\n' -> Buffer.add_string buf "\\n"
    | '\r' -> Buffer.add_string buf "\\r"
    | '\t' -> Buffer.add_string buf "\\t"
    | c    -> Buffer.add_char buf c
  ) s;
  Buffer.contents buf

let json_string s = Printf.sprintf "\"%s\"" (json_escape s)

(** Build a JSON object from a list of (key, value-already-serialised) pairs. *)
let json_obj pairs =
  let buf = Buffer.create 128 in
  Buffer.add_char buf '{';
  List.iteri (fun i (k, v) ->
    if i > 0 then Buffer.add_string buf ", ";
    Buffer.add_string buf (json_string k);
    Buffer.add_char buf ':';
    Buffer.add_string buf v
  ) pairs;
  Buffer.add_char buf '}';
  Buffer.contents buf

(* ------------------------------------------------------------------ *)
(* Snapshot / diff key                                                 *)
(* ------------------------------------------------------------------ *)

let decl_key (d : Rocq_parse.declaration) =
  Printf.sprintf "%s::%s"
    (Rocq_parse.string_of_kind d.kind) d.name

(* ------------------------------------------------------------------ *)
(* Subcommand: list                                                    *)
(* ------------------------------------------------------------------ *)

let cmd_list root kind_filter file_filter summary =
  let decls = collect root in
  (* Apply kind filter (case-insensitive prefix capitalise, like Python) *)
  let decls = match kind_filter with
    | None -> decls
    | Some k ->
        let k_norm =
          let n = String.length k in
          if n = 0 then k
          else
            String.uppercase_ascii (String.sub k 0 1) ^
            String.lowercase_ascii (String.sub k 1 (n-1))
        in
        List.filter (fun (d : Rocq_parse.declaration) ->
          Rocq_parse.string_of_kind d.kind = k_norm) decls
  in
  (* Apply file substring filter *)
  let decls = match file_filter with
    | None -> decls
    | Some f ->
        List.filter (fun (d : Rocq_parse.declaration) ->
          let idx =
            try
              let flen = String.length f in
              let dlen = String.length d.file in
              let found = ref false in
              for i = 0 to dlen - flen do
                if String.sub d.file i flen = f then found := true
              done;
              !found
            with _ -> false
          in idx) decls
  in
  (* Count by kind *)
  let by_kind : (string, int) Hashtbl.t = Hashtbl.create 8 in
  List.iter (fun (d : Rocq_parse.declaration) ->
    let k = Rocq_parse.string_of_kind d.kind in
    Hashtbl.replace by_kind k (1 + try Hashtbl.find by_kind k with Not_found -> 0)
  ) decls;
  (* Print entries if not summary mode *)
  if not summary then
    List.iter (fun (d : Rocq_parse.declaration) ->
      let rel = rel_to root d.file in
      let kind_str = color "33" (Printf.sprintf "[%s]" (Rocq_parse.string_of_kind d.kind)) in
      let name_str = color "1;36" d.name in
      let loc_str  = color "2" (Printf.sprintf "%s:%d" rel d.line) in
      Printf.printf "%s %s  %s\n" kind_str name_str loc_str;
      let preview = trunc 100 (String.trim (first_line d.statement)) in
      if preview <> "" then Printf.printf "    %s\n" preview
    ) decls;
  (* Summary counts *)
  Printf.printf "\ntotal: %d\n" (List.length decls);
  let pairs = Hashtbl.fold (fun k v acc -> (k, v) :: acc) by_kind [] in
  let sorted = List.sort (fun (_, a) (_, b) -> compare b a) pairs in
  List.iter (fun (k, v) -> Printf.printf "  %-14s %d\n" k v) sorted;
  0

(* ------------------------------------------------------------------ *)
(* Subcommand: snapshot                                                *)
(* ------------------------------------------------------------------ *)

(** Return current UTC time as ISO-8601 string YYYY-MM-DDTHH:MM:SS. *)
let iso8601_now () =
  let t = Unix.gmtime (Unix.time ()) in
  Printf.sprintf "%04d-%02d-%02dT%02d:%02d:%02d"
    (t.Unix.tm_year + 1900)
    (t.Unix.tm_mon  + 1)
    t.Unix.tm_mday
    t.Unix.tm_hour
    t.Unix.tm_min
    t.Unix.tm_sec

let cmd_snapshot root =
  let decls = collect root in
  let generated = iso8601_now () in
  let total = List.length decls in
  (* Build JSON items list (comma-separated objects, no outer brackets) *)
  let items_inner =
    let buf = Buffer.create (total * 120) in
    List.iteri (fun i (d : Rocq_parse.declaration) ->
      if i > 0 then Buffer.add_string buf ",\n    ";
      let file_rel = rel_to root d.file in
      let stmt_first = first_line d.statement in
      let obj = json_obj [
        ("kind",                 json_string (Rocq_parse.string_of_kind d.kind));
        ("name",                 json_string d.name);
        ("file",                 json_string file_rel);
        ("line",                 string_of_int d.line);
        ("statement_first_line", json_string stmt_first);
      ] in
      Buffer.add_string buf obj
    ) decls;
    Buffer.contents buf
  in
  let json =
    Printf.sprintf "{\n  \"generated\": %s,\n  \"total\": %d,\n  \"items\": [\n    %s\n  ]\n}\n"
      (json_string generated) total items_inner
  in
  (* Ensure .cag/ directory exists *)
  let snap_path = Filename.concat root snapshot_rel in
  let snap_dir  = Filename.dirname snap_path in
  if not (Sys.file_exists snap_dir) then Unix.mkdir snap_dir 0o755;
  let oc = open_out snap_path in
  output_string oc json;
  close_out oc;
  Printf.printf "snapshot: %d entries -> %s\n" total snap_path;
  0

(* ------------------------------------------------------------------ *)
(* Subcommand: diff                                                    *)
(* ------------------------------------------------------------------ *)

(** Minimal JSON object parser: extract a string value for [key]. *)
let json_get_string json key =
  (* Match "key":"value" — good enough for our controlled JSON *)
  let pat = Printf.sprintf {|"%s"\s*:\s*"([^"]*)"|}  key in
  let re = Re.Perl.compile_pat pat in
  match Re.exec_opt re json with
  | None -> None
  | Some g -> Some (Re.Group.get g 1)

let json_get_int json key =
  let pat = Printf.sprintf {|"%s"\s*:\s*([0-9]+)|} key in
  let re = Re.Perl.compile_pat pat in
  match Re.exec_opt re json with
  | None -> None
  | Some g -> (try Some (int_of_string (Re.Group.get g 1)) with _ -> None)

(** Parse items array from snapshot JSON.  Returns list of
    (kind, name, file, line) tuples.

    Strategy: the snapshot we write has each item on exactly one line
    (json_obj serialises inline, and statement_first_line has no raw newlines).
    So we split on newlines and test each line for the presence of "kind":"...",
    "name":"...", etc.  This avoids problems with {/} inside field values. *)
let parse_snapshot_items json =
  let lines = String.split_on_char '\n' json in
  List.filter_map (fun line ->
    let line = String.trim line in
    (* Each item line contains "kind":"..." — use that as a discriminator *)
    if not (Re.execp (Re.Perl.compile_pat {|"kind"\s*:|}) line) then None
    else
      match json_get_string line "kind", json_get_string line "name",
            json_get_string line "file", json_get_int   line "line" with
      | Some kind, Some name, Some file, Some line_num ->
          Some (kind, name, file, line_num)
      | _ -> None
  ) lines

let cmd_diff root =
  let snap_path = Filename.concat root snapshot_rel in
  if not (Sys.file_exists snap_path) then begin
    Printf.eprintf
      "no snapshot at %s; run `cag-audit snapshot` first to create one\n"
      snap_path;
    exit 2
  end;
  (* Read snapshot *)
  let snap_json =
    let ic = open_in snap_path in
    let n  = in_channel_length ic in
    let s  = really_input_string ic n in
    close_in ic; s
  in
  let snap_generated = Option.value ~default:"unknown"
    (json_get_string snap_json "generated") in
  let snap_total = Option.value ~default:0
    (json_get_int snap_json "total") in
  let snap_items = parse_snapshot_items snap_json in
  (* Build snap key → (kind,name,file,line) map *)
  let snap_map : (string, string * string * string * int) Hashtbl.t =
    Hashtbl.create (List.length snap_items) in
  List.iter (fun (kind, name, file, line) ->
    let k = Printf.sprintf "%s::%s" kind name in
    Hashtbl.replace snap_map k (kind, name, file, line)
  ) snap_items;
  (* Current state *)
  let cur_decls = collect root in
  let cur_map : (string, Rocq_parse.declaration) Hashtbl.t =
    Hashtbl.create (List.length cur_decls) in
  List.iter (fun (d : Rocq_parse.declaration) ->
    Hashtbl.replace cur_map (decl_key d) d
  ) cur_decls;
  (* Compute added / removed *)
  let cur_keys  = Hashtbl.fold (fun k _ acc -> k :: acc) cur_map  [] in
  let snap_keys = Hashtbl.fold (fun k _ acc -> k :: acc) snap_map [] in
  let added   = List.sort String.compare
    (List.filter (fun k -> not (Hashtbl.mem snap_map k)) cur_keys) in
  let removed = List.sort String.compare
    (List.filter (fun k -> not (Hashtbl.mem cur_map k))  snap_keys) in
  Printf.printf "snapshot: %s, %d entries\n" snap_generated snap_total;
  Printf.printf "current : %d entries\n" (List.length cur_decls);
  Printf.printf "delta   : +%d / -%d\n" (List.length added) (List.length removed);
  if added <> [] then begin
    print_endline "\nADDED:";
    List.iter (fun k ->
      let d = Hashtbl.find cur_map k in
      let rel = rel_to root d.file in
      Printf.printf "  + [%s] %s  %s:%d\n"
        (Rocq_parse.string_of_kind d.kind) d.name rel d.line
    ) added
  end;
  if removed <> [] then begin
    print_endline "\nREMOVED:";
    List.iter (fun k ->
      let (kind, name, file, line) = Hashtbl.find snap_map k in
      Printf.printf "  - [%s] %s  %s:%d\n" kind name file line
    ) removed
  end;
  if added = [] && removed = [] then 0 else 1

(* ------------------------------------------------------------------ *)
(* Subcommand: suspect                                                 *)
(* ------------------------------------------------------------------ *)

let re_true_body     = Re.Perl.compile_pat {|:\s*True\s*\.|}
let re_vacuous_forall = Re.Perl.compile_pat {|forall\s+\w+\s*:\s*True\s*,|}

let cmd_suspect root =
  let decls = collect root in
  let flagged =
    List.filter_map (fun (d : Rocq_parse.declaration) ->
      let body = d.statement in
      if Re.execp re_true_body body then Some ("type-is-True", d)
      else if Re.execp re_vacuous_forall body then Some ("vacuous-forall", d)
      else None
    ) decls
  in
  if flagged = [] then begin
    print_endline "no suspect axioms found";
    0
  end else begin
    List.iter (fun (tag, (d : Rocq_parse.declaration)) ->
      let rel = rel_to root d.file in
      Printf.printf "[%s] [%s] %s  %s:%d\n"
        tag (Rocq_parse.string_of_kind d.kind) d.name rel d.line;
      let preview = trunc 100 (String.trim (first_line d.statement)) in
      Printf.printf "    %s\n" preview
    ) flagged;
    1
  end

(* ------------------------------------------------------------------ *)
(* Cmdliner wiring                                                     *)
(* ------------------------------------------------------------------ *)

let resolve_root = function
  | Some r -> r
  | None   -> detect_root (Sys.getcwd ())

(** Each subcommand gets its own copy of root_opt so cmdliner tracks it
    independently per sub-command term. *)
let mk_root_opt () =
  Arg.(value & opt (some string) None
       & info ["root"] ~docv:"PATH"
         ~doc:"Project root (default: walk up from CWD for _CoqProject)")

(* ---------- list ---------------------------------------------------- *)

let list_cmd =
  let root_opt   = mk_root_opt () in
  let kind_opt =
    Arg.(value & opt (some string) None
         & info ["kind"] ~docv:"KIND"
           ~doc:"Filter to Axiom or Parameter")
  in
  let file_opt =
    Arg.(value & opt (some string) None
         & info ["file"] ~docv:"SUBSTR"
           ~doc:"Filter by file-path substring")
  in
  let summary_flag =
    Arg.(value & flag & info ["summary"; "s"]
           ~doc:"Only print counts, not individual entries")
  in
  let run root kind file summary =
    let root = resolve_root root in
    exit (cmd_list root kind file summary)
  in
  let term = Term.(const run $ root_opt $ kind_opt $ file_opt $ summary_flag) in
  let info_ = Cmd.info "list"
    ~doc:"List all Axioms and Parameters in the project" in
  Cmd.v info_ term

(* ---------- snapshot ----------------------------------------------- *)

let snapshot_cmd =
  let root_opt = mk_root_opt () in
  let run root =
    let root = resolve_root root in
    exit (cmd_snapshot root)
  in
  let term = Term.(const run $ root_opt) in
  let info_ = Cmd.info "snapshot"
    ~doc:"Save current Axiom/Parameter state to .cag/audit-snapshot.json" in
  Cmd.v info_ term

(* ---------- diff ---------------------------------------------------- *)

let diff_cmd =
  let root_opt = mk_root_opt () in
  let run root =
    let root = resolve_root root in
    exit (cmd_diff root)
  in
  let term = Term.(const run $ root_opt) in
  let info_ = Cmd.info "diff"
    ~doc:"Compare current state vs last snapshot" in
  Cmd.v info_ term

(* ---------- suspect ------------------------------------------------ *)

let suspect_cmd =
  let root_opt = mk_root_opt () in
  let run root =
    let root = resolve_root root in
    exit (cmd_suspect root)
  in
  let term = Term.(const run $ root_opt) in
  let info_ = Cmd.info "suspect"
    ~doc:"Flag suspicious-shape axioms (True-typed, vacuous foralls)" in
  Cmd.v info_ term

(* ------------------------------------------------------------------ *)
(* Argv normalisation: move --root PATH before the subcommand to      *)
(* after it, so cmdliner sees it as a per-subcommand option.          *)
(*                                                                     *)
(* Python's argparse handles a "parent" --root naturally; cmdliner's  *)
(* Cmd.group does not forward group-level options to subcommands.      *)
(* We solve this by rewriting argv before handing off to Cmd.eval.    *)
(* ------------------------------------------------------------------ *)

let subcommands = ["list"; "snapshot"; "diff"; "suspect"]

(** Rewrite argv so that any --root PATH appearing *before* the
    subcommand name is moved to *after* it.
    e.g.  cag-audit --root /foo list --summary
    →     cag-audit list --root /foo --summary  *)
let normalise_argv () =
  let argv = Sys.argv in
  let n = Array.length argv in
  if n < 2 then ()
  else begin
    (* Walk argv[1..] to separate:
       - root_tokens : the --root ... token(s) seen before any subcommand
       - subcmd_and_rest : everything from the subcommand name onwards       *)
    let root_tokens     = ref [] in
    let subcmd_and_rest = ref [] in
    let found_subcmd    = ref false in
    let i = ref 1 in
    while !i < n do
      let a = argv.(!i) in
      if !found_subcmd then begin
        subcmd_and_rest := !subcmd_and_rest @ [a];
        incr i
      end else if List.mem a subcommands then begin
        found_subcmd := true;
        subcmd_and_rest := [a];
        incr i
      end else if a = "--root" && !i + 1 < n then begin
        root_tokens := ["--root"; argv.(!i + 1)];
        i := !i + 2
      end else if String.length a > 7 && String.sub a 0 7 = "--root=" then begin
        root_tokens := [a];
        incr i
      end else
        incr i  (* skip unknown pre-subcommand args *)
    done;
    (* Only rewrite if --root appeared before the subcommand *)
    if !root_tokens <> [] && !subcmd_and_rest <> [] then begin
      let new_args = !subcmd_and_rest @ !root_tokens in
      List.iteri (fun idx v -> argv.(1 + idx) <- v) new_args
    end
  end

(* ---------- top-level group --------------------------------------- *)

let () =
  normalise_argv ();
  let info_ = Cmd.info "cag-audit" ~version:"0.1"
    ~doc:"Axiom/Parameter monitoring for the CAG project" in
  let default_term =
    let run () =
      (* No subcommand: print help *)
      Printf.printf "Usage: cag-audit [--root PATH] {list|snapshot|diff|suspect}\n";
      Printf.printf "  list      List Axioms/Parameters (--kind, --file, --summary)\n";
      Printf.printf "  snapshot  Save current state to .cag/audit-snapshot.json\n";
      Printf.printf "  diff      Compare current state vs snapshot\n";
      Printf.printf "  suspect   Flag suspicious-shape axioms\n";
      exit 0
    in
    Term.(const run $ const ())
  in
  exit (Cmd.eval (Cmd.group ~default:default_term info_
    [ list_cmd; snapshot_cmd; diff_cmd; suspect_cmd ]))
