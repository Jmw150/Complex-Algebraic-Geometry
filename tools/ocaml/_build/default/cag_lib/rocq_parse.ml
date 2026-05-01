type kind =
  | Theorem
  | Lemma
  | Corollary
  | Proposition
  | Fact
  | Remark
  | Definition
  | Fixpoint
  | CoFixpoint
  | Axiom
  | Parameter
  | Hypothesis
  | Conjecture
  | Example
  | Inductive
  | CoInductive
  | Class
  | Instance
  | Record
  | Structure
  | Variant

let all_kinds =
  [ Theorem; Lemma; Corollary; Proposition; Fact; Remark;
    Definition; Fixpoint; CoFixpoint;
    Axiom; Parameter; Hypothesis; Conjecture; Example;
    Inductive; CoInductive; Class; Instance;
    Record; Structure; Variant ]

let string_of_kind = function
  | Theorem -> "Theorem"
  | Lemma -> "Lemma"
  | Corollary -> "Corollary"
  | Proposition -> "Proposition"
  | Fact -> "Fact"
  | Remark -> "Remark"
  | Definition -> "Definition"
  | Fixpoint -> "Fixpoint"
  | CoFixpoint -> "CoFixpoint"
  | Axiom -> "Axiom"
  | Parameter -> "Parameter"
  | Hypothesis -> "Hypothesis"
  | Conjecture -> "Conjecture"
  | Example -> "Example"
  | Inductive -> "Inductive"
  | CoInductive -> "CoInductive"
  | Class -> "Class"
  | Instance -> "Instance"
  | Record -> "Record"
  | Structure -> "Structure"
  | Variant -> "Variant"

let kind_of_string s =
  List.find_opt (fun k -> string_of_kind k = s) all_kinds

type declaration = {
  name : string;
  kind : kind;
  statement : string;
  file : string;
  line : int;
}

(* ---------- comment stripping --------------------------------------- *)

(* Strip Rocq comments (* ... *), nested. Replace each comment with
   whitespace of the same length so byte-offsets and line numbers match
   the original source. *)
let strip_comments src =
  let n = String.length src in
  let buf = Bytes.of_string src in
  let i = ref 0 in
  while !i < n - 1 do
    if Bytes.get buf !i = '(' && Bytes.get buf (!i + 1) = '*' then begin
      let depth = ref 1 in
      let start = !i in
      Bytes.set buf !i ' ';
      Bytes.set buf (!i + 1) ' ';
      i := !i + 2;
      while !depth > 0 && !i < n - 1 do
        let c = Bytes.get buf !i in
        let d = Bytes.get buf (!i + 1) in
        if c = '(' && d = '*' then begin
          incr depth;
          Bytes.set buf !i ' ';
          Bytes.set buf (!i + 1) ' ';
          i := !i + 2
        end
        else if c = '*' && d = ')' then begin
          decr depth;
          Bytes.set buf !i ' ';
          Bytes.set buf (!i + 1) ' ';
          i := !i + 2
        end
        else begin
          if Bytes.get buf !i <> '\n' then Bytes.set buf !i ' ';
          incr i
        end
      done;
      ignore start
    end
    else
      incr i
  done;
  Bytes.unsafe_to_string buf

(* ---------- declaration matcher ------------------------------------- *)

(* Match prefix modifiers that can precede a declaration *)
let prefix_re = Re.Perl.compile_pat
  {|(?:(?:Local|Global|Polymorphic|Monomorphic|Program|#\[[^\]]*\])\s+)*|}

let kind_alts =
  String.concat "|" (List.map string_of_kind all_kinds)

let decl_re =
  let pat = Printf.sprintf
    {|^[ \t]*%s(?P<kind>%s)[ \t\n]+(?P<name>[A-Za-z_][A-Za-z0-9_']*)\b|}
    {|(?:(?:Local|Global|Polymorphic|Monomorphic|Program|#\[[^\]]*\])\s+)*|}
    kind_alts
  in
  Re.Perl.compile_pat ~opts:[`Multiline] pat
[@@warning "-26-27"]

let _ = prefix_re  (* silence warning *)

(* Find offset of statement-terminating `.` (skips parens/strings). *)
let find_stmt_end src start =
  let n = String.length src in
  let depth = ref 0 in
  let in_string = ref false in
  let i = ref start in
  let result = ref n in
  let stop = ref false in
  while not !stop && !i < n do
    let c = String.unsafe_get src !i in
    if !in_string then begin
      if c = '"' then begin
        if !i + 1 < n && String.unsafe_get src (!i + 1) = '"' then
          i := !i + 2
        else begin
          in_string := false;
          incr i
        end
      end else
        incr i
    end
    else if c = '"' then begin
      in_string := true;
      incr i
    end
    else begin
      (match c with
       | '(' | '[' | '{' -> incr depth
       | ')' | ']' | '}' -> decr depth
       | '.' when !depth = 0 ->
           if !i + 1 = n
              || (let d = String.unsafe_get src (!i + 1) in
                  d = ' ' || d = '\t' || d = '\n' || d = '\r') then begin
             result := !i;
             stop := true
           end
       | _ -> ());
      if not !stop then incr i
    end
  done;
  !result

let line_of src offset =
  let n = String.length src in
  let count = ref 0 in
  let lim = min offset n in
  for k = 0 to lim - 1 do
    if String.unsafe_get src k = '\n' then incr count
  done;
  !count + 1

let read_file path =
  let ic = open_in_bin path in
  let len = in_channel_length ic in
  let s = really_input_string ic len in
  close_in ic;
  s

let iter_declarations path =
  let src = read_file path in
  let clean = strip_comments src in
  let max_stmt = 4000 in
  let groups = Re.all decl_re clean in
  List.filter_map
    (fun g ->
      let kind_str = Re.Group.get g 1 in
      let name = Re.Group.get g 2 in
      match kind_of_string kind_str with
      | None -> None
      | Some kind ->
          let start = Re.Group.start g 0 in
          let after_match = Re.Group.stop g 0 in
          let stmt_end = find_stmt_end clean after_match in
          let snippet_end = min (stmt_end + 1) (String.length clean) in
          let raw = String.sub clean start (snippet_end - start) in
          let statement =
            if String.length raw > max_stmt
            then String.sub raw 0 max_stmt ^ " (...truncated...)"
            else raw
          in
          let line = line_of clean start in
          Some { name; kind; statement; file = path; line })
    groups

(* ---------- recursive walker ---------------------------------------- *)

let skip_dirs = ["_build"; "lib"; ".git"; ".cag"]

let rec walk_dir dir : string Seq.t =
  fun () ->
    if not (Sys.file_exists dir && Sys.is_directory dir) then Seq.Nil
    else
      let entries = Sys.readdir dir in
      Array.sort String.compare entries;
      let rec loop i () =
        if i >= Array.length entries then Seq.Nil
        else
          let name = entries.(i) in
          let full = Filename.concat dir name in
          if List.mem name skip_dirs then loop (i + 1) ()
          else if Sys.is_directory full then
            Seq.append (walk_dir full) (loop (i + 1)) ()
          else if Filename.check_suffix name ".v" then
            Seq.Cons (full, loop (i + 1))
          else loop (i + 1) ()
      in
      loop 0 ()

let walk_theories root =
  let files = walk_dir root in
  Seq.flat_map (fun path ->
    try List.to_seq (iter_declarations path)
    with exn ->
      Printf.eprintf "WARN: failed %s: %s\n" path (Printexc.to_string exn);
      Seq.empty
  ) files
