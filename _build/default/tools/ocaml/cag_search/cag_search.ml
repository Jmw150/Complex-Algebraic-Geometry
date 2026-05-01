(** cag-search — SQLite FTS5 lemma index for the Complex-Algebraic-Geometry
    project. Mirrors the Python prototype 1:1 in user-visible behavior. *)

open Cag_lib
module S = Sqlite3
module Rc = S.Rc

(* ---------- schema --------------------------------------------------- *)

let schema = {|
CREATE TABLE IF NOT EXISTS decls (
    id        INTEGER PRIMARY KEY,
    name      TEXT NOT NULL,
    kind      TEXT NOT NULL,
    statement TEXT NOT NULL,
    file      TEXT NOT NULL,
    line      INTEGER NOT NULL
);
CREATE VIRTUAL TABLE IF NOT EXISTS decls_fts USING fts5(
    name, kind, statement,
    content='decls', content_rowid='id',
    tokenize='unicode61'
);
CREATE TRIGGER IF NOT EXISTS decls_ai AFTER INSERT ON decls BEGIN
    INSERT INTO decls_fts(rowid, name, kind, statement)
    VALUES (new.id, new.name, new.kind, new.statement);
END;
CREATE TRIGGER IF NOT EXISTS decls_ad AFTER DELETE ON decls BEGIN
    INSERT INTO decls_fts(decls_fts, rowid, name, kind, statement)
    VALUES ('delete', old.id, old.name, old.kind, old.statement);
END;
CREATE INDEX IF NOT EXISTS decls_kind ON decls(kind);
CREATE INDEX IF NOT EXISTS decls_file ON decls(file);
|}

let must_ok rc = if rc <> Rc.OK then failwith (Rc.to_string rc)

let check db rc =
  if rc <> Rc.OK && rc <> Rc.DONE then begin
    failwith (Printf.sprintf "sqlite: %s" (S.errmsg db))
  end

let exec_sql db sql =
  S.exec db sql |> check db

(* ---------- DB ops --------------------------------------------------- *)

let open_db path =
  let dir = Filename.dirname path in
  if not (Sys.file_exists dir) then Unix.mkdir dir 0o755;
  let db = S.db_open path in
  exec_sql db schema;
  db

let truncate_decls db =
  exec_sql db "DELETE FROM decls";
  exec_sql db "INSERT INTO decls_fts(decls_fts) VALUES('rebuild')"

let insert db (d : Rocq_parse.declaration) =
  let stmt =
    S.prepare db
      "INSERT INTO decls(name, kind, statement, file, line) VALUES (?,?,?,?,?)"
  in
  S.bind_text stmt 1 d.name |> check db;
  S.bind_text stmt 2 (Rocq_parse.string_of_kind d.kind) |> check db;
  S.bind_text stmt 3 d.statement |> check db;
  S.bind_text stmt 4 d.file |> check db;
  S.bind_int stmt 5 d.line |> check db;
  let rc = S.step stmt in
  if rc <> Rc.DONE then check db rc;
  must_ok (S.finalize stmt)

let rebuild db root =
  let t0 = Unix.gettimeofday () in
  exec_sql db "BEGIN";
  truncate_decls db;
  let count = ref 0 in
  Rocq_parse.walk_theories (Filename.concat root "theories")
  |> Seq.iter (fun d -> insert db d; incr count);
  exec_sql db "COMMIT";
  let dt = Unix.gettimeofday () -. t0 in
  (!count, dt)

(* ---------- search --------------------------------------------------- *)

type hit = {
  score : float;
  name : string;
  kind : string;
  file : string;
  line : int;
  first_line : string;
}

let first_line s =
  match String.index_opt s '\n' with
  | None -> s
  | Some k -> String.sub s 0 k

let search db ?(kind=None) ?(file_substr=None) ?(limit=20) query =
  let has_query = String.trim query <> "" in
  let buf = Buffer.create 256 in
  let args = ref [] in
  if has_query then begin
    Buffer.add_string buf
      "SELECT d.id, d.name, d.kind, d.file, d.line, d.statement, \
       bm25(decls_fts) AS score \
       FROM decls d JOIN decls_fts f ON d.id = f.rowid \
       WHERE decls_fts MATCH ?";
    args := `T query :: !args
  end else
    Buffer.add_string buf
      "SELECT d.id, d.name, d.kind, d.file, d.line, d.statement, \
       0.0 AS score FROM decls d WHERE 1=1";
  (match kind with
   | None -> ()
   | Some k ->
       Buffer.add_string buf " AND d.kind = ?";
       args := `T k :: !args);
  (match file_substr with
   | None -> ()
   | Some f ->
       Buffer.add_string buf " AND d.file LIKE ?";
       args := `T (Printf.sprintf "%%%s%%" f) :: !args);
  if has_query then
    Buffer.add_string buf " ORDER BY score LIMIT ?"
  else
    Buffer.add_string buf " ORDER BY d.file, d.line LIMIT ?";
  args := `I limit :: !args;
  let stmt = S.prepare db (Buffer.contents buf) in
  List.rev !args
  |> List.iteri (fun i a ->
       let pos = i + 1 in
       (match a with
        | `T s -> S.bind_text stmt pos s |> check db
        | `I i -> S.bind_int stmt pos i |> check db));
  let acc = ref [] in
  let rec loop () =
    match S.step stmt with
    | Rc.ROW ->
        let col_text k =
          match S.column stmt k with
          | S.Data.TEXT s -> s
          | _ -> ""
        in
        let col_int k =
          match S.column stmt k with
          | S.Data.INT i -> Int64.to_int i
          | _ -> 0
        in
        let col_float k =
          match S.column stmt k with
          | S.Data.FLOAT f -> f
          | S.Data.INT i -> Int64.to_float i
          | _ -> 0.0
        in
        let stmt_text = col_text 5 in
        acc := { score = col_float 6;
                 name = col_text 1;
                 kind = col_text 2;
                 file = col_text 3;
                 line = col_int 4;
                 first_line = first_line stmt_text } :: !acc;
        loop ()
    | Rc.DONE -> ()
    | rc -> check db rc
  in
  loop ();
  must_ok (S.finalize stmt);
  List.rev !acc

let stats db =
  let stmt =
    S.prepare db "SELECT kind, COUNT(*) FROM decls GROUP BY kind ORDER BY 2 DESC"
  in
  let acc = ref [] in
  let rec loop () =
    match S.step stmt with
    | Rc.ROW ->
        let k = match S.column stmt 0 with S.Data.TEXT s -> s | _ -> "" in
        let c = match S.column stmt 1 with
          | S.Data.INT i -> Int64.to_int i
          | _ -> 0
        in
        acc := (k, c) :: !acc;
        loop ()
    | Rc.DONE -> ()
    | rc -> check db rc
  in
  loop ();
  must_ok (S.finalize stmt);
  List.rev !acc

let row_count db =
  let stmt = S.prepare db "SELECT COUNT(*) FROM decls" in
  let n = match S.step stmt with
    | Rc.ROW ->
        (match S.column stmt 0 with
         | S.Data.INT i -> Int64.to_int i
         | _ -> 0)
    | _ -> 0
  in
  must_ok (S.finalize stmt);
  n

(* ---------- project root detection ---------------------------------- *)

let detect_root start =
  let rec walk p =
    if Sys.file_exists (Filename.concat p "_CoqProject") then Some p
    else
      let parent = Filename.dirname p in
      if parent = p then None else walk parent
  in
  match walk start with
  | Some r -> r
  | None -> failwith ("no _CoqProject found above " ^ start)

(* ---------- output formatting --------------------------------------- *)

let isatty = Unix.isatty Unix.stdout
let no_color = (try Sys.getenv "NO_COLOR" <> "" with Not_found -> false)

let color code text =
  if isatty && not no_color
  then Printf.sprintf "\027[%sm%s\027[0m" code text
  else text

let print_hit root h =
  let rel =
    let abs_root = root |> Filename.concat in
    let _ = abs_root in
    if Filename.is_relative h.file then h.file
    else
      let plen = String.length root in
      let flen = String.length h.file in
      if flen > plen && String.sub h.file 0 plen = root
      then String.sub h.file (plen + 1) (flen - plen - 1)
      else h.file
  in
  let kind_str = color "33" (Printf.sprintf "[%s]" h.kind) in
  let name_str = color "1;36" h.name in
  let loc_str = color "2" (Printf.sprintf "%s:%d" rel h.line) in
  Printf.printf "%s %s  %s\n" kind_str name_str loc_str;
  let preview =
    if String.length h.first_line > 100
    then String.sub h.first_line 0 97 ^ "..."
    else h.first_line
  in
  if String.trim preview <> "" then Printf.printf "    %s\n" preview

(* ---------- CLI ----------------------------------------------------- *)

open Cmdliner

let default_db_path root =
  Filename.concat (Filename.concat root ".cag") "cag-index.db"

let auto_build conn root =
  if row_count conn = 0 then begin
    Printf.printf "index empty, building from %s/theories ...\n%!" root;
    let n, dt = rebuild conn root in
    Printf.printf "  -> %d decls in %.2fs\n" n dt
  end

let run query kind file_substr limit rebuild_flag stats_flag db_path_opt root_opt =
  let root = match root_opt with
    | Some r -> r
    | None -> detect_root (Sys.getcwd ())
  in
  let db_path = match db_path_opt with
    | Some d -> d
    | None -> default_db_path root
  in
  let conn = open_db db_path in
  if rebuild_flag then begin
    let n, dt = rebuild conn root in
    Printf.printf "indexed %d declarations in %.2fs -> %s\n" n dt db_path;
    0
  end
  else if stats_flag then begin
    let s = stats conn in
    let total = List.fold_left (fun a (_, n) -> a + n) 0 s in
    Printf.printf "total: %d\n" total;
    List.iter (fun (k, n) -> Printf.printf "  %-14s %d\n" k n) s;
    Printf.printf "db: %s\n" db_path;
    0
  end
  else begin
    auto_build conn root;
    let q = String.concat " " query in
    let kind_norm = match kind with
      | None -> None
      | Some s ->
          let n = String.length s in
          if n = 0 then None
          else Some (String.uppercase_ascii (String.sub s 0 1) ^
                     String.lowercase_ascii (String.sub s 1 (n - 1)))
    in
    let hits = search conn ~kind:kind_norm ~file_substr ~limit q in
    if hits = [] then begin print_endline "(no results)"; 1 end
    else begin
      List.iter (print_hit root) hits;
      0
    end
  end

let () =
  let query = Arg.(value & pos_all string [] & info [] ~docv:"QUERY"
    ~doc:"FTS5 query (e.g. \"core free\" or \"CReal arith\")") in
  let kind = Arg.(value & opt (some string) None & info ["k"; "kind"]
    ~docv:"KIND" ~doc:"Filter by declaration kind (Lemma, Axiom, ...)") in
  let file = Arg.(value & opt (some string) None & info ["f"; "file"]
    ~docv:"PAT" ~doc:"Filter by file-path substring") in
  let limit = Arg.(value & opt int 20 & info ["n"; "limit"]
    ~docv:"N" ~doc:"Max results") in
  let rebuild_flag = Arg.(value & flag & info ["rebuild"]
    ~doc:"Drop and rebuild the index") in
  let stats_flag = Arg.(value & flag & info ["stats"]
    ~doc:"Print index statistics") in
  let db = Arg.(value & opt (some string) None & info ["db"]
    ~docv:"PATH" ~doc:"Path to index DB") in
  let root = Arg.(value & opt (some string) None & info ["root"]
    ~docv:"PATH" ~doc:"Project root") in
  let info_ = Cmd.info "cag-search" ~version:"0.1" ~doc:"Search CAG declarations" in
  let term = Term.(const run $ query $ kind $ file $ limit
                   $ rebuild_flag $ stats_flag $ db $ root) in
  exit (Cmd.eval' (Cmd.v info_ term))
