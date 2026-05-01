(* Smoke test for the OCaml parser. *)
let () =
  let counts = Hashtbl.create 32 in
  let total = ref 0 in
  Cag_lib.Rocq_parse.walk_theories "theories"
  |> Seq.iter (fun (d : Cag_lib.Rocq_parse.declaration) ->
       incr total;
       let k = Cag_lib.Rocq_parse.string_of_kind d.kind in
       Hashtbl.replace counts k
         (1 + (try Hashtbl.find counts k with Not_found -> 0)));
  let pairs =
    Hashtbl.fold (fun k v acc -> (k, v) :: acc) counts []
    |> List.sort (fun (_, a) (_, b) -> compare b a)
  in
  List.iter (fun (k, v) -> Printf.printf "%-14s %d\n" k v) pairs;
  Printf.printf "total: %d\n" !total
