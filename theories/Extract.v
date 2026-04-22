From Stdlib Require Import Extraction.
From Stdlib Require Import ExtrOcamlBasic.

From Stdlib Require Import ZArith.
From Stdlib Require Import QArith.

From CAG Require Import AG.

Extraction Language OCaml.

(*
(* Extract Coq nat as Zarith.Z.t *)
Extract Inductive nat => "Z.t"
  ["Z.zero" "Z.succ"]
  "(fun fO fS n ->
      if Z.equal n Z.zero then 
         fO () 
      else fS (Z.pred n))".

(* Map nat operations to Zarith operations *)
Extract Constant Nat.add => "Z.add".
Extract Constant Nat.mul => "Z.mul".
Extract Constant Nat.sub => "Z.sub".
Extract Constant Nat.eqb => "Z.equal".
Extract Constant Nat.ltb => "Z.lt".
Extract Constant Nat.leb => "Z.leq".
*)
(* positive is part of Q definition Z/positive 

Like Nat, but encoded as bits
*)
(*
Extract Inductive positive => "Z.t"
[
  "Z.one"
  "(fun p -> Z.shift_left p 1)"
  "(fun p -> Z.succ (Z.shift_left p 1))"
]
"(fun fH fO fI p ->
      if (Z.equal p Z.one) then 
         fH()
      else
        let half = Z.shift_right p 1 in
        if Z.equal (Z.logand p Z.one) Z.zero
        then fO half 
        else fI half)".
*)
(* First, ensure Z extracts to Zarith.Z.t (same idea as above, but keep it simple) *)
(*
Extract Inductive Z => "ZZ.t"
  [ "Z.zero" "(fun p -> p)" "(fun p -> Z.neg p)" ]
  "(fun fZ0 fZpos fZneg z ->
      if Z.equal z Z.zero then fZ0 ()
      else if Z.sign z > 0 then fZpos z
      else fZneg (Z.neg z))".

Extract Inductive Q => "Q.t"
[ "(fun n d -> Q.make n d)" ]
"(fun f q -> f (Q.num q) (Q.den q))".


(* Map Q operations to Zarith *)
Extract Constant Qplus => "Q.add".
Extract Constant Qmult => "Q.mul".
Extract Constant Qminus => "Q.sub".
Extract Constant Qopp => "Q.neg".
Extract Constant Qinv => "Q.inv".
Extract Constant Qcompare => "Q.compare".
Extract Constant Qeq_bool => "Q.equal".
*)

Set Extraction Output Directory "lib".
Extraction "complexrocq.ml"
  AG.run_f
  AG.run_g
  AG.run_p
  AG.rev
  AG.app
  AG.filter
  AG.counter
  AG.add
  AG.repeat
  AG.length
  AG.vadd
  AG.vscale
  AG.vzero
  AG.madd
  AG.mmul
  AG.trace
.

(*Extraction "lib/group.ml" Group.*)
