
From Stdlib Require Import QArith ZArith.
From Stdlib Require Import Reals.Cauchy.ConstructiveCauchyReals.
From Stdlib Require Import Reals.Cauchy.ConstructiveCauchyRealsMult.
From Stdlib Require Import Reals.Cauchy.ConstructiveCauchyAbs.

Local Open Scope CReal_scope.
(** Extra functions for Constructive Reals *)

Definition CRpositive (x : CReal) : Prop :=
  CRealLtProp (inject_Q 0) x.

(* Meaning: is R positive? *)
(*Definition CRpositive (x : CReal) : Prop := CRealLtProp (inject_Q 0) x.*)

(* 
   Rlimit_at f x0 L means:

       ∀ ε > 0, ∃ δ > 0, ∀ x,
           |x − x0| < δ  ⇒  |f(x) − L| < ε.

   That is, lim_{x → x0} f(x) = L.
*)
Definition Rlimit_at (f : CReal -> CReal) (x0 L : CReal) : Prop :=
  forall eps : CReal,
    CRpositive eps ->
    exists delta : CReal,
      CRpositive delta /\
      forall x : CReal,
        CRealLtProp (CReal_abs (x - x0)) delta ->
        CRealLtProp (CReal_abs (f x - L)) eps.



Definition Rlimit_at_punctured (f : CReal -> CReal) (x0 L : CReal) : Prop :=
  forall eps : CReal,
    CRpositive eps ->
    exists delta : CReal,
      CRpositive delta /\
      forall x : CReal,
        (CReal_abs (x - x0) # 0) -> (* Implying ~ lim x = x0 *)
        CRealLtProp (CReal_abs (x - x0)) delta ->
        CRealLtProp (CReal_abs (f x - L)) eps.


(*  To avoid division:
 ∣f(x)−f(x0​)−L(x−x0​)∣<ε∣x−x0​∣for 0<∣x−x0​∣< delta *)
Definition Rderiv_at (f : CReal -> CReal) (x0 L : CReal) : Prop :=
  forall eps : CReal,
    CRpositive eps ->
    exists delta : CReal,
      CRpositive delta /\
      forall x : CReal,
        (CReal_abs (x - x0) # 0) ->
        CRealLtProp (CReal_abs (x - x0)) delta ->
        CRealLtProp
          (CReal_abs ((f x - f x0) - (L * (x - x0))))
          (eps * CReal_abs (x - x0)).

(* “Compute an approximation” by reading off the underlying 
   Cauchy sequence *)
Definition approx (x : CReal) (k : Z) : Q := seq x k.
