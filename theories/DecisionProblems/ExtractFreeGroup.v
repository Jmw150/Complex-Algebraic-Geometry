(** * DecisionProblems/ExtractFreeGroup.v

    Coq → OCaml extraction of free-group operations.

    Addresses [E1] from the McReynolds-roadmap todos.

    Produces lib/free_group_ml.ml with:
    - [reduce] : Word n → Word n  (free-reduction normal form)
    - [free_mul] : Word n → Word n → Word n
    - [free_inv] : Word n → Word n
    - [word_eq] : Word n → Word n → bool  (decidable equality)
    - [gamma_pow] : (Word n) → nat → (Word n)
    - [letter_inv]
    - constructors for Letter n, Fin.t

    Plus convenience F_2 specializations used by the OCaml driver. *)

From CAG Require Import FreeGroup.
From CAG Require Import DecisionProblems.HallTheorem.
From Stdlib Require Import List Vectors.Fin Bool Extraction ExtrOcamlBasic ExtrOcamlNatInt.
Import ListNotations.

(** Convenience: F_2 letter constructors using bool selector. *)

Definition fin2_of_bool (b : bool) : Fin.t 2 :=
  if b then Fin.F1 else Fin.FS Fin.F1.

(** F_2 generators as Letter 2: generator-a = (F1, false), inverse a^-1 =
    (F1, true), generator-b = (FS F1, false), b^-1 = (FS F1, true).

    Convention: snd = false denotes the positive generator. *)
Definition F2_a : Letter 2 := (Fin.F1, false).
Definition F2_b : Letter 2 := (Fin.FS Fin.F1, false).
Definition F2_A : Letter 2 := letter_inv F2_a.
Definition F2_B : Letter 2 := letter_inv F2_b.

(** F_2-specific specializations of the polymorphic operations. *)
Definition reduce_F2 : Word 2 -> Word 2 := @reduce 2.
Definition free_mul_F2 : Word 2 -> Word 2 -> Word 2 := @free_mul 2.
Definition free_inv_F2 : Word 2 -> Word 2 := @free_inv 2.
Definition word_eq_F2 : Word 2 -> Word 2 -> bool := @word_eq 2.

(** [Word 2] → reduced canonical form, then equality test. *)
Definition word_canonical_F2 (w : Word 2) : Word 2 := reduce_F2 w.

(** Conjugation in F_2: g·w·g^-1 (in reduced form). *)
Definition conjugate_F2 (g w : Word 2) : Word 2 :=
  free_mul_F2 (free_mul_F2 g w) (free_inv_F2 g).

(** Cyclic rotation: send (l :: rest) to (rest ++ [l]). *)
Fixpoint rotate_left {A : Type} (xs : list A) : list A :=
  match xs with
  | nil => nil
  | x :: rest => rest ++ (x :: nil)
  end.

(** All cyclic rotations of a word, as a list. *)
Fixpoint all_rotations_aux {A : Type} (k : nat) (w : list A) : list (list A) :=
  match k with
  | O => nil
  | S k' => w :: all_rotations_aux k' (rotate_left w)
  end.

Definition all_rotations {A : Type} (w : list A) : list (list A) :=
  all_rotations_aux (length w) w.

(** Cyclic reduction: repeatedly cancel (l :: ... :: letter_inv l) at
    the boundary. *)

Definition cyclic_reduce_step (w : Word 2) : option (Word 2) :=
  match w with
  | nil => None
  | l :: rest =>
      match List.rev rest with
      | nil => None
      | l' :: _ =>
          if (Nat.eqb (proj1_sig (Fin.to_nat (fst l))) (proj1_sig (Fin.to_nat (fst l'))))
             && (Bool.eqb (snd l) (negb (snd l')))
          then Some (List.removelast rest)
          else None
      end
  end.

Fixpoint cyclic_reduce_aux (fuel : nat) (w : Word 2) : Word 2 :=
  match fuel with
  | O => w
  | S fuel' =>
      match cyclic_reduce_step w with
      | None => w
      | Some w' => cyclic_reduce_aux fuel' w'
      end
  end.

Definition cyclic_reduce_F2 (w : Word 2) : Word 2 :=
  cyclic_reduce_aux (length w) (reduce_F2 w).

(** Conjugacy test in F_2: cyclically reduce both, then check whether
    one is a cyclic rotation of the other. *)
Definition word_eq_list_F2 (ws : list (Word 2)) (target : Word 2) : bool :=
  List.existsb (word_eq_F2 target) ws.

Definition are_conjugate_F2_dec (u v : Word 2) : bool :=
  let cu := cyclic_reduce_F2 u in
  let cv := cyclic_reduce_F2 v in
  word_eq_list_F2 (all_rotations cu) cv.

(** [gamma_pow] for F_2. *)
Definition gamma_pow_F2_word (gamma : Word 2) (i : nat) : Word 2 :=
  Nat.iter i (free_mul_F2 gamma) nil.

(** Polymorphic versions exposed too. *)
Definition reduce_poly := @reduce.
Definition free_mul_poly := @free_mul.
Definition free_inv_poly := @free_inv.
Definition word_eq_poly := @word_eq.

Set Extraction Output Directory "lib".

Extraction "free_group_ml.ml"
  reduce_F2 free_mul_F2 free_inv_F2 word_eq_F2
  conjugate_F2 cyclic_reduce_F2 are_conjugate_F2_dec
  gamma_pow_F2_word all_rotations rotate_left
  letter_inv
  fin2_of_bool F2_a F2_b F2_A F2_B
  reduce_poly free_mul_poly free_inv_poly word_eq_poly.
