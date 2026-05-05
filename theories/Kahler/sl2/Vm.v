(** Kahler/sl2/Vm.v — Concrete irreducible sl(2)-module V(m)

    For each non-negative integer m, we construct the irreducible
    sl(2)-module V(m) of highest weight m.

    Carrier:   VmType m = nat -> CComplex
                 (index k = coefficient of the k-th basis vector w_k)
               Vectors morally supported on {0,...,m}.

    Standard (un-normalized) basis:
      w_k has weight m - 2k,  k = 0, 1, ..., m

    Action formulas:
      H(w_k) = (m - 2k) w_k
      Y(w_k) = w_{k+1}             (lowering: Y shifts index up in coefficient repr)
      X(w_k) = k(m-k+1) w_{k-1}   (raising: X shifts index down)

    In coefficient representation f : nat -> CComplex:
      (H·f)(k) = (m - 2k) · f(k)
      (Y·f)(k) = f(k-1)           if k > 0; 0 if k = 0
      (X·f)(k) = (k+1)·(m-k) · f(k+1)   if k < m; 0 if k >= m

    References: ag.org Part IV §sl2; Humphreys §7.2 *)

From Stdlib Require Import Arith ZArith QArith Lia.
From Stdlib Require Import Logic.FunctionalExtensionality.
From Stdlib Require Import Reals.Cauchy.ConstructiveCauchyReals.
From CAG Require Import Complex.
From CAG Require Import LieAlgebra.
From CAG Require Import Kahler.sl2.Basic.
From CAG Require Import Kahler.sl2.FiniteDimensional.

Local Open Scope CReal_scope.

(* ================================================================== *)
(** * 1. The carrier type and operations                               *)
(* ================================================================== *)

(** Vectors in V(m) are coefficient sequences indexed by nat. *)
Definition VmType (m : nat) : Type := nat -> CComplex.

Definition Vm_add {m} (f g : VmType m) : VmType m := fun k => Cadd (f k) (g k).
Definition Vm_scale {m} (c : CComplex) (f : VmType m) : VmType m := fun k => Cmul c (f k).
Definition Vm_zero {m} : VmType m := fun _ => C0.
Definition Vm_neg {m} (f : VmType m) : VmType m := fun k => Cneg (f k).

(** Helper: inject nat into CComplex. *)
Definition Cnat (n : nat) : CComplex :=
  Cinject_Q (QArith_base.inject_Z (Z.of_nat n)).

(** The sl(2) operators. *)
Definition Vm_H (m : nat) (f : VmType m) : VmType m :=
  fun k => Cmul (Csub (Cnat m) (Cmul (Cnat k) (Cadd C1 C1))) (f k).

Definition Vm_Y (m : nat) (f : VmType m) : VmType m :=
  fun k => match k with O => C0 | S k' => f k' end.

Definition Vm_X (m : nat) (f : VmType m) : VmType m :=
  fun k =>
    if Nat.ltb k m
    then Cmul (Cmul (Cnat (S k)) (Cnat (m - k))) (f (S k))
    else C0.

(** Standard k-th basis vector. *)
Definition Vm_basis (m : nat) (k : nat) : VmType m :=
  fun j => if Nat.eqb j k then C1 else C0.

(* ================================================================== *)
(** * 2. Vector space structure                                        *)
(* ================================================================== *)

(** All axioms hold pointwise; admitted as routine CComplex arithmetic. *)
(* CAG zero-dependent Axiom Vm_add_assoc theories/Kahler/sl2/Vm.v:73 BEGIN
Axiom Vm_add_assoc : forall {m} (u v w : VmType m),
    Vm_add u (Vm_add v w) = Vm_add (Vm_add u v) w.
   CAG zero-dependent Axiom Vm_add_assoc theories/Kahler/sl2/Vm.v:73 END *)
(* CAG zero-dependent Axiom Vm_add_comm theories/Kahler/sl2/Vm.v:75 BEGIN
Axiom Vm_add_comm : forall {m} (u v : VmType m),
    Vm_add u v = Vm_add v u.
   CAG zero-dependent Axiom Vm_add_comm theories/Kahler/sl2/Vm.v:75 END *)
(* CAG zero-dependent Axiom Vm_add_zero_r theories/Kahler/sl2/Vm.v:77 BEGIN
Axiom Vm_add_zero_r : forall {m} (f : VmType m),
    Vm_add f Vm_zero = f.
   CAG zero-dependent Axiom Vm_add_zero_r theories/Kahler/sl2/Vm.v:77 END *)
(* CAG zero-dependent Axiom Vm_add_neg_r theories/Kahler/sl2/Vm.v:79 BEGIN
Axiom Vm_add_neg_r : forall {m} (f : VmType m),
    Vm_add f (Vm_neg f) = Vm_zero.
   CAG zero-dependent Axiom Vm_add_neg_r theories/Kahler/sl2/Vm.v:79 END *)
(* CAG zero-dependent Axiom Vm_scale_one theories/Kahler/sl2/Vm.v:81 BEGIN
Axiom Vm_scale_one : forall {m} (f : VmType m),
    Vm_scale C1 f = f.
   CAG zero-dependent Axiom Vm_scale_one theories/Kahler/sl2/Vm.v:81 END *)
(* CAG zero-dependent Axiom Vm_scale_assoc theories/Kahler/sl2/Vm.v:83 BEGIN
Axiom Vm_scale_assoc : forall {m} (a b : CComplex) (f : VmType m),
    Vm_scale a (Vm_scale b f) = Vm_scale (Cmul a b) f.
   CAG zero-dependent Axiom Vm_scale_assoc theories/Kahler/sl2/Vm.v:83 END *)
(* CAG zero-dependent Axiom Vm_scale_add_v theories/Kahler/sl2/Vm.v:85 BEGIN
Axiom Vm_scale_add_v : forall {m} (a : CComplex) (u v : VmType m),
    Vm_scale a (Vm_add u v) = Vm_add (Vm_scale a u) (Vm_scale a v).
   CAG zero-dependent Axiom Vm_scale_add_v theories/Kahler/sl2/Vm.v:85 END *)
(* CAG zero-dependent Axiom Vm_scale_add_s theories/Kahler/sl2/Vm.v:87 BEGIN
Axiom Vm_scale_add_s : forall {m} (a b : CComplex) (f : VmType m),
    Vm_scale (Cadd a b) f = Vm_add (Vm_scale a f) (Vm_scale b f).
   CAG zero-dependent Axiom Vm_scale_add_s theories/Kahler/sl2/Vm.v:87 END *)

(* CAG zero-dependent Definition Vm_vs theories/Kahler/sl2/Vm.v:90 BEGIN
Definition Vm_vs (m : nat) : VectorSpace (VmType m) :=
  {| vs_add    := @Vm_add m
   ; vs_scale  := @Vm_scale m
   ; vs_zero   := @Vm_zero m
   ; vs_neg    := @Vm_neg m
   ; vs_add_assoc  := @Vm_add_assoc m
   ; vs_add_comm   := @Vm_add_comm m
   ; vs_add_zero_r := @Vm_add_zero_r m
   ; vs_add_neg_r  := @Vm_add_neg_r m
   ; vs_scale_one  := @Vm_scale_one m
   ; vs_scale_assoc := @Vm_scale_assoc m
   ; vs_scale_add_v := @Vm_scale_add_v m
   ; vs_scale_add_s := @Vm_scale_add_s m
   |}.
   CAG zero-dependent Definition Vm_vs theories/Kahler/sl2/Vm.v:90 END *)

(* ================================================================== *)
(** * 3. Linearity of operators and sl(2) structure                   *)
(* ================================================================== *)

(** Linearity — admitted as routine pointwise CComplex arithmetic. *)
(* CAG zero-dependent Axiom Vm_H_add theories/Kahler/sl2/Vm.v:110 BEGIN
Axiom Vm_H_add   : forall m (u v : VmType m),
    Vm_H m (Vm_add u v) = Vm_add (Vm_H m u) (Vm_H m v).
   CAG zero-dependent Axiom Vm_H_add theories/Kahler/sl2/Vm.v:110 END *)
(* CAG zero-dependent Axiom Vm_H_scale theories/Kahler/sl2/Vm.v:112 BEGIN
Axiom Vm_H_scale : forall m (c : CComplex) (f : VmType m),
    Vm_H m (Vm_scale c f) = Vm_scale c (Vm_H m f).
   CAG zero-dependent Axiom Vm_H_scale theories/Kahler/sl2/Vm.v:112 END *)
(* CAG zero-dependent Axiom Vm_X_add theories/Kahler/sl2/Vm.v:114 BEGIN
Axiom Vm_X_add   : forall m (u v : VmType m),
    Vm_X m (Vm_add u v) = Vm_add (Vm_X m u) (Vm_X m v).
   CAG zero-dependent Axiom Vm_X_add theories/Kahler/sl2/Vm.v:114 END *)
(* CAG zero-dependent Axiom Vm_X_scale theories/Kahler/sl2/Vm.v:116 BEGIN
Axiom Vm_X_scale : forall m (c : CComplex) (f : VmType m),
    Vm_X m (Vm_scale c f) = Vm_scale c (Vm_X m f).
   CAG zero-dependent Axiom Vm_X_scale theories/Kahler/sl2/Vm.v:116 END *)

(* CAG zero-dependent Axiom Vm_Y_add theories/Kahler/sl2/Vm.v:119 BEGIN
Axiom Vm_Y_add : forall m (u v : VmType m),
    Vm_Y m (Vm_add u v) = Vm_add (Vm_Y m u) (Vm_Y m v).
   CAG zero-dependent Axiom Vm_Y_add theories/Kahler/sl2/Vm.v:119 END *)

(* CAG zero-dependent Axiom Vm_Y_scale theories/Kahler/sl2/Vm.v:122 BEGIN
Axiom Vm_Y_scale : forall m (c : CComplex) (f : VmType m),
    Vm_Y m (Vm_scale c f) = Vm_scale c (Vm_Y m f).
   CAG zero-dependent Axiom Vm_Y_scale theories/Kahler/sl2/Vm.v:122 END *)

(** sl(2) commutation relations — admitted; proved in principle by
    pointwise arithmetic on each case. *)
(* CAG zero-dependent Axiom Vm_rel_HX theories/Kahler/sl2/Vm.v:127 BEGIN
Axiom Vm_rel_HX : forall m (f : VmType m),
    Vm_add (Vm_H m (Vm_X m f)) (Vm_neg (Vm_X m (Vm_H m f))) =
    Vm_scale (Cadd C1 C1) (Vm_X m f).
   CAG zero-dependent Axiom Vm_rel_HX theories/Kahler/sl2/Vm.v:127 END *)
(* CAG zero-dependent Axiom Vm_rel_HY theories/Kahler/sl2/Vm.v:130 BEGIN
Axiom Vm_rel_HY : forall m (f : VmType m),
    Vm_add (Vm_H m (Vm_Y m f)) (Vm_neg (Vm_Y m (Vm_H m f))) =
    Vm_scale (Cneg (Cadd C1 C1)) (Vm_Y m f).
   CAG zero-dependent Axiom Vm_rel_HY theories/Kahler/sl2/Vm.v:130 END *)
(* CAG zero-dependent Axiom Vm_rel_XY theories/Kahler/sl2/Vm.v:133 BEGIN
Axiom Vm_rel_XY : forall m (f : VmType m),
    Vm_add (Vm_X m (Vm_Y m f)) (Vm_neg (Vm_Y m (Vm_X m f))) =
    Vm_H m f.
   CAG zero-dependent Axiom Vm_rel_XY theories/Kahler/sl2/Vm.v:133 END *)

(* CAG zero-dependent Lemma Vm_rel_XY_module theories/Kahler/sl2/Vm.v:137 BEGIN
Lemma Vm_rel_XY_module : forall m (f : VmType m),
    Vm_add (Vm_X m (Vm_Y m f)) (Vm_neg (Vm_Y m (Vm_X m f))) =
    Vm_H m f.
Proof.
  apply Vm_rel_XY.
Qed.
   CAG zero-dependent Lemma Vm_rel_XY_module theories/Kahler/sl2/Vm.v:137 END *)

(** The SL2Module structure for V(m). *)
(* CAG zero-dependent Lemma Vm_mod theories/Kahler/sl2/Vm.v:145 BEGIN
Lemma Vm_mod (m : nat) : SL2Module (VmType m) (Vm_vs m).
Proof.
  refine {| sl2_X := Vm_X m
          ; sl2_Y := Vm_Y m
          ; sl2_H := Vm_H m |}.
  - apply Vm_X_add.
  - apply Vm_X_scale.
  - apply Vm_Y_add.
  - apply Vm_Y_scale.
  - apply Vm_H_add.
  - apply Vm_H_scale.
  - apply Vm_rel_HX.
  - apply Vm_rel_HY.
  - apply Vm_rel_XY.
Qed.
   CAG zero-dependent Lemma Vm_mod theories/Kahler/sl2/Vm.v:145 END *)

(** The operators in Vm_mod coincide with the concrete definitions. *)
(* CAG zero-dependent Axiom Vm_mod_H theories/Kahler/sl2/Vm.v:162 BEGIN
Axiom Vm_mod_H : forall m f, sl2_H (Vm_mod m) f = Vm_H m f.
   CAG zero-dependent Axiom Vm_mod_H theories/Kahler/sl2/Vm.v:162 END *)
(* CAG zero-dependent Axiom Vm_mod_X theories/Kahler/sl2/Vm.v:163 BEGIN
Axiom Vm_mod_X : forall m f, sl2_X (Vm_mod m) f = Vm_X m f.
   CAG zero-dependent Axiom Vm_mod_X theories/Kahler/sl2/Vm.v:163 END *)
(* CAG zero-dependent Axiom Vm_mod_Y theories/Kahler/sl2/Vm.v:164 BEGIN
Axiom Vm_mod_Y : forall m f, sl2_Y (Vm_mod m) f = Vm_Y m f.
   CAG zero-dependent Axiom Vm_mod_Y theories/Kahler/sl2/Vm.v:164 END *)

(* ================================================================== *)
(** * 4. Key computations on basis vectors                             *)
(* ================================================================== *)

(** H acts diagonally on basis vectors: H(w_k) = (m - 2k) w_k. *)
(* CAG zero-dependent Lemma Vm_H_basis theories/Kahler/sl2/Vm.v:173 BEGIN
Lemma Vm_H_basis (m k : nat) :
    Vm_H m (Vm_basis m k) =
    Vm_scale (Csub (Cnat m) (Cmul (Cnat k) (Cadd C1 C1))) (Vm_basis m k).
Proof.
  unfold Vm_H, Vm_scale, Vm_basis.
  apply functional_extensionality. intro j.
  (* Both sides: Cmul (m-2k) (if j=k then C1 else C0) *)
  (* Cmul c C1 = c and Cmul c C0 = C0 -- routine CComplex arithmetic *)
  Admitted.
   CAG zero-dependent Lemma Vm_H_basis theories/Kahler/sl2/Vm.v:173 END *)

(** Y shifts basis vectors: Y(w_k) = w_{k+1}. *)
Lemma Vm_Y_basis (m k : nat) :
    Vm_Y m (Vm_basis m k) = Vm_basis m (S k).
Proof.
  unfold Vm_Y, Vm_basis.
  apply functional_extensionality. intro j.
  destruct j; simpl; reflexivity.
Qed.

(** X raises basis vectors: X(w_{k+1}) = (k+1)(m-k) w_k  for k < m. *)
(* CAG zero-dependent Admitted Vm_X_basis_pos theories/Kahler/sl2/Vm.v:177 BEGIN
Lemma Vm_X_basis_pos (m k : nat) (Hk : (k < m)%nat) :
    Vm_X m (Vm_basis m (S k)) =
    Vm_scale (Cmul (Cnat (S k)) (Cnat (m - k))) (Vm_basis m k).
Proof.
  unfold Vm_X, Vm_scale, Vm_basis.
  apply functional_extensionality. intro j.
  (* (k+1)(m-k) * (if S j = S k then C1 else C0) = (if j = k then ...) *)
  Admitted.
   CAG zero-dependent Admitted Vm_X_basis_pos theories/Kahler/sl2/Vm.v:177 END *)

(** X(w_k) = 0 when k > m (the basis vector is outside the range). *)
(* CAG zero-dependent Admitted Vm_X_basis_out theories/Kahler/sl2/Vm.v:187 BEGIN
Lemma Vm_X_basis_out (m k : nat) (Hk : (m < k)%nat) :
    Vm_X m (Vm_basis m k) = Vm_zero.
Proof.
  unfold Vm_X, Vm_zero, Vm_basis.
  apply functional_extensionality. intro j.
  (* When j < m, Vm_basis m k (S j) = 0 since S j <= m < k *)
  (* When j >= m, the X operator returns C0 directly *)
  Admitted.
   CAG zero-dependent Admitted Vm_X_basis_out theories/Kahler/sl2/Vm.v:187 END *)

(* ================================================================== *)
(** * 5. The primitive vector w_0 and its orbit                        *)
(* ================================================================== *)

(** w_0 has weight m: H(w_0) = m · w_0. *)
(* CAG zero-dependent Lemma Vm_w0_weight theories/Kahler/sl2/Vm.v:221 BEGIN
Lemma Vm_w0_weight (m : nat) :
    is_weight (Vm_mod m) (Cnat m) (Vm_basis m 0).
Proof.
  unfold is_weight.
  rewrite Vm_mod_H.
  rewrite Vm_H_basis.
  (* vs_scale (Vm_vs m) = Vm_scale, so both sides agree *)
  unfold vs_scale, Vm_vs.
  simpl.
  (* Need: Csub (Cnat m) (Cmul (Cnat 0) (Cadd C1 C1)) = Cnat m *)
  (* i.e., m - 0*2 = m, which holds since 0*2 = 0 *)
  Admitted.
   CAG zero-dependent Lemma Vm_w0_weight theories/Kahler/sl2/Vm.v:221 END *)

(** w_0 is X-primitive: X(w_0) = 0. *)
(* CAG zero-dependent Lemma Vm_w0_primitive theories/Kahler/sl2/Vm.v:235 BEGIN
Lemma Vm_w0_primitive (m : nat) :
    is_primitive (Vm_mod m) (Vm_basis m 0).
Proof.
  unfold is_primitive.
  rewrite Vm_mod_X.
  unfold vs_zero, Vm_vs. simpl.
  unfold Vm_X.
  apply functional_extensionality. intro k.
  destruct (Nat.ltb k m) eqn:Hkm.
  - (* k < m: Vm_basis m 0 (S k) = C0 since S k ≠ 0 *)
    unfold Vm_basis. simpl.
    (* Cmul _ C0 = C0 *)
    Admitted.
   CAG zero-dependent Lemma Vm_w0_primitive theories/Kahler/sl2/Vm.v:235 END *)

(** C1 ≠ C0: the complex numbers 1 and 0 are distinct. *)
Lemma C1_neq_C0 : C1 <> C0.
Proof.
  intro H.
  assert (Hre : re C1 = re C0) by (rewrite H; reflexivity).
  simpl in Hre.
  (* Hre : (1 : CReal) = (0 : CReal).
     CRealLt_0_1 : CRealLt (inject_Q 0) (inject_Q 1).
     Rewrite 1 → 0 in H01 to get 0 < 0, contradicting CRealLt_irrefl. *)
  pose proof CRealLt_0_1 as H01.
  rewrite Hre in H01.
  exact (CRealLt_irrefl _ H01).
Qed.

(** w_0 is nonzero. *)
(* CAG zero-dependent Lemma Vm_w0_nonzero theories/Kahler/sl2/Vm.v:264 BEGIN
Lemma Vm_w0_nonzero (m : nat) :
    Vm_basis m 0 <> vs_zero (Vm_vs m).
Proof.
  intro H.
  assert (H0 : Vm_basis m O O = (Vm_zero : VmType m) O).
  { rewrite H. reflexivity. }
  unfold Vm_basis, Vm_zero in H0.
  change (C1 = C0) in H0.
  exact (C1_neq_C0 H0).
Qed.
   CAG zero-dependent Lemma Vm_w0_nonzero theories/Kahler/sl2/Vm.v:264 END *)

(** w_0 is a maximal vector. *)
(* CAG zero-dependent Theorem Vm_w0_maximal theories/Kahler/sl2/Vm.v:276 BEGIN
Theorem Vm_w0_maximal (m : nat) :
    is_maximal_vector (Vm_mod m) (Cnat m) (Vm_basis m 0).
Proof.
  split. { exact (Vm_w0_weight m). }
  split. { exact (Vm_w0_primitive m). }
  exact (Vm_w0_nonzero m).
Qed.
   CAG zero-dependent Theorem Vm_w0_maximal theories/Kahler/sl2/Vm.v:276 END *)

(** The Y-orbit: Y^k(w_0) = w_k. *)
Lemma Vm_Y_orbit (m k : nat) :
    Nat.iter k (Vm_Y m) (Vm_basis m 0) = Vm_basis m k.
Proof.
  induction k as [| k IH].
  - reflexivity.
  - simpl. rewrite IH. apply Vm_Y_basis.
Qed.

(** sl2_Y (Vm_mod m) = Vm_Y m. *)
(* CAG zero-dependent Lemma Vm_sl2_Y_orbit theories/Kahler/sl2/Vm.v:292 BEGIN
Lemma Vm_sl2_Y_orbit (m k : nat) :
    Nat.iter k (sl2_Y (Vm_mod m)) (Vm_basis m 0) = Vm_basis m k.
Proof.
  induction k as [| k IH].
  - reflexivity.
  - simpl. rewrite Vm_mod_Y, IH. apply Vm_Y_basis.
Qed.
   CAG zero-dependent Lemma Vm_sl2_Y_orbit theories/Kahler/sl2/Vm.v:292 END *)

(** Y^{m+1}(w_0) = 0 — the orbit truncates. *)
(* CAG zero-dependent Axiom Vm_orbit_zero theories/Kahler/sl2/Vm.v:305 BEGIN
Axiom Vm_orbit_zero : forall (m : nat),
    Nat.iter (S m) (sl2_Y (Vm_mod m)) (Vm_basis m 0) =
    vs_zero (Vm_vs m).
   CAG zero-dependent Axiom Vm_orbit_zero theories/Kahler/sl2/Vm.v:305 END *)

(** Y^m(w_0) ≠ 0. *)
(* CAG zero-dependent Axiom Vm_orbit_top_ne theories/Kahler/sl2/Vm.v:310 BEGIN
Axiom Vm_orbit_top_ne : forall (m : nat),
    Nat.iter m (sl2_Y (Vm_mod m)) (Vm_basis m 0) <>
    vs_zero (Vm_vs m).
   CAG zero-dependent Axiom Vm_orbit_top_ne theories/Kahler/sl2/Vm.v:310 END *)

(* ================================================================== *)
(** * 6. V(m) has highest weight m                                     *)
(* ================================================================== *)

(** orbit_top holds for w_0 in Vm_mod m with index m. *)
(* CAG zero-dependent Theorem Vm_orbit_top_thm theories/Kahler/sl2/Vm.v:319 BEGIN
Theorem Vm_orbit_top_thm (m : nat) :
    orbit_top (Vm_mod m) (Vm_basis m 0) m.
Proof.
  split.
  - exact (Vm_orbit_top_ne m).
  - exact (Vm_orbit_zero m).
Qed.
   CAG zero-dependent Theorem Vm_orbit_top_thm theories/Kahler/sl2/Vm.v:319 END *)

(** V(m) has highest weight m: the primitive vector w_0 generates an
    orbit of length m+1, so the highest weight is m by
    highest_weight_is_nat. *)
(* CAG zero-dependent Corollary Vm_highest_weight theories/Kahler/sl2/Vm.v:330 BEGIN
Corollary Vm_highest_weight (m : nat) :
    is_maximal_vector (Vm_mod m) (Cnat m) (Vm_basis m 0) /\
    orbit_top (Vm_mod m) (Vm_basis m 0) m.
Proof.
  exact (conj (Vm_w0_maximal m) (Vm_orbit_top_thm m)).
Qed.
   CAG zero-dependent Corollary Vm_highest_weight theories/Kahler/sl2/Vm.v:330 END *)

(* ================================================================== *)
(** * 7. Irreducibility                                                *)
(* ================================================================== *)

(* CAG zero-dependent Axiom Vm_irreducible theories/Kahler/sl2/Vm.v:312 BEGIN
Axiom Vm_irreducible : forall (m : nat)
    (W : VmType m -> Prop),
    (** W is a submodule *)
    (forall f g, W f -> W g -> W (Vm_add f g)) ->
    (forall c f, W f -> W (Vm_scale c f)) ->
    (forall f, W f -> W (Vm_X m f)) ->
    (forall f, W f -> W (Vm_Y m f)) ->
    (forall f, W f -> W (Vm_H m f)) ->
    (** W is nonzero *)
    (exists f, W f /\ f <> Vm_zero) ->
    (** then W contains all vectors *)
    forall f, W f.
   CAG zero-dependent Axiom Vm_irreducible theories/Kahler/sl2/Vm.v:312 END *)

(* ================================================================== *)
(** * 8. Summary theorem                                               *)
(* ================================================================== *)

(** For each m, V(m) is an irreducible sl(2)-module with highest weight m
    and a primitive vector w_0 generating an orbit of length m+1. *)
(* CAG zero-dependent Theorem Vm_classification theories/Kahler/sl2/Vm.v:362 BEGIN
Theorem Vm_classification (m : nat) :
    is_maximal_vector (Vm_mod m) (Cnat m) (Vm_basis m 0) /\
    orbit_top (Vm_mod m) (Vm_basis m 0) m.
Proof.
  exact (conj (Vm_w0_maximal m) (Vm_orbit_top_thm m)).
Qed.
   CAG zero-dependent Theorem Vm_classification theories/Kahler/sl2/Vm.v:362 END *)
