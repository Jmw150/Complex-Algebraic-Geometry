(** Hypersurface/NormalBundle.v — Normal/conormal bundles and Adjunction Formula I

    For a smooth hypersurface V ⊂ M:
    - Normal bundle:   N_V = T'M|_V / T'V
    - Conormal bundle: N_V* = (N_V)* = ker(T'*M|_V → T'*V)^⊥

    Adjunction Formula I:
        N_V* ≅ [-V]|_V   (equivalently N_V ≅ [V]|_V)

    Proof:
    - Locally V = {f_α = 0}, so df_α ∈ Gamma(U_α, N_V-star)
    - Transition: df_α = (f_α/f_β) df_β on overlaps
      (since f_α = g_{αβ} f_β with g_{αβ} = f_α/f_β nonzero)
    - So the df_α trivialize N_V* ⊗ [V]|_V, hence N_V* = [-V]|_V.

    References: ag.org Part IX §Conormal bundle and Adjunction Formula I *)

From Stdlib Require Import List Arith ZArith.
From CAG Require Import Complex.
From CAG Require Import AG.
From CAG Require Import ManifoldTopology.
From CAG Require Import Divisor.LineBundleCech.
From CAG Require Import Divisor.DivisorBundle.

Local Open Scope CReal_scope.

(* ================================================================== *)
(** * 1. Smooth hypersurfaces                                          *)
(* ================================================================== *)

(** A smooth analytic hypersurface V ⊂ M. *)
Record SmoothHypersurface (M : ComplexManifold) : Type :=
{ sh_variety : Cn (cm_dim M) -> Prop
; sh_hypersurface : AnalyticHypersurface (fun _ => True) sh_variety
; sh_smooth : forall z, sh_variety z -> smooth_point (fun _ => True) sh_variety z
}.
Arguments sh_variety {M} _.
Arguments sh_hypersurface {M} _.
Arguments sh_smooth {M} _ _ _.

(** View a smooth hypersurface as a divisor component. *)
Definition sh_to_dc {M : ComplexManifold} (V : SmoothHypersurface M) :
    DivisorComponent M :=
  {| dc_variety := sh_variety V
   ; dc_is_hypersurface := sh_hypersurface V |}.

(** The divisor [V] associated to a smooth hypersurface. *)
Definition sh_divisor {M : ComplexManifold} (V : SmoothHypersurface M) :
    Divisor M :=
  [(1%Z, sh_to_dc V)].

(** The line bundle [V]. *)
(* CAG constructive-remove Definition sh_bundle theories/Hypersurface/NormalBundle.v:53 BEGIN -- repair partial command cleanup after removing LB
Definition sh_bundle {M : ComplexManifold} (V : SmoothHypersurface M) :
    HolLineBundleCech M :=
  (* CAG constructive-remove Command LB[sh_divisor theories/Hypersurface/NormalBundle.v:55 BEGIN -- missing LB
LB[sh_divisor V].

   CAG constructive-remove Command LB[sh_divisor theories/Hypersurface/NormalBundle.v:55 END *)
   CAG constructive-remove Definition sh_bundle theories/Hypersurface/NormalBundle.v:53 END *)

(* ================================================================== *)
(** * 2. Normal and conormal bundles                                   *)
(* ================================================================== *)

(** The holomorphic tangent bundle T'M restricted to V.
    We represent bundles as line bundles here (since V is a hypersurface,
    the normal bundle is a line bundle). *)

(** The normal bundle N_V of V in M: a holomorphic line bundle on V. *)
(* CAG zero-dependent Parameter normal_bundle theories/Hypersurface/NormalBundle.v:66 BEGIN
Parameter normal_bundle : forall {M : ComplexManifold},
    SmoothHypersurface M -> HolLineBundleCech M.
   CAG zero-dependent Parameter normal_bundle theories/Hypersurface/NormalBundle.v:66 END *)

(** The conormal bundle N_V^* = (N_V)^*. *)
(* CAG zero-dependent Definition conormal_bundle theories/Hypersurface/NormalBundle.v:70 BEGIN
Definition conormal_bundle {M : ComplexManifold} (V : SmoothHypersurface M) :
    HolLineBundleCech M :=
  hlb_dual (normal_bundle V).
   CAG zero-dependent Definition conormal_bundle theories/Hypersurface/NormalBundle.v:70 END *)

(** Local defining sections: on U_α, df_α is a nonzero section of N_V^*.
    These define a nowhere-zero global section of N_V^* ⊗ [V].

    Stated as a Conjecture pending the introduction of cotangent-bundle
    section infrastructure (df as a 1-form, restriction to V, nowhere-zero
    predicate). Reference: ag.org Part IX, Conormal Bundle §1. *)
(* CAG zero-dependent Conjecture df_sections_nonzero theories/Hypersurface/NormalBundle.v:80 BEGIN
Conjecture df_sections_nonzero : forall {M : ComplexManifold}
    (V : SmoothHypersurface M) (z : Cn (cm_dim M)),
    sh_variety V z ->
    smooth_point (fun _ => True) (sh_variety V) z.
   CAG zero-dependent Conjecture df_sections_nonzero theories/Hypersurface/NormalBundle.v:80 END *)
(* The smoothness witness is the structural fact that df_α ≠ 0 at z. *)

(** Transition relation: df_α = g_{αβ} · df_β where g_{αβ} = f_α/f_β.
    This means N_V^* has the same transition functions as [V],
    so N_V^* ≅ [V]|_V.

    Stated as a Conjecture pending overlap-cocycle infrastructure for
    holomorphic line bundles. Reference: ag.org Part IX, Conormal Bundle §1
    (Adjunction Formula derivation). *)
(* CAG zero-dependent Conjecture conormal_transition theories/Hypersurface/NormalBundle.v:93 BEGIN
Conjecture conormal_transition : forall {M : ComplexManifold}
    (V : SmoothHypersurface M),
    hlb_iso (hlb_tensor (conormal_bundle V) (sh_bundle V)) (hlb_trivial M).
   CAG zero-dependent Conjecture conormal_transition theories/Hypersurface/NormalBundle.v:93 END *)

(* ================================================================== *)
(** * 3. Adjunction Formula I: N_V^* ≅ [-V]|_V                        *)
(* ================================================================== *)

(** Adjunction Formula I:
    The conormal bundle of V in M is isomorphic to [-V]|_V,
    i.e., N_V* ≅ [-V]|_V  (equivalently N_V ≅ [V]|_V).

    Proof: the df_α trivialize N_V* ⊗ [V]|_V, so this tensor product
    is trivial. Hence N_V^* ≅ [-V]|_V. *)

(* CAG zero-dependent Admitted adjunction_formula_I theories/Hypersurface/NormalBundle.v:115 BEGIN
Theorem adjunction_formula_I : forall {M : ComplexManifold}
    (V : SmoothHypersurface M),
    hlb_iso (conormal_bundle V) (hlb_dual (sh_bundle V)).
Proof. Admitted.
   CAG zero-dependent Admitted adjunction_formula_I theories/Hypersurface/NormalBundle.v:115 END *)

(** Equivalently: N_V ≅ [V]|_V. *)
(* CAG zero-dependent Theorem normal_bundle_iso_divisor_bundle theories/Hypersurface/NormalBundle.v:118 BEGIN
Theorem normal_bundle_iso_divisor_bundle : forall {M : ComplexManifold}
    (V : SmoothHypersurface M),
    hlb_iso (normal_bundle V) (sh_bundle V).
Proof.
  intros M V.
  (* normal_bundle V ≅ (normal_bundle V)** ≅ (sh_bundle V)** ≅ sh_bundle V *)
  apply hlb_iso_trans with (hlb_dual (hlb_dual (normal_bundle V))).
  - apply hlb_iso_symm. apply hlb_dual_dual.
  - apply hlb_iso_trans with (hlb_dual (hlb_dual (sh_bundle V))).
    + (* (conormal_bundle V = hlb_dual (normal_bundle V)) ≅ hlb_dual (sh_bundle V)
         so apply hlb_dual_cong to adjunction_formula_I *)
      apply hlb_dual_cong. apply adjunction_formula_I.
    + apply hlb_dual_dual.
Qed.
   CAG zero-dependent Theorem normal_bundle_iso_divisor_bundle theories/Hypersurface/NormalBundle.v:118 END *)

(** Corollary: N_V* ⊗ [V]|_V is trivial. *)
(* CAG zero-dependent Theorem conormal_tensor_divisor_trivial theories/Hypersurface/NormalBundle.v:134 BEGIN
Theorem conormal_tensor_divisor_trivial : forall {M : ComplexManifold}
    (V : SmoothHypersurface M),
    hlb_iso (hlb_tensor (conormal_bundle V) (sh_bundle V))
            (hlb_trivial M).
Proof.
  intros M V.
  apply hlb_iso_trans with (hlb_tensor (hlb_dual (sh_bundle V)) (sh_bundle V)).
  - (* conormal_bundle V ≅ hlb_dual (sh_bundle V) by adjunction_formula_I *)
    apply hlb_tensor_cong.
    + apply adjunction_formula_I.
    + apply hlb_iso_refl.
  - apply hlb_iso_trans with (hlb_tensor (sh_bundle V) (hlb_dual (sh_bundle V))).
    + apply hlb_tensor_comm.
    + apply hlb_tensor_dual.
Qed.
   CAG zero-dependent Theorem conormal_tensor_divisor_trivial theories/Hypersurface/NormalBundle.v:134 END *)

(* ================================================================== *)
(** * 4. Application: N_{V_d}^* for hypersurface in ℙⁿ                *)
(* ================================================================== *)

(** For a smooth hypersurface V_d of degree d in ℙⁿ,
    N_{V_d} ≅ O(d)|_{V_d}.

    Stated as a Conjecture: needs O(d) (twisting sheaf / hyperplane bundle
    powers) infrastructure as a HolLineBundleCech, plus the hypersurface
    degree function `sh_degree_Pn`. Reference: ag.org Part IX, Adjunction
    Formula corollary for projective hypersurfaces. *)
(* CAG zero-dependent Conjecture normal_bundle_degree_d_hypersurface theories/Hypersurface/NormalBundle.v:157 BEGIN
Conjecture normal_bundle_degree_d_hypersurface :
    forall (n : nat) (V : SmoothHypersurface (CPn_manifold n)),
    hlb_iso (normal_bundle V) (sh_bundle V).
   CAG zero-dependent Conjecture normal_bundle_degree_d_hypersurface theories/Hypersurface/NormalBundle.v:157 END *)
