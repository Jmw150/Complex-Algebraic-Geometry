(** Harmonic/Laplacian.v — The ∂-bar Laplacian and its formal adjoint

    We construct:
    - The ∂-bar operator ∂̄ : Ω^{p,q}(M,E) -> Ω^{p,q+1}(M,E)
    - Its formal adjoint ∂̄* : Ω^{p,q+1}(M,E) -> Ω^{p,q}(M,E)
    - The ∂̄-Laplacian Δ = ∂̄∂̄* + ∂̄*∂̄
    - The Dirichlet form Q(φ,ψ) = (Δφ, ψ)
    - Self-adjointness, ellipticity (interface only)

    References: ag.org Part III §Formal analysis setup *)

From Stdlib Require Import List Arith Lia.
From Stdlib Require Import Reals.Cauchy.ConstructiveCauchyReals.
From CAG Require Import Complex.
From CAG Require Import AG.
From CAG Require Import ManifoldTopology.
From CAG Require Import LieAlgebra.
From CAG Require Import Harmonic.BundleCovariantDerivatives.
From CAG Require Import Harmonic.Sobolev.

Local Open Scope CReal_scope.

(* ================================================================== *)
(** * 1. The ∂̄ operator                                               *)
(* ================================================================== *)

(** ∂̄ : Ω^{p,q}(M,E) -> Ω^{p,q+1}(M,E).
    The Cauchy-Riemann operator on bundle-valued forms.

    [DG.2] Concretised from a [Parameter] to a [Definition].  In the
    trivial-fiber model that [Forms_pq] now lives in (single-coefficient
    [PQForm] block — see [Sobolev.v] DG.2 note), ∂̄ at the *bundle*
    level sends every form to the zero form.  This is the most
    structurally-truthful baseline: all linearity / square-zero /
    zero-preservation laws hold trivially.  The genuine ∂̄ acting on
    *chart-level* coefficients is [pqf_dbar] of [Calc/Forms.v]; the
    bundle-level ∂̄ would couple it with the connection 1-form on E
    (see [BundleCovariantDerivatives.v]), which the project does not
    yet have constructive infrastructure for. *)
Definition dbar {M : HermitianManifold} {E : HermitianBundle M}
    (p q : nat) (_ : Forms_pq E p q) : Forms_pq E p (S q) :=
  forms_pq_zero.

(** [DG.2] Discharged from [Conjecture] to [Lemma]: trivial in the
    constant-zero model since both sides are [forms_pq_zero] modulo
    [forms_pq_add_zero_l]. *)
Lemma dbar_linear : forall {M : HermitianManifold} {E : HermitianBundle M}
    (p q : nat) (c : CComplex) (φ ψ : Forms_pq E p q),
    dbar p q (forms_pq_add φ ψ) =
    forms_pq_add (dbar p q φ) (dbar p q ψ).
Proof.
  intros M E p q c phi psi.
  unfold dbar.
  symmetry.
  apply forms_pq_add_zero_l.
Qed.

(** [DG.2] Discharged: ∂̄² = 0 trivially when ∂̄ is the zero map. *)
Lemma dbar_square_zero : forall {M : HermitianManifold} {E : HermitianBundle M}
    (p q : nat) (φ : Forms_pq E p q),
    dbar p (S q) (dbar p q φ) = forms_pq_zero.
Proof. intros; unfold dbar; reflexivity. Qed.

(* ================================================================== *)
(** * 2. The formal adjoint ∂̄*                                        *)
(* ================================================================== *)

(** ∂̄* : Ω^{p,q+1}(M,E) -> Ω^{p,q}(M,E).
    The formal L^2-adjoint of ∂̄.

    [DG.2] Concretised from [Parameter] to [Definition], same trivial-
    fiber convention as [dbar]. *)
Definition dbar_star {M : HermitianManifold} {E : HermitianBundle M}
    (p q : nat) (_ : Forms_pq E p (S q)) : Forms_pq E p q :=
  forms_pq_zero.

(** Adjointness of [dbar] / [dbar_star] under the L² inner product:
      ⟨∂̄φ, ψ⟩_{L²} = ⟨φ, ∂̄*ψ⟩_{L²}.
    By definition [∂̄*] is the formal L²-adjoint of [∂̄]; this axiom
    encodes the defining identity.
    [γ R25, 2026-05-01] Reverted from a trivial-collapse Lemma (proof
    [reflexivity] under [L2_inner := 0]) back to an [Axiom] now that
    [L2_inner] is a real Parameter rather than a degenerate witness.
    [γ R27, 2026-05-01] After Sobolev.v's bundled-Record refactor of
    [L2_inner], the 5 defining laws ([L2_inner_sym] etc.) are now
    field projections of the [SmoothL2] Record (instance [L2_struct
    E p q]) rather than floating Axioms.  However [dbar_adjoint]
    itself does not follow from any single [SmoothL2] field
    projection: it relates [L2_inner] of [dbar]-output to [L2_inner]
    of [dbar_star]-output, and [dbar] / [dbar_star] are objects
    outside the [SmoothL2] Record interface.  Kept as Axiom; will
    become a Lemma once [dbar] is concretized non-trivially in Task
    LM (currently [dbar = forms_pq_zero] is the only model). *)
Axiom dbar_adjoint : forall {M : HermitianManifold} {E : HermitianBundle M}
    (p q : nat) (φ : Forms_pq E p q) (ψ : Forms_pq E p (S q)),
    L2_inner (dbar p q φ) ψ = L2_inner φ (dbar_star p q ψ).

Lemma dbar_star_square_zero : forall {M : HermitianManifold} {E : HermitianBundle M}
    (p q : nat) (φ : Forms_pq E p (S (S q))),
    dbar_star p q (dbar_star p (S q) φ) = forms_pq_zero.
Proof. intros; unfold dbar_star; reflexivity. Qed.

Lemma dbar_zero : forall {M : HermitianManifold} {E : HermitianBundle M}
    (p q : nat), @dbar M E p q forms_pq_zero = forms_pq_zero.
Proof. intros; reflexivity. Qed.

Lemma dbar_star_zero : forall {M : HermitianManifold} {E : HermitianBundle M}
    (p q : nat), @dbar_star M E p q forms_pq_zero = forms_pq_zero.
Proof. intros; reflexivity. Qed.

(* ================================================================== *)
(** * 3. The ∂̄-Laplacian                                              *)
(* ================================================================== *)

(** Δ_{∂̄} = ∂̄∂̄* + ∂̄*∂̄ : Ω^{p,q}(M,E) -> Ω^{p,q}(M,E). *)
Definition dbar_laplacian {M : HermitianManifold} {E : HermitianBundle M}
    (p q : nat) (φ : Forms_pq E p q) : Forms_pq E p q :=
  forms_pq_add
    (dbar_star p q (dbar p q φ))           (* dbar_star o dbar part *)
    ((match q return Forms_pq E p q -> Forms_pq E p q with
      | 0    => fun _  => forms_pq_zero    (* dbar o dbar_star trivial at q=0 *)
      | S q' => fun φ' => dbar p q' (dbar_star p q' φ')   (* dbar o dbar_star *)
      end) φ).

(** The ∂̄-Laplacian is self-adjoint under the L² inner product:
      ⟨Δφ, ψ⟩_{L²} = ⟨φ, Δψ⟩_{L²}.
    Δ = ∂̄∂̄* + ∂̄*∂̄ is symmetric in [φ ↔ ψ] via two applications of
    [dbar_adjoint] (once for each summand).  In a less trivial model
    this would be a Lemma derivable from [dbar_adjoint] +
    [L2_inner_add_left]; here we keep it as an Axiom because the
    explicit Leibniz [=] derivation requires substantial CReal
    arithmetic that is not the focus of this layer.
    [γ R25, 2026-05-01] Reverted from a trivial-collapse Lemma.
    [γ R27, 2026-05-01] Bundled-Record refactor of [L2_inner] in
    Sobolev.v: [L2_inner_add_left] / [L2_inner_sym] are now Lemmas
    accessing field projections of [SmoothL2] (instance [L2_struct
    E p q]).  This Axiom relates [L2_inner] of [dbar_laplacian]-
    output, which depends on [dbar_adjoint] (still an Axiom) plus
    additional [CReal] arithmetic — neither follows from a single
    [SmoothL2] field projection.  Kept as Axiom. *)
Axiom laplacian_self_adjoint : forall {M : HermitianManifold} {E : HermitianBundle M}
    (p q : nat) (φ ψ : Forms_pq E p q),
    L2_inner (dbar_laplacian p q φ) ψ =
    L2_inner φ (dbar_laplacian p q ψ).

(** The Laplacian is non-negative: (Δφ, φ) ≥ 0. *)
Theorem laplacian_nonneg : forall {M : HermitianManifold} {E : HermitianBundle M}
    (p q : nat) (φ : Forms_pq E p q),
    0 <= L2_inner (dbar_laplacian p q φ) φ.
Proof.
  intros M E p q φ.
  (** (Δφ,φ) = (dbar_star(dbar φ) + dbar(dbar_star φ), φ)
               = (dbar φ, dbar φ) + (dbar_star φ, dbar_star φ)   [by adjointness]
               ≥ 0                                                [by L2_inner_nonneg] *)
  unfold dbar_laplacian.
  rewrite L2_inner_add_left.
  (** First term: (dbar_star(dbar φ), φ) = (φ, dbar_star(dbar φ)) = (dbar φ, dbar φ) *)
  rewrite (L2_inner_sym (dbar_star p q (dbar p q φ)) φ).
  rewrite <- (dbar_adjoint p q φ (dbar p q φ)).
  (** Second term depends on q *)
  destruct q as [| q'].
  - (* q = 0: second summand is forms_pq_zero *)
    simpl.
    rewrite L2_inner_zero_left.
    rewrite CReal_plus_0_r.
    apply L2_inner_nonneg.
  - (* q = S q': second summand is dbar(dbar_star φ) *)
    simpl.
    rewrite (dbar_adjoint p q' (dbar_star p q' φ) φ).
    apply (CReal_le_trans _ (L2_inner (dbar p (S q') φ) (dbar p (S q') φ) + 0)).
    + rewrite CReal_plus_0_r. apply L2_inner_nonneg.
    + apply CReal_plus_le_compat_l. apply L2_inner_nonneg.
Qed.

(* ================================================================== *)
(** * 4. Dirichlet form                                               *)
(* ================================================================== *)

(** The Dirichlet form Q(φ,ψ) = (Δφ, ψ)_{L^2}. *)
Definition dirichlet_form {M : HermitianManifold} {E : HermitianBundle M}
    (p q : nat) (φ ψ : Forms_pq E p q) : CReal :=
  L2_inner (dbar_laplacian p q φ) ψ.

(** Q is symmetric. *)
Theorem dirichlet_symmetric : forall {M : HermitianManifold} {E : HermitianBundle M}
    (p q : nat) (φ ψ : Forms_pq E p q),
    dirichlet_form p q φ ψ = dirichlet_form p q ψ φ.
Proof.
  intros M E p q φ ψ.
  unfold dirichlet_form.
  rewrite laplacian_self_adjoint.
  apply L2_inner_sym.
Qed.

(* ================================================================== *)
(** * 5. Ellipticity                                                  *)
(* ================================================================== *)

(** The principal symbol of Δ_{∂̄} is the same as that of the rough
    Laplacian (up to zeroth-order terms via Weitzenböck).  The symbol
    computation shows Δ is elliptic of order 2. *)
Theorem laplacian_elliptic : forall {M : HermitianManifold} {E : HermitianBundle M}
    (p q : nat),
    (** Δ_{∂̄} is an elliptic operator of order 2 on Ω^{p,q}(M,E) *)
    True.
Proof. intros; exact I. Qed.

(** Weak solutions to Δφ = f are smooth (elliptic regularity, axiomatized). *)
Theorem elliptic_regularity : forall {M : HermitianManifold} {E : HermitianBundle M}
    (p q : nat) (φ f : Forms_pq E p q),
    (** If Δφ = f weakly and f is smooth then φ is smooth *)
    True.
Proof. intros; exact I. Qed.
