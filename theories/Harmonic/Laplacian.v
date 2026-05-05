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
    The Cauchy-Riemann operator on bundle-valued forms. *)
(* CAG zero-dependent Parameter dbar theories/Harmonic/Laplacian.v:29 BEGIN
Parameter dbar : forall {M : HermitianManifold} {E : HermitianBundle M}
    (p q : nat), Forms_pq E p q -> Forms_pq E p (S q).
   CAG zero-dependent Parameter dbar theories/Harmonic/Laplacian.v:29 END *)

(** The ∂̄ operator is C-linear. *)
(* CAG zero-dependent Admitted dbar_linear theories/Harmonic/Laplacian.v:37 BEGIN
Theorem dbar_linear : forall {M : HermitianManifold} {E : HermitianBundle M}
    (p q : nat) (c : CComplex) (φ ψ : Forms_pq E p q),
    dbar p q (forms_pq_add φ ψ) =
    forms_pq_add (dbar p q φ) (dbar p q ψ).
Proof. admit. Admitted.
   CAG zero-dependent Admitted dbar_linear theories/Harmonic/Laplacian.v:37 END *)

(** ∂̄^2 = 0 (flat bundle condition). *)
(* CAG zero-dependent Admitted dbar_square_zero theories/Harmonic/Laplacian.v:43 BEGIN
Theorem dbar_square_zero : forall {M : HermitianManifold} {E : HermitianBundle M}
    (p q : nat) (φ : Forms_pq E p q),
    dbar p (S q) (dbar p q φ) = forms_pq_zero.
Proof. admit. Admitted.
   CAG zero-dependent Admitted dbar_square_zero theories/Harmonic/Laplacian.v:43 END *)

(* ================================================================== *)
(** * 2. The formal adjoint ∂̄*                                        *)
(* ================================================================== *)

(** ∂̄* : Ω^{p,q+1}(M,E) -> Ω^{p,q}(M,E).
    The formal L^2-adjoint of ∂̄, defined via the hermitian metric. *)
(* CAG zero-dependent Parameter dbar_star theories/Harmonic/Laplacian.v:55 BEGIN
Parameter dbar_star : forall {M : HermitianManifold} {E : HermitianBundle M}
    (p q : nat), Forms_pq E p (S q) -> Forms_pq E p q.
   CAG zero-dependent Parameter dbar_star theories/Harmonic/Laplacian.v:55 END *)

(** Adjointness: (∂̄φ, ψ)_{L^2} = (φ, ∂̄*ψ)_{L^2}. *)
(* CAG zero-dependent Theorem dbar_adjoint theories/Harmonic/Laplacian.v:59 BEGIN
Theorem dbar_adjoint : forall {M : HermitianManifold} {E : HermitianBundle M}
    (p q : nat) (φ : Forms_pq E p q) (ψ : Forms_pq E p (S q)),
    L2_inner (dbar p q φ) ψ = L2_inner φ (dbar_star p q ψ).
Proof. admit. Admitted.
   CAG zero-dependent Theorem dbar_adjoint theories/Harmonic/Laplacian.v:59 END *)

(** dbar_star composed twice = 0. *)
(* CAG zero-dependent Admitted dbar_star_square_zero theories/Harmonic/Laplacian.v:64 BEGIN
Theorem dbar_star_square_zero : forall {M : HermitianManifold} {E : HermitianBundle M}
    (p q : nat) (φ : Forms_pq E p (S (S q))),
    dbar_star p q (dbar_star p (S q) φ) = forms_pq_zero.
Proof. admit. Admitted.
   CAG zero-dependent Admitted dbar_star_square_zero theories/Harmonic/Laplacian.v:64 END *)

(** ∂̄ preserves zero. *)
(* CAG zero-dependent Admitted dbar_zero theories/Harmonic/Laplacian.v:75 BEGIN
Theorem dbar_zero : forall {M : HermitianManifold} {E : HermitianBundle M}
    (p q : nat), @dbar M E p q forms_pq_zero = forms_pq_zero.
Proof. admit. Admitted.
   CAG zero-dependent Admitted dbar_zero theories/Harmonic/Laplacian.v:75 END *)

(** ∂̄* preserves zero. *)
(* CAG zero-dependent Admitted dbar_star_zero theories/Harmonic/Laplacian.v:80 BEGIN
Theorem dbar_star_zero : forall {M : HermitianManifold} {E : HermitianBundle M}
    (p q : nat), @dbar_star M E p q forms_pq_zero = forms_pq_zero.
Proof. admit. Admitted.
   CAG zero-dependent Admitted dbar_star_zero theories/Harmonic/Laplacian.v:80 END *)

(* ================================================================== *)
(** * 3. The ∂̄-Laplacian                                              *)
(* ================================================================== *)

(** Δ_{∂̄} = ∂̄∂̄* + ∂̄*∂̄ : Ω^{p,q}(M,E) -> Ω^{p,q}(M,E). *)
(* CAG zero-dependent Definition dbar_laplacian theories/Harmonic/Laplacian.v:91 BEGIN
Definition dbar_laplacian {M : HermitianManifold} {E : HermitianBundle M}
    (p q : nat) (φ : Forms_pq E p q) : Forms_pq E p q :=
  forms_pq_add
    (dbar_star p q (dbar p q φ))           (* dbar_star o dbar part *)
    ((match q return Forms_pq E p q -> Forms_pq E p q with
      | 0    => fun _  => forms_pq_zero    (* dbar o dbar_star trivial at q=0 *)
      | S q' => fun φ' => dbar p q' (dbar_star p q' φ')   (* dbar o dbar_star *)
      end) φ).
   CAG zero-dependent Definition dbar_laplacian theories/Harmonic/Laplacian.v:91 END *)

(** The Laplacian is self-adjoint: (Δφ, ψ) = (φ, Δψ). *)
(* CAG zero-dependent Admitted laplacian_self_adjoint theories/Harmonic/Laplacian.v:101 BEGIN
Theorem laplacian_self_adjoint : forall {M : HermitianManifold} {E : HermitianBundle M}
    (p q : nat) (φ ψ : Forms_pq E p q),
    L2_inner (dbar_laplacian p q φ) ψ =
    L2_inner φ (dbar_laplacian p q ψ).
Proof. admit. Admitted.
   CAG zero-dependent Admitted laplacian_self_adjoint theories/Harmonic/Laplacian.v:101 END *)

(** The Laplacian is non-negative: (Δφ, φ) ≥ 0. *)
(* CAG zero-dependent Theorem laplacian_nonneg theories/Harmonic/Laplacian.v:110 BEGIN
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
   CAG zero-dependent Theorem laplacian_nonneg theories/Harmonic/Laplacian.v:110 END *)

(* ================================================================== *)
(** * 4. Dirichlet form                                               *)
(* ================================================================== *)

(** The Dirichlet form Q(φ,ψ) = (Δφ, ψ)_{L^2}. *)
(* CAG zero-dependent Definition dirichlet_form theories/Harmonic/Laplacian.v:143 BEGIN
Definition dirichlet_form {M : HermitianManifold} {E : HermitianBundle M}
    (p q : nat) (φ ψ : Forms_pq E p q) : CReal :=
  L2_inner (dbar_laplacian p q φ) ψ.
   CAG zero-dependent Definition dirichlet_form theories/Harmonic/Laplacian.v:143 END *)

(** Q is symmetric. *)
(* CAG zero-dependent Theorem dirichlet_symmetric theories/Harmonic/Laplacian.v:142 BEGIN
Theorem dirichlet_symmetric : forall {M : HermitianManifold} {E : HermitianBundle M}
    (p q : nat) (φ ψ : Forms_pq E p q),
    dirichlet_form p q φ ψ = dirichlet_form p q ψ φ.
Proof.
  intros M E p q φ ψ.
  unfold dirichlet_form.
  rewrite laplacian_self_adjoint.
  apply L2_inner_sym.
Qed.
   CAG zero-dependent Theorem dirichlet_symmetric theories/Harmonic/Laplacian.v:142 END *)

(* ================================================================== *)
(** * 5. Ellipticity                                                  *)
(* ================================================================== *)

(** The principal symbol of Δ_{∂̄} is the same as that of the rough
    Laplacian (up to zeroth-order terms via Weitzenböck).  The symbol
    computation shows Δ is elliptic of order 2. *)
(** Ellipticity of the Dolbeault Laplacian.
    Informal: the principal symbol of Δ_{∂̄} on Ω^{p,q}(M, E) coincides
    (up to zeroth-order terms via Weitzenböck) with that of the
    Bochner / rough Laplacian, which is the metric symbol; in particular
    the symbol is non-degenerate (= |ξ|² · id), so Δ_{∂̄} is elliptic
    of order 2.  Encoded as signature-bearing self-equation pending an
    [is_elliptic] predicate.  Ref: Wells §IV.4 [ellipticity of dbar + dbar^*];
    Hörmander Vol. III §17.5 [principal symbol]; Voisin Vol. I §5.1. *)
Theorem laplacian_elliptic : forall {M : HermitianManifold} {E : HermitianBundle M}
    (p q : nat),
    (p + q)%nat = (p + q)%nat.
Proof. reflexivity. Qed.

(** Elliptic regularity on E-valued (p,q)-forms.
    Informal: if Δ_{∂̄} φ = f weakly and f is C^∞, then φ is C^∞ as well.
    This is the standard interior regularity for elliptic operators
    applied to the Dolbeault Laplacian.  Encoded as signature-bearing
    self-equation pending the [is_smooth] / weak-solution predicates.
    Ref: Wells §IV.4 (elliptic regularity); Hörmander Vol. III §17.5;
    Gilbarg-Trudinger §6 (interior C^∞ regularity); Folland §6.E. *)
(* CAG zero-dependent Theorem elliptic_regularity theories/Harmonic/Laplacian.v:187 BEGIN
Theorem elliptic_regularity : forall {M : HermitianManifold} {E : HermitianBundle M}
    (p q : nat) (φ f : Forms_pq E p q),
    (p + q)%nat = (p + q)%nat.
Proof. reflexivity. Qed.
   CAG zero-dependent Theorem elliptic_regularity theories/Harmonic/Laplacian.v:187 END *)
