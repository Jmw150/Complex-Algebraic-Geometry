(** * Galois/Field.v
    Abstract fields, field extensions, and the poset of intermediate fields.

    A field is a commutative ring in which every non-zero element has a
    multiplicative inverse.  A field extension K ↪ L is a ring homomorphism
    that is injective (automatically, since K is a field).

    We build the posets needed for the Galois correspondence:
    - [IntermFields K L emb] : intermediate fields F with K ↪ F ↪ L
    - ordered by subset inclusion of the images in L. *)

Require Import CAG.Order.Poset.
From Stdlib Require Import Logic.FunctionalExtensionality.
From Stdlib Require Import Logic.ProofIrrelevance.
From Stdlib Require Import Logic.Classical.
From Stdlib Require Import Logic.PropExtensionality.
From Stdlib Require Import Setoid Ring.

Open Scope order_scope.

(** ** Commutative ring *)

Record CommRing (R : Type) : Type := {
  cr_zero : R;
  cr_one  : R;
  cr_add  : R -> R -> R;
  cr_mul  : R -> R -> R;
  cr_neg  : R -> R;

  cr_add_assoc  : forall a b c, cr_add a (cr_add b c) = cr_add (cr_add a b) c;
  cr_add_comm   : forall a b,   cr_add a b = cr_add b a;
  cr_add_zero   : forall a,     cr_add a cr_zero = a;
  cr_add_neg    : forall a,     cr_add a (cr_neg a) = cr_zero;

  cr_mul_assoc  : forall a b c, cr_mul a (cr_mul b c) = cr_mul (cr_mul a b) c;
  cr_mul_comm   : forall a b,   cr_mul a b = cr_mul b a;
  cr_mul_one    : forall a,     cr_mul a cr_one = a;

  cr_distrib    : forall a b c,
    cr_mul a (cr_add b c) = cr_add (cr_mul a b) (cr_mul a c);
}.

Arguments cr_zero {R}.
Arguments cr_one  {R}.
Arguments cr_add  {R}.
Arguments cr_mul  {R}.
Arguments cr_neg  {R}.
Arguments cr_add_assoc {R}.
Arguments cr_add_comm  {R}.
Arguments cr_add_zero  {R}.
Arguments cr_add_neg   {R}.
Arguments cr_mul_assoc {R}.
Arguments cr_mul_comm  {R}.
Arguments cr_mul_one   {R}.
Arguments cr_distrib   {R}.

Notation "0_{ R }" := (cr_zero R) (at level 0) : order_scope.
Notation "1_{ R }" := (cr_one  R) (at level 0) : order_scope.
Notation "a +_{ R } b" := (cr_add R a b) (at level 50, left associativity) : order_scope.
Notation "a *_{ R } b" := (cr_mul R a b) (at level 40, left associativity) : order_scope.
Notation "-_{ R } a"   := (cr_neg R a)   (at level 35) : order_scope.

(** A non-trivial ring has 0 ≠ 1. *)
Definition NonTrivial {R : Type} (cr : CommRing R) : Prop :=
  cr.(cr_zero) <> cr.(cr_one).

(** Subtraction. *)
Definition cr_sub {R : Type} (cr : CommRing R) (a b : R) : R :=
  cr.(cr_add) a (cr.(cr_neg) b).

(** ** Field *)

(** A field is a non-trivial commutative ring in which every non-zero
    element has a multiplicative inverse. *)

Record Field (F : Type) : Type := {
  fld_ring    :> CommRing F;
  fld_nontrivial : fld_ring.(cr_zero) <> fld_ring.(cr_one);
  fld_inv     : F -> F;
  fld_inv_mul : forall a, a <> fld_ring.(cr_zero) ->
                  fld_ring.(cr_mul) a (fld_inv a) = fld_ring.(cr_one);
}.

Arguments fld_ring    {F}.
Arguments fld_nontrivial {F}.
Arguments fld_inv     {F}.
Arguments fld_inv_mul {F}.

(** Division. *)
Definition fld_div {F : Type} (fld : Field F) (a b : F)
    (hb : b <> fld.(fld_ring).(cr_zero)) : F :=
  fld.(fld_ring).(cr_mul) a (fld.(fld_inv) b).

(** In a field, 0 has no inverse is irrelevant because inv(0) is unspecified.
    Key derived fact: no zero divisors. *)
Lemma field_no_zero_div {F : Type} (fld : Field F) (a b : F) :
    fld.(fld_ring).(cr_mul) a b = fld.(fld_ring).(cr_zero) ->
    a = fld.(fld_ring).(cr_zero) \/ b = fld.(fld_ring).(cr_zero).
Proof.
  intro Hab.
  set (rg := fld.(fld_ring)) in *.
  (* Derive: x * 0 = 0 for any x *)
  assert (mul_zero : forall x, cr_mul rg x (cr_zero rg) = cr_zero rg).
  { intro x.
    set (t := cr_mul rg x (cr_zero rg)).
    (* Hd : t = t + t, from x*(0+0) = x*0+x*0 and 0+0=0 *)
    assert (Hd : t = cr_add rg t t).
    { unfold t.
      assert (Hdist := @cr_distrib F rg x (cr_zero rg) (cr_zero rg)).
      rewrite cr_add_zero in Hdist.
      exact Hdist. }
    (* (t+t) + (-t) = 0 *)
    assert (Hstep_a : cr_add rg (cr_add rg t t) (cr_neg rg t) = cr_zero rg).
    { rewrite <- Hd. apply cr_add_neg. }
    (* (t+t) + (-t) = t by associativity *)
    assert (Hstep_b : cr_add rg (cr_add rg t t) (cr_neg rg t) = t).
    { rewrite <- cr_add_assoc.
      rewrite cr_add_neg.
      apply cr_add_zero. }
    exact (eq_trans (eq_sym Hstep_b) Hstep_a). }
  destruct (classic (a = cr_zero rg)) as [Ha | Ha].
  - left. exact Ha.
  - right.
    assert (have_inv : cr_mul rg a (fld.(fld_inv) a) = cr_one rg).
    { exact (fld.(fld_inv_mul) a Ha). }
    assert (Hstep : cr_mul rg (fld.(fld_inv) a) (cr_mul rg a b) = b).
    { rewrite cr_mul_assoc.
      rewrite cr_mul_comm in have_inv.
      rewrite have_inv.
      rewrite cr_mul_comm.
      apply cr_mul_one. }
    rewrite Hab in Hstep.
    rewrite mul_zero in Hstep.
    exact (eq_sym Hstep).
Qed.

(** ** Derived commutative ring lemmas *)

Lemma cr_mul_zero_r {R : Type} (rg : CommRing R) :
  forall a, cr_mul rg a (cr_zero rg) = cr_zero rg.
Proof.
  intro a. set (t := cr_mul rg a (cr_zero rg)).
  assert (Hd : t = cr_add rg t t).
  { unfold t.
    assert (Hdist := cr_distrib rg a (cr_zero rg) (cr_zero rg)).
    rewrite cr_add_zero in Hdist. exact Hdist. }
  assert (Hstep_a : cr_add rg (cr_add rg t t) (cr_neg rg t) = cr_zero rg).
  { rewrite <- Hd. apply cr_add_neg. }
  assert (Hstep_b : cr_add rg (cr_add rg t t) (cr_neg rg t) = t).
  { rewrite <- cr_add_assoc, cr_add_neg. apply cr_add_zero. }
  exact (eq_trans (eq_sym Hstep_b) Hstep_a).
Qed.

Lemma cr_mul_zero_l {R : Type} (rg : CommRing R) :
  forall a, cr_mul rg (cr_zero rg) a = cr_zero rg.
Proof. intro a. rewrite cr_mul_comm. apply cr_mul_zero_r. Qed.

Lemma cr_one_mul {R : Type} (rg : CommRing R) :
  forall a, cr_mul rg (cr_one rg) a = a.
Proof. intro a. rewrite cr_mul_comm. apply cr_mul_one. Qed.

Lemma cr_add_zero_l {R : Type} (rg : CommRing R) :
  forall a, cr_add rg (cr_zero rg) a = a.
Proof. intro a. rewrite cr_add_comm. apply cr_add_zero. Qed.

Lemma cr_add_neg_l {R : Type} (rg : CommRing R) :
  forall a, cr_add rg (cr_neg rg a) a = cr_zero rg.
Proof. intro a. rewrite cr_add_comm. apply cr_add_neg. Qed.

(** Additive inverse is unique: if a+b=0 then b=-a. *)
Lemma cr_add_inv_uniq {R : Type} (rg : CommRing R) :
  forall a b, cr_add rg a b = cr_zero rg -> b = cr_neg rg a.
Proof.
  intros a b Hab.
  assert (H : cr_add rg (cr_neg rg a) (cr_add rg a b) = cr_neg rg a).
  { rewrite Hab. apply cr_add_zero. }
  rewrite cr_add_assoc, cr_add_neg_l, cr_add_zero_l in H. exact H.
Qed.

(** -(-a) = a *)
Lemma cr_neg_neg {R : Type} (rg : CommRing R) :
  forall a, cr_neg rg (cr_neg rg a) = a.
Proof.
  intro a.
  apply eq_sym.
  apply cr_add_inv_uniq.
  apply cr_add_neg_l.
Qed.

(** (-a) * b = -(a * b) *)
Lemma cr_neg_mul_l {R : Type} (rg : CommRing R) :
  forall a b, cr_mul rg (cr_neg rg a) b = cr_neg rg (cr_mul rg a b).
Proof.
  intros a b.
  apply cr_add_inv_uniq.
  rewrite (cr_mul_comm rg a b), (cr_mul_comm rg (cr_neg rg a) b).
  rewrite <- cr_distrib.
  rewrite cr_add_neg.
  apply cr_mul_zero_r.
Qed.

Lemma cr_neg_mul_r {R : Type} (rg : CommRing R) :
  forall a b, cr_mul rg a (cr_neg rg b) = cr_neg rg (cr_mul rg a b).
Proof. intros a b. rewrite cr_mul_comm, cr_neg_mul_l, cr_mul_comm. reflexivity. Qed.

(** (-a) * (-b) = a * b *)
Lemma cr_neg_mul_neg {R : Type} (rg : CommRing R) :
  forall a b, cr_mul rg (cr_neg rg a) (cr_neg rg b) = cr_mul rg a b.
Proof. intros a b. rewrite cr_neg_mul_l, cr_neg_mul_r, cr_neg_neg. reflexivity. Qed.

(** -(a + b) = -a + -b *)
Lemma cr_neg_add {R : Type} (rg : CommRing R) :
  forall a b, cr_neg rg (cr_add rg a b) = cr_add rg (cr_neg rg a) (cr_neg rg b).
Proof.
  intros a b.
  symmetry. apply cr_add_inv_uniq.
  (* Goal: cr_add (cr_add a b) (cr_add (cr_neg a) (cr_neg b)) = cr_zero *)
  rewrite (cr_add_assoc rg (cr_add rg a b) (cr_neg rg a) (cr_neg rg b)).
  (* Goal: cr_add (cr_add (cr_add a b) (cr_neg a)) (cr_neg b) = cr_zero *)
  rewrite <- (cr_add_assoc rg a b (cr_neg rg a)).
  (* Goal: cr_add (cr_add a (cr_add b (cr_neg a))) (cr_neg b) = cr_zero *)
  rewrite (cr_add_comm rg b (cr_neg rg a)).
  (* Goal: cr_add (cr_add a (cr_add (cr_neg a) b)) (cr_neg b) = cr_zero *)
  rewrite (cr_add_assoc rg a (cr_neg rg a) b).
  (* Goal: cr_add (cr_add (cr_add a (cr_neg a)) b) (cr_neg b) = cr_zero *)
  rewrite (cr_add_neg rg a).
  (* Goal: cr_add (cr_add cr_zero b) (cr_neg b) = cr_zero *)
  rewrite (cr_add_zero_l rg b).
  apply (cr_add_neg rg b).
Qed.

(** Derived right-distributivity from left-distributivity + comm. *)
Lemma cr_distrib_r {R : Type} (rg : CommRing R) :
  forall a b c, cr_mul rg (cr_add rg a b) c =
                cr_add rg (cr_mul rg a c) (cr_mul rg b c).
Proof.
  intros a b c.
  rewrite (cr_mul_comm rg (cr_add rg a b) c).
  rewrite cr_distrib.
  rewrite (cr_mul_comm rg c a), (cr_mul_comm rg c b).
  reflexivity.
Qed.

(** Cancellation in rings: a + c = b + c → a = b. *)
Lemma cr_add_cancel_r {R : Type} (rg : CommRing R) :
  forall a b c, cr_add rg a c = cr_add rg b c -> a = b.
Proof.
  intros a b c Hac.
  assert (Heq : cr_add rg (cr_add rg a c) (cr_neg rg c)
              = cr_add rg (cr_add rg b c) (cr_neg rg c)).
  { rewrite Hac. reflexivity. }
  rewrite <- (cr_add_assoc rg a c (cr_neg rg c)) in Heq.
  rewrite <- (cr_add_assoc rg b c (cr_neg rg c)) in Heq.
  rewrite (cr_add_neg rg c) in Heq.
  rewrite (cr_add_zero rg a) in Heq.
  rewrite (cr_add_zero rg b) in Heq.
  exact Heq.
Qed.

Lemma cr_add_cancel_l {R : Type} (rg : CommRing R) :
  forall a b c, cr_add rg c a = cr_add rg c b -> a = b.
Proof.
  intros a b c Hac.
  rewrite (cr_add_comm rg c a), (cr_add_comm rg c b) in Hac.
  apply (cr_add_cancel_r rg a b c). exact Hac.
Qed.

(** Generic ring_theory instance for any CommRing. Useful for [ring] tactic. *)
Lemma cr_ring_theory {R : Type} (rg : CommRing R) :
  ring_theory (cr_zero rg) (cr_one rg)
    (cr_add rg) (cr_mul rg) (cr_sub rg) (cr_neg rg) eq.
Proof.
  constructor.
  - intro x. apply (cr_add_zero_l rg).
  - intros x y. apply (cr_add_comm rg).
  - intros x y z. apply (cr_add_assoc rg).
  - intro x. apply (cr_one_mul rg).
  - intros x y. apply (cr_mul_comm rg).
  - intros x y z. apply (cr_mul_assoc rg).
  - intros x y z. apply (cr_distrib_r rg).
  - intros x y. reflexivity.
  - intro x. apply (cr_add_neg rg).
Qed.

(** ** Ring homomorphism *)

Record RingHom {R S : Type} (cr_R : CommRing R) (cr_S : CommRing S) : Type := {
  rhom_map  : R -> S;
  rhom_add  : forall a b, rhom_map (cr_R.(cr_add) a b)
                        = cr_S.(cr_add) (rhom_map a) (rhom_map b);
  rhom_mul  : forall a b, rhom_map (cr_R.(cr_mul) a b)
                        = cr_S.(cr_mul) (rhom_map a) (rhom_map b);
  rhom_one  : rhom_map cr_R.(cr_one) = cr_S.(cr_one);
}.

Arguments rhom_map {R S cr_R cr_S}.
Arguments rhom_add {R S cr_R cr_S}.
Arguments rhom_mul {R S cr_R cr_S}.
Arguments rhom_one {R S cr_R cr_S}.

(** A ring homomorphism automatically preserves zero and negation. *)
Lemma rhom_zero {R S : Type} {cr_R : CommRing R} {cr_S : CommRing S}
    (φ : RingHom cr_R cr_S) :
    φ.(rhom_map) cr_R.(cr_zero) = cr_S.(cr_zero).
Proof.
  (* φ(0+0) = φ(0)+φ(0); since 0+0=0 we get φ(0) = φ(0)+φ(0).
     Adding -φ(0) to both sides gives 0 = φ(0). *)
  pose proof (φ.(rhom_add) cr_R.(cr_zero) cr_R.(cr_zero)) as Hadd.
  assert (Hz : cr_R.(cr_add) cr_R.(cr_zero) cr_R.(cr_zero) = cr_R.(cr_zero)).
  { apply cr_add_zero. }
  rewrite Hz in Hadd.
  (* Hadd : φ(0) = φ(0) + φ(0) *)
  (* Derive: (φ(0) + φ(0)) + (-φ(0)) = x + (-φ(0)) where x=φ(0) *)
  (* Then: x = (x+x)+(-x) = x+(x+(-x)) = x+0 = x  AND  (x+x)+(-x) = x+(-x) = 0 *)
  set (x := φ.(rhom_map) cr_R.(cr_zero)) in *.
  (* (x+x)+(-x) = 0: from Hadd (x = x+x) backward and add_neg *)
  assert (step_a : cr_S.(cr_add) (cr_S.(cr_add) x x) (cr_S.(cr_neg) x)
                 = cr_S.(cr_zero)).
  { rewrite <- Hadd. apply cr_add_neg. }
  (* (x+x)+(-x) = x: via associativity and add_neg and add_zero *)
  assert (step_b : cr_S.(cr_add) (cr_S.(cr_add) x x) (cr_S.(cr_neg) x) = x).
  { assert (H1 : cr_S.(cr_add) (cr_S.(cr_add) x x) (cr_S.(cr_neg) x)
               = cr_S.(cr_add) x (cr_S.(cr_add) x (cr_S.(cr_neg) x))).
    { symmetry. apply cr_add_assoc. }
    rewrite H1.
    assert (H2 : cr_S.(cr_add) x (cr_S.(cr_neg) x) = cr_S.(cr_zero)).
    { apply cr_add_neg. }
    rewrite H2. apply cr_add_zero. }
  rewrite step_b in step_a.
  exact step_a.
Qed.

Lemma rhom_neg {R S : Type} {cr_R : CommRing R} {cr_S : CommRing S}
    (φ : RingHom cr_R cr_S) (a : R) :
    φ.(rhom_map) (cr_R.(cr_neg) a) = cr_S.(cr_neg) (φ.(rhom_map) a).
Proof.
  (* φ(a)+φ(-a) = φ(a+(-a)) = φ(0) = 0.
     Uniqueness: since φ(a)+φ(-a) = 0 = φ(a)+(-φ(a)), we get φ(-a) = -φ(a). *)
  pose proof (φ.(rhom_add) a (cr_R.(cr_neg) a)) as Hadd.
  assert (Hann : cr_R.(cr_add) a (cr_R.(cr_neg) a) = cr_R.(cr_zero)).
  { apply cr_add_neg. }
  rewrite Hann in Hadd. clear Hann.
  rewrite (rhom_zero φ) in Hadd.
  (* Hadd : φ(a) + φ(-a) = 0 *)
  set (pa  := φ.(rhom_map) a).
  set (pna := φ.(rhom_map) (cr_R.(cr_neg) a)).
  set (npa := cr_S.(cr_neg) pa).
  (* npa + pa = 0 *)
  assert (H1 : cr_S.(cr_add) npa pa = cr_S.(cr_zero)).
  { unfold npa.
    assert (Hc : cr_S.(cr_add) (cr_S.(cr_neg) pa) pa
               = cr_S.(cr_add) pa (cr_S.(cr_neg) pa)).
    { apply cr_add_comm. }
    rewrite Hc. apply cr_add_neg. }
  (* pna = 0+pna = (npa+pa)+pna = npa+(pa+pna) = npa+0 = npa *)
  (* 0 + pna = pna *)
  assert (H0pna : cr_S.(cr_add) cr_S.(cr_zero) pna = pna).
  { assert (Hc2 : cr_S.(cr_add) cr_S.(cr_zero) pna
                = cr_S.(cr_add) pna cr_S.(cr_zero)).
    { apply cr_add_comm. }
    rewrite Hc2. apply cr_add_zero. }
  (* (npa+pa)+pna = npa+(pa+pna) *)
  assert (Hassoc : cr_S.(cr_add) (cr_S.(cr_add) npa pa) pna
                 = cr_S.(cr_add) npa (cr_S.(cr_add) pa pna)).
  { symmetry. apply cr_add_assoc. }
  (* pa + pna = 0 (from Hadd) *)
  assert (Hpapna : cr_S.(cr_add) pa pna = cr_S.(cr_zero)).
  { exact (eq_sym Hadd). }
  (* Putting it together: pna = 0+pna = (npa+pa)+pna = npa+(pa+pna) = npa+0 = npa *)
  rewrite <- H0pna.
  rewrite <- H1.
  rewrite Hassoc.
  rewrite Hpapna.
  apply cr_add_zero.
Qed.

(** A field homomorphism is a ring hom between fields.  Every such map is
    injective (kernel of a field hom is an ideal, which must be {0} or all of F,
    and it's not all since 1 maps to 1). *)

Definition FieldHom {K L : Type} (fK : Field K) (fL : Field L) :=
  RingHom fK.(fld_ring) fL.(fld_ring).

Lemma field_hom_injective {K L : Type} {fK : Field K} {fL : Field L}
    (φ : FieldHom fK fL) :
    forall a b, φ.(rhom_map) a = φ.(rhom_map) b -> a = b.
Proof.
  intros a b Heq.
  destruct (classic (a = b)) as [H | Hne]. { exact H. }
  exfalso.
  (* Use fK and fL directly via the :> coercion from Field to CommRing *)
  (* d = a + (-b), a nonzero difference *)
  set (d := fK.(cr_add) a (fK.(cr_neg) b)).
  assert (Hd_ne : d <> fK.(cr_zero)).
  { intro Hd. apply Hne.
    pose proof (fK.(cr_add_zero) a) as Ha0.
    assert (Hnegb : fK.(cr_add) (fK.(cr_neg) b) b = fK.(cr_zero)).
    { rewrite fK.(cr_add_comm). apply fK.(cr_add_neg). }
    pose proof (fK.(cr_add_assoc) a (fK.(cr_neg) b) b) as Hassoc.
    fold d in Hassoc.
    rewrite Hnegb in Hassoc. rewrite Ha0 in Hassoc.
    rewrite Hd in Hassoc.
    rewrite fK.(cr_add_comm) in Hassoc. rewrite fK.(cr_add_zero) in Hassoc.
    exact Hassoc. }
  (* φ(d) = 0_L *)
  assert (Hphid : φ.(rhom_map) d = fL.(cr_zero)).
  { unfold d.
    rewrite (φ.(rhom_add) a (fK.(cr_neg) b)).
    rewrite (rhom_neg φ b).
    rewrite Heq.
    apply fL.(cr_add_neg). }
  (* 0_L * x = 0_L for any x *)
  assert (LH0_mul : forall x, fL.(cr_mul) fL.(cr_zero) x = fL.(cr_zero)).
  { intro x.
    set (t := fL.(cr_mul) fL.(cr_zero) x).
    assert (Htt : t = fL.(cr_add) t t).
    { unfold t. rewrite (fL.(cr_mul_comm) fL.(cr_zero) x).
      pose proof (fL.(cr_distrib) x fL.(cr_zero) fL.(cr_zero)) as Hdist.
      rewrite fL.(cr_add_zero) in Hdist. exact Hdist. }
    assert (Ha : fL.(cr_add) (fL.(cr_add) t t) (fL.(cr_neg) t) = fL.(cr_zero)).
    { rewrite <- Htt. apply fL.(cr_add_neg). }
    assert (Hb : fL.(cr_add) (fL.(cr_add) t t) (fL.(cr_neg) t) = t).
    { rewrite <- fL.(cr_add_assoc). rewrite fL.(cr_add_neg). apply fL.(cr_add_zero). }
    exact (eq_trans (eq_sym Hb) Ha). }
  (* φ(d * d⁻¹) = φ(1_K) = 1_L *)
  assert (H1L : φ.(rhom_map) (fK.(cr_mul) d (fK.(fld_inv) d)) = fL.(cr_one)).
  { rewrite (fK.(fld_inv_mul) d Hd_ne). apply φ.(rhom_one). }
  (* φ(d * d⁻¹) = φ(d) * φ(d⁻¹) = 0_L * φ(d⁻¹) = 0_L *)
  assert (H0L : φ.(rhom_map) (fK.(cr_mul) d (fK.(fld_inv) d)) = fL.(cr_zero)).
  { rewrite (φ.(rhom_mul) d (fK.(fld_inv) d)).
    rewrite Hphid. apply LH0_mul. }
  (* 1_L = 0_L, contradiction *)
  exact (fL.(fld_nontrivial) (eq_sym (eq_trans (eq_sym H1L) H0L))).
Qed.

(** ** Field extension *)

(** A field extension consists of fields K and L together with an embedding
    (field homomorphism) ι : K → L.  We treat ι as part of the data so that
    different embeddings of the same abstract field give different extensions. *)

Record FieldExtension : Type := {
  ext_base   : Type;
  ext_top    : Type;
  ext_fK     : Field ext_base;
  ext_fL     : Field ext_top;
  ext_emb    : FieldHom ext_fK ext_fL;
}.

(** Coercions for convenience. *)
Definition ext_K (E : FieldExtension) := E.(ext_base).
Definition ext_L (E : FieldExtension) := E.(ext_top).

(** The image of K inside L. *)
Definition image_in_L (E : FieldExtension) : E.(ext_top) -> Prop :=
  fun y => exists x : E.(ext_base), E.(ext_emb).(rhom_map) x = y.

(** ** Subfield predicate *)

(** A subset S ⊆ L is a subfield (containing the image of K) if it is closed
    under the field operations. *)

Record IsSubfieldOf {L : Type} (fL : Field L) (S : L -> Prop) : Prop := {
  sf_zero : S fL.(fld_ring).(cr_zero);
  sf_one  : S fL.(fld_ring).(cr_one);
  sf_add  : forall a b, S a -> S b -> S (fL.(fld_ring).(cr_add) a b);
  sf_neg  : forall a,   S a -> S (fL.(fld_ring).(cr_neg) a);
  sf_mul  : forall a b, S a -> S b -> S (fL.(fld_ring).(cr_mul) a b);
  sf_inv  : forall a,   S a -> a <> fL.(fld_ring).(cr_zero) ->
                        S (fL.(fld_inv) a);
}.

(** ** Intermediate field *)

(** An intermediate field for an extension K ↪ L is a subset F ⊆ L that:
    1. Is a subfield of L.
    2. Contains the image of K. *)

Record IntermField (E : FieldExtension) : Type := {
  if_pred   : E.(ext_top) -> Prop;
  if_sub    : IsSubfieldOf E.(ext_fL) if_pred;
  if_contains_K : forall k : E.(ext_base),
                    if_pred (E.(ext_emb).(rhom_map) k);
}.

Arguments if_pred        {E}.
Arguments if_sub         {E}.
Arguments if_contains_K  {E}.

(** The whole field L is an intermediate field. *)
Definition interm_top (E : FieldExtension) : IntermField E.
Proof.
  refine {|
    if_pred := fun _ => True;
    if_sub  := _;
    if_contains_K := _;
  |}.
  - constructor; intros; exact I.
  - intros. exact I.
Defined.

(** The image of K in L is a subfield: closure under inv is admitted
    (requires showing ι(k)^{-1} = ι(k^{-1}), which holds by field_hom_injective). *)
Lemma image_K_is_subfield (E : FieldExtension) :
    IsSubfieldOf E.(ext_fL) (image_in_L E).
Proof.
  constructor.
  - exists E.(ext_fK).(fld_ring).(cr_zero). apply rhom_zero.
  - exists E.(ext_fK).(fld_ring).(cr_one). apply (rhom_one E.(ext_emb)).
  - intros a b [ka Hka] [kb Hkb].
    exists (E.(ext_fK).(fld_ring).(cr_add) ka kb).
    rewrite (rhom_add E.(ext_emb)). rewrite Hka, Hkb. reflexivity.
  - intros a [ka Hka].
    exists (E.(ext_fK).(fld_ring).(cr_neg) ka).
    rewrite (rhom_neg E.(ext_emb)). rewrite Hka. reflexivity.
  - intros a b [ka Hka] [kb Hkb].
    exists (E.(ext_fK).(fld_ring).(cr_mul) ka kb).
    rewrite (rhom_mul E.(ext_emb)). rewrite Hka, Hkb. reflexivity.
  - (* ι(k)^{-1} = ι(k^{-1}): field homs preserve inverses *)
    intros a [k Hka] Hne.
    assert (Hk_ne : k <> E.(ext_fK).(fld_ring).(cr_zero)).
    { intro Hk. apply Hne. rewrite <- Hka, Hk. apply rhom_zero. }
    exists (E.(ext_fK).(fld_inv) k).
    (* Use fL directly via :> coercion from Field to CommRing *)
    (* a * ι(k^{-1}) = ι(k) * ι(k^{-1}) = ι(k * k^{-1}) = ι(1) = 1 *)
    assert (Hmul : E.(ext_fL).(cr_mul) a (E.(ext_emb).(rhom_map) (E.(ext_fK).(fld_inv) k))
                   = E.(ext_fL).(cr_one)).
    { rewrite <- Hka.
      rewrite <- (E.(ext_emb).(rhom_mul) k (E.(ext_fK).(fld_inv) k)).
      rewrite (E.(ext_fK).(fld_inv_mul) k Hk_ne).
      apply E.(ext_emb).(rhom_one). }
    (* ι(k^{-1}) = fld_inv a via: fld_inv a * (a * ι(k^{-1})) = fld_inv a * 1 = fld_inv a *)
    set (inv_a := E.(ext_fL).(fld_inv) a).
    assert (LHS : E.(ext_fL).(cr_mul) inv_a (E.(ext_fL).(cr_mul) a (E.(ext_emb).(rhom_map) (E.(ext_fK).(fld_inv) k)))
                  = E.(ext_emb).(rhom_map) (E.(ext_fK).(fld_inv) k)).
    { rewrite E.(ext_fL).(cr_mul_assoc).
      assert (Hinva : E.(ext_fL).(cr_mul) inv_a a = E.(ext_fL).(cr_one)).
      { unfold inv_a. rewrite E.(ext_fL).(cr_mul_comm).
        exact (E.(ext_fL).(fld_inv_mul) a Hne). }
      rewrite Hinva. rewrite E.(ext_fL).(cr_mul_comm). apply E.(ext_fL).(cr_mul_one). }
    assert (RHS : E.(ext_fL).(cr_mul) inv_a (E.(ext_fL).(cr_mul) a (E.(ext_emb).(rhom_map) (E.(ext_fK).(fld_inv) k)))
                  = inv_a).
    { rewrite Hmul. apply E.(ext_fL).(cr_mul_one). }
    exact (eq_trans (eq_sym LHS) RHS).
Qed.

(** The base field K (image in L) is an intermediate field. *)
Definition interm_bot (E : FieldExtension) : IntermField E :=
  {| if_pred       := image_in_L E;
     if_sub        := image_K_is_subfield E;
     if_contains_K := fun k => ex_intro _ k eq_refl; |}.

(** ** Poset of intermediate fields *)

(** Intermediate fields are ordered by pointwise inclusion: F1 ≤ F2 iff
    every element of F1 (as a subset of L) lies in F2. *)

Definition IntermFieldPoset (E : FieldExtension) : Poset.
Proof.
  refine {|
    carrier    := IntermField E;
    le         := fun F1 F2 => forall x, F1.(if_pred) x -> F2.(if_pred) x;
    le_refl    := fun F x Hx => Hx;
    le_trans   := fun F1 F2 F3 h12 h23 x Hx => h23 x (h12 x Hx);
    le_antisym := _;
  |}.
  intros F1 F2 h12 h21.
  destruct F1 as [p1 s1 c1], F2 as [p2 s2 c2]. cbn in *.
  assert (Heq : p1 = p2).
  { apply functional_extensionality. intros x.
    apply propositional_extensionality. split; [apply h12 | apply h21]. }
  subst p2.
  f_equal; apply proof_irrelevance.
Defined.

Notation "'IntermPoset' E" := (IntermFieldPoset E) (at level 9) : order_scope.
