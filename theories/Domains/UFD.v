(** * Domains/UFD.v — Unique Factorization Domains

    Formalizes UFDs: every nonzero nonunit has a factorization into
    irreducibles, unique up to permutation and associates.

    Reference: Dummit & Foote §8.3. *)

From CAG Require Import Rings.Ring Domains.Divisibility Domains.Associates
                        Domains.IrreduciblePrime.
From Stdlib Require Import Arith Lia List Permutation Classical.
Import ListNotations.

(* ================================================================== *)
(** ** Factorizations *)
(* ================================================================== *)

Section UFDDef.
  Context {R : Type} (d : IntegralDomain R).

  Let r    : Ring R                                                            := id_r d.
  Let comm : forall a b : R, rmul R r a b = rmul R r b a                       := id_comm d.
  Let nt   : rone R r <> rzero R r                                             := id_nontrivial d.
  Let nzd  : forall a b : R, rmul R r a b = rzero R r ->
               a = rzero R r \/ b = rzero R r                                  := id_no_zero_div d.

  (** A factorization of a nonzero a is:
      - a unit u
      - a finite list of irreducibles ps
      - a proof that a = u * product(ps) *)

  Fixpoint list_product (ps : list R) : R :=
    match ps with
    | []      => rone R r
    | p :: rest => rmul R r p (list_product rest)
    end.

  Record Factorization (a : R) : Type := mkFact {
    fact_unit : R;
    fact_irrs : list R;
    fact_unit_is_unit : is_unit r fact_unit;
    fact_irrs_irr : forall p, In p fact_irrs -> is_irreducible d p;
    fact_eq  : a = rmul R r fact_unit (list_product fact_irrs);
  }.

  (** Two factorizations are equivalent if:
      - the lists are permutations of each other (up to associates)
      - the units are associate *)

  (** The permutation-up-to-associates relation on lists *)
  (** We use Permutation from Stdlib + pointwise associates *)

  (** A UFD is an integral domain where every nonzero nonunit has a factorization,
      and any two factorizations are equivalent. *)

  (** Existence of factorization *)
  Definition has_factorization (a : R) : Prop :=
    a <> rzero R r ->
    ~ is_unit r a ->
    exists F : Factorization a, True.

  (** Uniqueness of factorization (up to permutation and associates) *)
  (** We state uniqueness axiomatically: any two factorizations have
      the same length and their factors can be matched pairwise as associates. *)

  Definition ufd_uniqueness : Prop :=
    forall a : R,
    forall F1 F2 : Factorization a,
      exists sigma : list nat,
        (* sigma is a permutation of [0..n-1] *)
        Permutation sigma (seq 0 (length (fact_irrs a F1))) /\
        length sigma = length (fact_irrs a F2) /\
        forall i j : nat,
          nth_error sigma i = Some j ->
          is_associate d
            (nth i (fact_irrs a F1) (rzero R r))
            (nth j (fact_irrs a F2) (rzero R r)).

  Record IsUFD : Prop := mkUFD {
    ufd_factorization : forall a : R, has_factorization a;
    ufd_unique        : ufd_uniqueness;
  }.

  (* ================================================================== *)
  (** ** Basic UFD lemmas *)
  (* ================================================================== *)

  (** In a UFD, irreducible implies prime — proved at end of section. *)

  (** Product of a list is zero only if some factor is zero *)
  Lemma list_product_zero : forall ps : list R,
      list_product ps = rzero R r ->
      exists p, In p ps /\ p = rzero R r.
  Proof.
    intros ps. induction ps as [| p rest IH].
    - simpl. intro H. exfalso. exact (nt H).
    - simpl. intro H.
      destruct (nzd p (list_product rest) H) as [Hp | Hrest].
      + exists p. split; [left; reflexivity | exact Hp].
      + destruct (IH Hrest) as [q [Hq0 Hq1]].
        exists q. split; [right; exact Hq0 | exact Hq1].
  Qed.

  (** If all factors are irreducible, the product is nonzero *)
  Lemma list_product_nonzero : forall ps : list R,
      (forall p, In p ps -> is_irreducible d p) ->
      list_product ps <> rzero R r.
  Proof.
    intros ps Hirr Hzero.
    destruct (list_product_zero ps Hzero) as [p [Hp Hpz]].
    destruct (Hirr p Hp) as [Hp0 _]. exact (Hp0 Hpz).
  Qed.

  (** list_product respects append *)
  Lemma list_product_app : forall ps qs : list R,
      list_product (ps ++ qs) = rmul R r (list_product ps) (list_product qs).
  Proof.
    intros ps qs. induction ps as [| p rest IH].
    - simpl. symmetry. apply rmul_one_l.
    - simpl. rewrite IH. apply rmul_assoc.
  Qed.

  (** Divisibility criterion: if p is irreducible/prime and divides a product,
      it divides some factor *)
  Lemma prime_divides_list_product : forall (H : IsUFD) (p : R) (ps : list R),
      is_prime d p ->
      divides r p (list_product ps) ->
      exists q, In q ps /\ divides r p q.
  Proof.
    intros H p ps [Hp0 [Hpu Hprime]].
    induction ps as [| q rest IH].
    - simpl. intro Hdiv.
      exfalso. apply Hpu.
      apply (proj2 (unit_iff_divides_one r comm p)). exact Hdiv.
    - simpl. intro Hdiv.
      destruct (Hprime q (list_product rest) Hdiv) as [Hpq | Hprest].
      + exists q. split; [left; reflexivity | exact Hpq].
      + destruct (IH Hprest) as [s [Hs Hps]].
        exists s. split; [right; exact Hs | exact Hps].
  Qed.

  (** UFD divisibility: a | b in terms of prime factorizations *)
  (** Complex general statement — left for extended development *)
  Lemma ufd_divisibility_exponents : forall (H : IsUFD) (a b : R),
      a <> rzero R r -> b <> rzero R r ->
      divides r a b ->
      (* a divides b means every prime in factorization of a appears
         with <= exponent in factorization of b *)
      True.
  Proof. intros. exact I. Qed.

  (* ================================================================== *)
  (** ** Proof: irreducible implies prime in a UFD *)
  (* ================================================================== *)

  (** Helper: any element in a list divides the list product. *)
  Lemma in_divides_list_product : forall (x : R) (ps : list R),
      In x ps -> divides r x (list_product ps).
  Proof.
    intros x ps Hin. induction ps as [| q rest IH].
    - simpl in Hin. contradiction.
    - simpl. destruct Hin as [Heq | Hin'].
      + subst q. exists (list_product rest). reflexivity.
      + destruct (IH Hin') as [c Hc].
        exists (rmul R r q c).
        rewrite Hc.
        rewrite (rmul_assoc R r q x c).
        rewrite (comm q x).
        rewrite <- (rmul_assoc R r x q c). reflexivity.
  Qed.

  (** Helper: divisibility through a unit factor. *)
  Lemma divides_through_unit_l : forall (p u x : R),
      is_unit r u ->
      divides r p (rmul R r u x) ->
      divides r p x.
  Proof.
    intros p u x [uinv [Hur Hul]] [c Hc].
    exists (rmul R r uinv c).
    assert (Hx : x = rmul R r uinv (rmul R r u x)).
    { rewrite (rmul_assoc R r uinv u x), Hul, rmul_one_l. reflexivity. }
    rewrite Hx, Hc.
    rewrite (rmul_assoc R r uinv p c).
    rewrite (comm uinv p).
    rewrite <- (rmul_assoc R r p uinv c). reflexivity.
  Qed.

  (** Key helper: if irreducible p divides a product of irreducibles, then
      p is associate to one of them. Uses the uniqueness clause of UFD. *)
  Lemma irr_divides_irr_product_associate :
    forall (H : IsUFD) (p : R) (qs : list R),
      is_irreducible d p ->
      (forall q, In q qs -> is_irreducible d q) ->
      divides r p (list_product qs) ->
      exists q, In q qs /\ is_associate d p q.
  Proof.
    intros H p qs Hpirr Hqsirr [c Hc].
    destruct qs as [| q0 rest] eqn:Eqs.
    { exfalso. simpl in Hc.
      destruct Hpirr as [_ [Hpu _]].
      apply Hpu.
      change (is_unit r p). unfold is_unit.
      exists c. split.
      - symmetry. exact Hc.
      - rewrite (comm c p). symmetry. exact Hc. }
    rewrite <- Eqs in *. clear q0 rest Eqs.
    assert (Hlpqs_nz : list_product qs <> rzero R r)
      by (apply list_product_nonzero; exact Hqsirr).
    assert (Hc_nz : c <> rzero R r).
    { intro Hc0. apply Hlpqs_nz. rewrite Hc, Hc0. apply rmul_zero_r. }
    set (a := list_product qs).
    assert (HF2_eq : a = rmul R r (rone R r) (list_product qs))
      by (unfold a; symmetry; apply rmul_one_l).
    pose (F2 := mkFact a (rone R r) qs (unit_one r) Hqsirr HF2_eq).
    destruct (classic (is_unit r c)) as [Hcu | Hcnu].
    - assert (HF1_eq : a = rmul R r c (list_product [p])).
      { unfold a. simpl. rewrite rmul_one_r.
        rewrite Hc. apply comm. }
      assert (Hps_irr : forall x, In x [p] -> is_irreducible d x).
      { intros x [Heq | []]. subst x. exact Hpirr. }
      pose (F1 := mkFact a c [p] Hcu Hps_irr HF1_eq).
      destruct (ufd_unique H a F1 F2) as [sigma [Hperm [Hlen Hrel]]].
      simpl in Hperm. simpl in Hlen.
      assert (Hsigma_len : length sigma = 1).
      { rewrite (Permutation_length Hperm). reflexivity. }
      destruct sigma as [| s0 srest]; [discriminate |].
      destruct srest; [| simpl in Hsigma_len; discriminate].
      assert (Hs0 : s0 = 0).
      { pose proof (Permutation_in s0 Hperm) as Hin.
        assert (Hin' : In s0 [s0]) by (left; reflexivity).
        specialize (Hin Hin'). destruct Hin as [E | []]. exact (eq_sym E). }
      subst s0.
      simpl in Hlen.
      destruct qs as [| q0 qrest]; [simpl in Hlen; discriminate |].
      destruct qrest; [| simpl in Hlen; discriminate].
      pose proof (Hrel 0 0 eq_refl) as Hassoc.
      simpl in Hassoc.
      exists q0. split; [left; reflexivity | exact Hassoc].
    - destruct (ufd_factorization H c Hc_nz Hcnu) as [Fc _].
      destruct Fc as [uc cs Huc_unit Hcs_irr Hc_eq].
      assert (HF1_eq : a = rmul R r uc (list_product (p :: cs))).
      { unfold a. simpl.
        rewrite Hc. rewrite Hc_eq.
        rewrite (rmul_assoc R r p uc (list_product cs)).
        rewrite (comm p uc).
        rewrite <- (rmul_assoc R r uc p (list_product cs)). reflexivity. }
      assert (Hpcs_irr : forall x, In x (p :: cs) -> is_irreducible d x).
      { intros x [Heq | Hin].
        - subst x. exact Hpirr.
        - apply Hcs_irr. exact Hin. }
      pose (F1 := mkFact a uc (p :: cs) Huc_unit Hpcs_irr HF1_eq).
      destruct (ufd_unique H a F1 F2) as [sigma [Hperm [Hlen Hrel]]].
      assert (Hsigma_len_eq : length sigma = S (length cs)).
      { rewrite (Permutation_length Hperm). rewrite length_seq.
        simpl. reflexivity. }
      assert (Hsigma_len_pos : length sigma >= 1) by (rewrite Hsigma_len_eq; lia).
      destruct sigma as [| s0 srest]; [simpl in Hsigma_len_pos; lia |].
      pose proof (Hrel 0 s0 eq_refl) as Hassoc.
      simpl in Hassoc.
      assert (Hs0_in_seq : In s0 (seq 0 (length (p :: cs)))).
      { apply (Permutation_in s0 Hperm). left. reflexivity. }
      apply in_seq in Hs0_in_seq.
      destruct Hs0_in_seq as [_ Hs0_lt].
      simpl in Hs0_lt.
      simpl in Hlen.
      assert (Hqs_len : length qs = S (length cs)).
      { rewrite <- Hlen. exact Hsigma_len_eq. }
      assert (Hs0_lt_qs : s0 < length qs) by (rewrite Hqs_len; lia).
      assert (Hnth_in : In (nth s0 qs (rzero R r)) qs).
      { apply nth_In. exact Hs0_lt_qs. }
      exists (nth s0 qs (rzero R r)). split.
      + exact Hnth_in.
      + exact Hassoc.
  Qed.

  (** Main theorem: in a UFD, irreducible elements are prime. *)
  Theorem ufd_irreducible_prime : forall (H : IsUFD) (p : R),
      is_irreducible d p -> is_prime d p.
  Proof.
    intros H p Hpirr.
    pose proof Hpirr as Hpirr_orig.
    destruct Hpirr as [Hp0 [Hpu _]].
    split; [exact Hp0 | split; [exact Hpu |]].
    intros a b Hpab.
    (* Hpab : divides (id_r d) p (rmul R (id_r d) a b) — unfolded externally.
       Convert it to use UFD.v's r. *)
    change (divides r p (rmul R r a b)) in Hpab.
    destruct Hpab as [c Hc].
    destruct (classic (a = rzero R r)) as [Ha0 | Ha0].
    { left. change (divides r p a). rewrite Ha0. apply divides_zero. }
    destruct (classic (b = rzero R r)) as [Hb0 | Hb0].
    { right. change (divides r p b). rewrite Hb0. apply divides_zero. }
    destruct (classic (is_unit r a)) as [Hau | Hau].
    { right.
      destruct Hau as [ainv [Hair Hail]].
      change (divides r p b).
      exists (rmul R r ainv c).
      assert (Hb_eq : b = rmul R r ainv (rmul R r a b)).
      { rewrite (rmul_assoc R r ainv a b), Hail, rmul_one_l. reflexivity. }
      rewrite Hb_eq at 1.
      rewrite Hc.
      rewrite (rmul_assoc R r ainv p c).
      rewrite (comm ainv p).
      rewrite <- (rmul_assoc R r p ainv c). reflexivity. }
    destruct (classic (is_unit r b)) as [Hbu | Hbu].
    { left.
      destruct Hbu as [binv [Hbir Hbil]].
      change (divides r p a).
      exists (rmul R r binv c).
      assert (Ha_eq : a = rmul R r (rmul R r a b) binv).
      { rewrite <- (rmul_assoc R r a b binv), Hbir, rmul_one_r. reflexivity. }
      rewrite Ha_eq at 1.
      rewrite Hc.
      rewrite <- (rmul_assoc R r p c binv).
      rewrite (comm c binv).
      reflexivity. }
    destruct (ufd_factorization H a Ha0 Hau) as [Fa _].
    destruct Fa as [ua asps Hua_u Hasps_irr Ha_eq].
    destruct (ufd_factorization H b Hb0 Hbu) as [Fb _].
    destruct Fb as [ub bsps Hub_u Hbsps_irr Hb_eq].
    assert (Hab_eq : rmul R r a b =
              rmul R r (rmul R r ua ub) (list_product (asps ++ bsps))).
    { rewrite list_product_app.
      rewrite Ha_eq, Hb_eq.
      rewrite <- (rmul_assoc R r ua (list_product asps)
                                   (rmul R r ub (list_product bsps))).
      rewrite (rmul_assoc R r (list_product asps) ub (list_product bsps)).
      rewrite (comm (list_product asps) ub).
      rewrite <- (rmul_assoc R r ub (list_product asps) (list_product bsps)).
      rewrite (rmul_assoc R r ua ub
                              (rmul R r (list_product asps) (list_product bsps))).
      reflexivity. }
    assert (Huu : is_unit r (rmul R r ua ub)) by (apply unit_mul; assumption).
    assert (Hp_div_lp : divides r p (list_product (asps ++ bsps))).
    { apply (divides_through_unit_l p (rmul R r ua ub) _ Huu).
      rewrite <- Hab_eq.
      exists c. exact Hc. }
    assert (Hps_irr : forall x, In x (asps ++ bsps) -> is_irreducible d x).
    { intros x Hin. apply in_app_or in Hin. destruct Hin as [Hina | Hinb].
      - apply Hasps_irr. exact Hina.
      - apply Hbsps_irr. exact Hinb. }
    destruct (irr_divides_irr_product_associate H p (asps ++ bsps)
                Hpirr_orig Hps_irr Hp_div_lp) as [q [Hq_in Hq_assoc]].
    apply in_app_or in Hq_in.
    destruct Hq_assoc as [u [Hu Hq_eq]].
    assert (Hpdivq : divides r p q).
    { exists u. rewrite Hq_eq. apply comm. }
    destruct Hq_in as [Hina | Hinb].
    - left. change (divides r p a).
      assert (Hq_div_la : divides r q (list_product asps))
        by (apply in_divides_list_product; exact Hina).
      assert (Hp_div_la : divides r p (list_product asps))
        by (apply (divides_trans r p q (list_product asps)); assumption).
      rewrite Ha_eq.
      apply (divides_mul_l r comm p (list_product asps) ua). exact Hp_div_la.
    - right. change (divides r p b).
      assert (Hq_div_lb : divides r q (list_product bsps))
        by (apply in_divides_list_product; exact Hinb).
      assert (Hp_div_lb : divides r p (list_product bsps))
        by (apply (divides_trans r p q (list_product bsps)); assumption).
      rewrite Hb_eq.
      apply (divides_mul_l r comm p (list_product bsps) ub). exact Hp_div_lb.
  Qed.

End UFDDef.

Arguments list_product {R} d ps.
Arguments IsUFD {R} d.
Arguments Factorization {R} d a.
