(** * Domains/GCD_LCM.v — GCDs and LCMs in integral domains

    Formalizes greatest common divisors and least common multiples.

    Reference: Dummit & Foote §8.3. *)

From CAG Require Import Rings.Ring Domains.Divisibility Domains.Associates
                        Domains.IrreduciblePrime Domains.UFD.
From Stdlib Require Import Arith Lia List Classical.
Import ListNotations.

(* ================================================================== *)
(** ** Greatest common divisors *)
(* ================================================================== *)

Section GCD.
  Context {R : Type} (d : IntegralDomain R).

  Let r : Ring R := id_r d.
  Let comm : forall a b : R, rmul R r a b = rmul R r b a := id_comm d.

  (** d is a gcd of a and b if:
      - d | a
      - d | b
      - for any c, c | a and c | b implies c | d *)
  Definition is_gcd (g a b : R) : Prop :=
    divides r g a /\
    divides r g b /\
    forall c : R, divides r c a -> divides r c b -> divides r c g.

  (** lcm of a and b: l is an lcm if:
      - a | l
      - b | l
      - for any c, a | c and b | c implies l | c *)
  Definition is_lcm (l a b : R) : Prop :=
    divides r a l /\
    divides r b l /\
    forall c : R, divides r a c -> divides r b c -> divides r l c.

  (** GCD is unique up to associates *)
  Lemma gcd_unique_up_to_associate : forall g1 g2 a b : R,
      is_gcd g1 a b -> is_gcd g2 a b ->
      is_associate d g1 g2.
  Proof.
    intros g1 g2 a b [Hg1a [Hg1b Hg1min]] [Hg2a [Hg2b Hg2min]].
    pose proof (Hg1min g2 Hg2a Hg2b) as Hg1g2.
    pose proof (Hg2min g1 Hg1a Hg1b) as Hg2g1.
    destruct (classic (g1 = rzero R r)) as [Hg10 | Hg10].
    - rewrite Hg10 in Hg2g1.
      pose proof (zero_divides r g2 Hg2g1) as Hg20.
      rewrite Hg10, Hg20. apply associate_refl.
    - apply (associated_iff_mutual_divides d g1 g2 Hg10).
      split; [exact Hg2g1 | exact Hg1g2].
  Qed.

  (** LCM is unique up to associates *)
  Lemma lcm_unique_up_to_associate : forall l1 l2 a b : R,
      is_lcm l1 a b -> is_lcm l2 a b ->
      is_associate d l1 l2.
  Proof.
    intros l1 l2 a b [Hal1 [Hbl1 Hl1min]] [Hal2 [Hbl2 Hl2min]].
    pose proof (Hl2min l1 Hal1 Hbl1) as Hl1l2.
    pose proof (Hl1min l2 Hal2 Hbl2) as Hl2l1.
    destruct (classic (l1 = rzero R r)) as [Hl10 | Hl10].
    - rewrite Hl10 in Hl2l1.
      pose proof (zero_divides r l2 Hl2l1) as Hl20.
      rewrite Hl10, Hl20. apply associate_refl.
    - apply (associated_iff_mutual_divides d l1 l2 Hl10).
      split; [exact Hl2l1 | exact Hl1l2].
  Qed.

  (** gcd(a, 0) = a (up to associates) *)
  Lemma gcd_zero_r : forall a : R, is_gcd a a (rzero R r).
  Proof.
    intro a. unfold is_gcd. split; [| split].
    - apply divides_refl.
    - apply divides_zero.
    - intros c Hca _. exact Hca.
  Qed.

  (** gcd(0, b) = b *)
  Lemma gcd_zero_l : forall b : R, is_gcd b (rzero R r) b.
  Proof.
    intro b. unfold is_gcd. split; [| split].
    - apply divides_zero.
    - apply divides_refl.
    - intros c _ Hcb. exact Hcb.
  Qed.

  (** gcd of units: gcd(u, b) = 1 when u is a unit *)
  Lemma gcd_unit_l : forall u b : R,
      is_unit r u ->
      is_gcd (rone R r) u b.
  Proof.
    intros u b Hu. unfold is_gcd. split; [| split].
    - apply unit_divides_all. exact (unit_one r).
    - apply unit_divides_all. exact (unit_one r).
    - intros c Hcu _.
      apply (divides_trans r c u (rone R r) Hcu).
      apply (proj1 (unit_iff_divides_one r comm u)). exact Hu.
  Qed.

  (** lcm(a, 0) = 0 *)
  Lemma lcm_zero_r : forall a : R, is_lcm (rzero R r) a (rzero R r).
  Proof.
    intro a. unfold is_lcm. split; [| split].
    - apply divides_zero.
    - apply divides_refl.
    - intros c _ Hc0. exact Hc0.
  Qed.

  (** UFD: GCD exists from factorizations *)
  (** The general proof proceeds by strong induction on the length of
      a's factorization, using uniqueness of factorization. *)

  (** Helper: in the irreducible factor list of a, classically decide
      whether some factor divides b. *)
  Lemma irr_list_div_dec : forall (ps : list R) (b : R),
      (exists p, In p ps /\ divides r p b) \/
      (forall p, In p ps -> ~ divides r p b).
  Proof.
    intros ps b. induction ps as [| q rest IH].
    - right. intros p [].
    - destruct (classic (divides r q b)) as [Hqb | Hqb].
      + left. exists q. split; [left; reflexivity | exact Hqb].
      + destruct IH as [[p [Hp Hpb]] | Hno].
        * left. exists p. split; [right; exact Hp | exact Hpb].
        * right. intros p [Heq | Hin].
          { subst p. exact Hqb. }
          { apply Hno. exact Hin. }
  Qed.

  (** Helper: if p is in the irreducible list of a's factorization
      [a = u * p_1 * ... * p_n], then we can extract [a = p * a'] with
      a' = u * (product of the other irreducibles), nonzero, with a
      strictly shorter factorization. *)
  Lemma extract_irr_from_factorization :
      forall (H : IsUFD d) (a : R) (Fa : Factorization d a) (p : R),
      a <> rzero R r ->
      In p (fact_irrs d a Fa) ->
      exists a' : R,
        a = rmul R r p a' /\
        a' <> rzero R r /\
        exists Fa' : Factorization d a',
          length (fact_irrs d a' Fa') < length (fact_irrs d a Fa).
  Proof.
    intros H a Fa p Ha Hin.
    destruct Fa as [u ps Hu Hps_irr Ha_eq]. simpl in Hin.
    (* Split ps at p: ps = pre ++ p :: post. *)
    apply in_split in Hin.
    destruct Hin as [pre [post Hps_eq]].
    (* a' = u * (product of pre ++ post) *)
    set (a' := rmul R r u (list_product d (pre ++ post))).
    (* Build factorization Fa' of a'. *)
    assert (Hpp_irr : forall q, In q (pre ++ post) -> is_irreducible d q).
    { intros q Hq. apply Hps_irr. rewrite Hps_eq.
      apply in_or_app. apply in_app_or in Hq. destruct Hq as [Hq | Hq].
      - left. exact Hq.
      - right. right. exact Hq. }
    assert (Ha'_eq : a' = rmul R r u (list_product d (pre ++ post))) by reflexivity.
    pose (Fa' := mkFact d a' u (pre ++ post) Hu Hpp_irr Ha'_eq).
    (* Verify a = p * a'. *)
    assert (Ha_pa' : a = rmul R r p a').
    { unfold a'.
      (* a = u * lp(pre ++ p :: post) = u * (lp pre * (p * lp post)) *)
      transitivity (rmul R r u (rmul R r (list_product d pre)
                                  (rmul R r p (list_product d post)))).
      { rewrite Ha_eq, Hps_eq, (list_product_app d pre (p :: post)).
        simpl. reflexivity. }
      (* RHS = p * (u * (lp pre * lp post))
            = p * (u * lp(pre ++ post))         [list_product_app]
         Strategy: shuffle u, lp pre, p, lp post. *)
      (* Step: u * (lp pre * (p * lp post))
             = u * ((lp pre * p) * lp post)     [assoc]
             = u * ((p * lp pre) * lp post)     [comm]
             = u * (p * (lp pre * lp post))     [assoc back]
             = (u * p) * (lp pre * lp post)     [assoc]
             = (p * u) * (lp pre * lp post)     [comm]
             = p * (u * (lp pre * lp post))     [assoc back] *)
      transitivity (rmul R r u (rmul R r (rmul R r (list_product d pre) p)
                                  (list_product d post))).
      { f_equal. apply rmul_assoc. }
      transitivity (rmul R r u (rmul R r (rmul R r p (list_product d pre))
                                  (list_product d post))).
      { f_equal. f_equal. apply comm. }
      transitivity (rmul R r u (rmul R r p
                                  (rmul R r (list_product d pre) (list_product d post)))).
      { f_equal. symmetry. apply rmul_assoc. }
      transitivity (rmul R r (rmul R r u p)
                              (rmul R r (list_product d pre) (list_product d post))).
      { apply rmul_assoc. }
      transitivity (rmul R r (rmul R r p u)
                              (rmul R r (list_product d pre) (list_product d post))).
      { rewrite (comm u p). reflexivity. }
      transitivity (rmul R r p
                              (rmul R r u (rmul R r (list_product d pre) (list_product d post)))).
      { symmetry. apply rmul_assoc. }
      f_equal. f_equal. symmetry. apply (list_product_app d pre post). }
    (* Verify a' ≠ 0. *)
    assert (Ha'_ne : a' <> rzero R r).
    { intro Ha'0. apply Ha. rewrite Ha_pa', Ha'0. apply rmul_zero_r. }
    exists a'. split; [exact Ha_pa' | split; [exact Ha'_ne |]].
    exists Fa'.
    (* Goal: length (fact_irrs d a' Fa') < length ps  (after destruct Fa) *)
    simpl.
    rewrite Hps_eq.
    repeat rewrite length_app.
    simpl.
    lia.
  Qed.

  (** Main lemma: GCD exists, by strong induction on factorization length of a. *)
  Lemma ufd_gcd_exists_aux : forall (H : IsUFD d) (n : nat),
      forall a b : R,
        a <> rzero R r -> b <> rzero R r ->
        (exists Fa : Factorization d a, length (fact_irrs d a Fa) <= n) ->
        exists g : R, is_gcd g a b.
  Proof.
    intros H. induction n as [| n IHn].
    - (* Base: a's factorization has length 0, so a is a unit. *)
      intros a b Ha Hb [Fa Hlen].
      destruct Fa as [u ps Hu Hps_irr Ha_eq]. simpl in Hlen.
      assert (Hps_nil : ps = []).
      { destruct ps; [reflexivity | simpl in Hlen; lia]. }
      subst ps. simpl in Ha_eq.
      assert (Ha_unit : is_unit r a).
      { rewrite Ha_eq, rmul_one_r. exact Hu. }
      (* gcd = a. *)
      exists a. split; [| split].
      + apply divides_refl.
      + apply unit_divides_all. exact Ha_unit.
      + intros c Hca _. exact Hca.
    - (* Inductive step. *)
      intros a b Ha Hb [Fa Hlen].
      destruct (Nat.eq_dec (length (fact_irrs d a Fa)) 0) as [Hlen0 | Hlenpos].
      { (* a is a unit, same as base. *)
        destruct Fa as [u ps Hu Hps_irr Ha_eq]. simpl in Hlen0.
        assert (Hps_nil : ps = []).
        { destruct ps; [reflexivity | simpl in Hlen0; discriminate]. }
        subst ps. simpl in Ha_eq.
        assert (Ha_unit : is_unit r a).
        { rewrite Ha_eq, rmul_one_r. exact Hu. }
        exists a. split; [| split].
        + apply divides_refl.
        + apply unit_divides_all. exact Ha_unit.
        + intros c Hca _. exact Hca. }
      (* length ≥ 1. EM-split: some factor of a divides b? *)
      destruct (irr_list_div_dec (fact_irrs d a Fa) b) as [[p [Hp_in Hp_div_b]] | Hno].
      + (* Some p in factorization of a divides b. Extract a = p * a'. *)
        destruct (extract_irr_from_factorization H a Fa p Ha Hp_in)
          as [a' [Ha_pa' [Ha'_ne [Fa' Hlen']]]].
        (* Extract b = p * b'. *)
        destruct Hp_div_b as [b' Hb_pb'].
        assert (Hb'_ne : b' <> rzero R r).
        { intro Hb'0. apply Hb. rewrite Hb_pb', Hb'0. apply rmul_zero_r. }
        (* IH on (a', b'). *)
        assert (Hlen'_n : length (fact_irrs d a' Fa') <= n) by lia.
        destruct (IHn a' b' Ha'_ne Hb'_ne (ex_intro _ Fa' Hlen'_n))
          as [g' [Hg'a' [Hg'b' Hg'min]]].
        (* g = p * g'. *)
        exists (rmul R r p g'). split; [| split].
        * (* p * g' | a *)
          rewrite Ha_pa'.
          destruct Hg'a' as [x Hx].
          exists x. rewrite Hx.
          apply rmul_assoc.
        * (* p * g' | b *)
          rewrite Hb_pb'.
          destruct Hg'b' as [y Hy].
          exists y. rewrite Hy.
          apply rmul_assoc.
        * (* For any c | a, c | b: c | p * g'. *)
          intros c Hca Hcb.
          (* Need: p irreducible (so prime), and we need to show c | p*g'.
             Strategy: get p irreducible from factorization.
             Show p prime. Then... actually this is delicate. *)
          (* Actually the easier path: c | a = p*a' and c | b = p*b'.
             By the prime/irreducible properties, c divides p*gcd(a', b').
             Hmm, but we need a more careful argument. *)
          (* Let me try: g' is the gcd of a' and b'. We want p*g' to be the
             gcd of p*a' and p*b'. The standard fact: gcd(p*x, p*y) = p*gcd(x, y).
             To show c | p*g': consider c. By UFD, c has a factorization.
             Approach: use that p is prime in the UFD. *)
          (* Plan: split c by extracting how many times p divides c.
             More directly: claim c = p^k * c' with c' coprime to p. Then... *)
          (* This is the messy case. Use the prime property differently. *)
          assert (Hp_irr : is_irreducible d p).
          { destruct Fa as [u ps Hu Hps_irr Ha_eq]. simpl in Hp_in.
            apply Hps_irr. exact Hp_in. }
          assert (Hp_prime : is_prime d p).
          { apply ufd_irreducible_prime. exact H. exact Hp_irr. }
          (* p prime: p | c*x → p | c or p | x. *)
          (* Strategy: show that c = p * c'' or c is coprime to p,
             but it's easier to note: c | p*a', so by primeness:
                Either p | c (then c = p*c''),
                Or there's some structure we can exploit. *)
          (* Actually use: c | a = p*a'. Claim ∃ c'', c = p^k * c'' for max k.
             Equivalent: write c via factorization, extract powers of p. *)
          (* Cleaner approach: use the prime element extraction.
             Since p is prime and p | a*b is not what we have...
             We have c | p*a' and c | p*b'.

             Let me try: consider rmul R r p a' = a. Since c | a,
             write a = c * d. So p * a' = c * d. By prime p | c * d
             so p | c or p | d.
             - Case p | c: c = p * c1. Then c1 | a' (since p*c1 | p*a' so c1 | a' by cancel).
               Similarly c1 | b'. By IH-given gcd: c1 | g'. So c = p*c1 | p*g'.
             - Case p | d: d = p*d1. Then c * (p*d1) = p * a', so c*d1 = a' (cancel).
               So c | a'. Symmetrically check c | b'... hmm need to think.
               If p | d (where a = c*d), then a = c * p * d1.  And a = p*a',
               so p*a' = c*p*d1, cancel p: a' = c*d1. So c | a'.
               Now consider c | b = p*b'. Either p | c or p | (b's cofactor in terms of c).
               Hmm, this case-splits again.
               Actually if c | a' (from this case), and c | b. Then:
                 c | a' (just shown) and c | b. We want c | p*g'.
                 But we have IH on (a', b'). Wait, IH gives gcd(a', b') = g'.
                 We don't immediately get c | gcd(a', b)... only (a', b'). *)
          (* This is getting tangled. Let me try a completely different tactic
             for the minimality. *)
          (* Since c | p*a' and c | p*b', we want c | p*g'.
             Reduction: by prime p, every divisor c of p*x has the form
             p^k * c' where c' | x (after dividing out p's). *)
          (* Use the prime decomposition of c via extraction-of-p. *)
          (* CLAIM: Either p | c, or c | a' and c | b'. *)
          assert (Hsplit : divides r p c \/ (divides r c a' /\ divides r c b')).
          { destruct (classic (divides r p c)) as [Hpc | Hpc].
            - left. exact Hpc.
            - right.
              destruct Hca as [da Hda].
              destruct Hp_prime as [Hp0 [Hpu Hp_div]].
              assert (Hp_div_cd : divides r p (rmul R r c da)).
              { exists a'. rewrite <- Hda. exact Ha_pa'. }
              destruct (Hp_div c da Hp_div_cd) as [Hpc' | Hpd].
              { contradiction. }
              destruct Hpd as [k1 Hk1].
              change (id_r d) with r in Hk1.
              assert (Hcanc : a' = rmul R r c k1).
              { apply (mul_cancel_l r (id_no_zero_div d) p).
                - destruct Hp_irr as [Hp0' _]. exact Hp0'.
                - transitivity a; [symmetry; exact Ha_pa' | ].
                  transitivity (rmul R r c da); [exact Hda | ].
                  rewrite Hk1.
                  (* Goal: rmul c (rmul p k1) = rmul p (rmul c k1) *)
                  rewrite (rmul_assoc R r c p k1).
                  rewrite (comm c p).
                  rewrite <- (rmul_assoc R r p c k1).
                  reflexivity. }
              split.
              + exists k1. exact Hcanc.
              + destruct Hcb as [db Hdb].
                assert (Hp_div_cdb : divides r p (rmul R r c db)).
                { exists b'. rewrite <- Hdb. exact Hb_pb'. }
                destruct (Hp_div c db Hp_div_cdb) as [Hpc'' | Hpdb].
                { contradiction. }
                destruct Hpdb as [k2 Hk2].
                change (id_r d) with r in Hk2.
                assert (Hcanc2 : b' = rmul R r c k2).
                { apply (mul_cancel_l r (id_no_zero_div d) p).
                  - destruct Hp_irr as [Hp0' _]. exact Hp0'.
                  - transitivity b; [symmetry; exact Hb_pb' | ].
                    transitivity (rmul R r c db); [exact Hdb | ].
                    rewrite Hk2.
                    rewrite (rmul_assoc R r c p k2).
                    rewrite (comm c p).
                    rewrite <- (rmul_assoc R r p c k2).
                    reflexivity. }
                exists k2. exact Hcanc2. }
          destruct Hsplit as [Hpc | [Hca' Hcb']].
          -- (* p | c: c = p*c1; c1 | a' and c1 | b'; IH gives c1 | g'. *)
             destruct Hpc as [c1 Hc1].
             (* c | a means p*c1 | p*a'. Cancel p: c1 | a'. *)
             destruct Hca as [da Hda].
             rewrite Hc1 in Hda.
             rewrite Ha_pa' in Hda.
             (* Hda : p*a' = (p*c1)*da = p*(c1*da) by assoc. So a' = c1*da. *)
             assert (Ha'_eq : a' = rmul R r c1 da).
             { apply (mul_cancel_l r (id_no_zero_div d) p).
               - destruct Hp_irr as [Hp0' _]. exact Hp0'.
               - rewrite (rmul_assoc R r p c1 da). exact Hda. }
             assert (Hc1_a' : divides r c1 a') by (exists da; exact Ha'_eq).
             destruct Hcb as [db Hdb].
             rewrite Hc1 in Hdb.
             rewrite Hb_pb' in Hdb.
             assert (Hb'_eq : b' = rmul R r c1 db).
             { apply (mul_cancel_l r (id_no_zero_div d) p).
               - destruct Hp_irr as [Hp0' _]. exact Hp0'.
               - rewrite (rmul_assoc R r p c1 db). exact Hdb. }
             assert (Hc1_b' : divides r c1 b') by (exists db; exact Hb'_eq).
             pose proof (Hg'min c1 Hc1_a' Hc1_b') as Hc1_g'.
             destruct Hc1_g' as [e He].
             exists e. rewrite Hc1, He.
             (* Goal: rmul (rmul p c1) e = rmul p (rmul c1 e) *)
             rewrite <- (rmul_assoc R r p c1 e). reflexivity.
          -- (* c | a' and c | b': IH gives c | g', so c | p*g'. *)
             pose proof (Hg'min c Hca' Hcb') as Hc_g'.
             apply (divides_mul_l r comm). exact Hc_g'.
      + (* No factor of a divides b. Claim gcd = 1. *)
        exists (rone R r). split; [| split].
        * apply one_divides.
        * apply one_divides.
        * intros c Hca Hcb.
          (* Want: c | 1.  Equivalent to c being a unit. *)
          apply (proj1 (unit_iff_divides_one r comm c)).
          (* Show c is a unit. *)
          assert (Hc_ne : c <> rzero R r).
          { intro Hc0. apply Ha.
            destruct Hca as [x Hx]. rewrite Hx, Hc0. apply rmul_zero_l. }
          apply NNPP. intro Hc_nu.
          (* c is nonzero non-unit, so has a factorization with nonempty list. *)
          destruct (ufd_factorization d H c Hc_ne Hc_nu) as [Fc _].
          destruct Fc as [uc cs Huc Hcs_irr Hc_eq].
          destruct cs as [| q crest].
          { (* Empty list ⇒ c = uc, a unit. Contradiction. *)
            apply Hc_nu. simpl in Hc_eq. rewrite rmul_one_r in Hc_eq.
            rewrite Hc_eq. exact Huc. }
          (* Take q (the first irreducible in c's factorization). *)
          assert (Hq_irr : is_irreducible d q).
          { apply Hcs_irr. left. reflexivity. }
          (* q | c (since q is in c's factor list). *)
          assert (Hq_div_c : divides r q c).
          { rewrite Hc_eq.
            apply divides_mul_l. exact comm.
            simpl.
            exists (list_product d crest). reflexivity. }
          (* q | a (via c | a). *)
          assert (Hq_div_a : divides r q a)
            by (apply (divides_trans r q c a); assumption).
          (* q | b (via c | b). *)
          assert (Hq_div_b : divides r q b)
            by (apply (divides_trans r q c b); assumption).
          (* By irr_divides_irr_product_associate, q is associate to some
             p in a's factor list. *)
          destruct Fa as [ua aps Hua Haps_irr Ha_eq2]. simpl in *.
          assert (Hq_div_lp : divides r q (list_product d aps)).
          { apply (divides_through_unit_l d q ua _ Hua).
            rewrite <- Ha_eq2. exact Hq_div_a. }
          destruct (irr_divides_irr_product_associate d H q aps
                      Hq_irr Haps_irr Hq_div_lp) as [p [Hp_in Hp_assoc]].
          (* Hp_assoc : is_associate d q p.  q | b ⇒ p | b. *)
          assert (Hp_div_b : divides r p b).
          { apply (proj1 (associate_divides_iff d q p b Hp_assoc)). exact Hq_div_b. }
          exact (Hno p Hp_in Hp_div_b).
  Qed.

  Theorem ufd_gcd_exists : forall (H : IsUFD d) (a b : R),
      a <> rzero R r -> b <> rzero R r ->
      exists g : R, is_gcd g a b.
  Proof.
    intros H a b Ha Hb.
    (* Get a factorization of a (or recognize a as a unit). *)
    destruct (classic (is_unit r a)) as [Hau | Hau].
    - (* a is a unit: use empty factorization. *)
      pose (Fa := mkFact d a a [] Hau
                   (fun p (Hp : In p []) => match Hp with end)
                   (eq_sym (rmul_one_r R r a))).
      apply (ufd_gcd_exists_aux H 0 a b Ha Hb).
      exists Fa. simpl. lia.
    - destruct (ufd_factorization d H a Ha Hau) as [Fa _].
      apply (ufd_gcd_exists_aux H (length (fact_irrs d a Fa)) a b Ha Hb).
      exists Fa. lia.
  Qed.

  (** Euclid's lemma in a UFD: if gcd(a,b) = 1 and a | b*c, then a | c.
      Proved by strong induction on length of a's factorization, mirroring
      the gcd_exists proof. *)
  Lemma euclid_lemma_ufd_aux : forall (H : IsUFD d) (n : nat),
      forall a b c : R,
        a <> rzero R r ->
        is_gcd (rone R r) a b ->
        (exists Fa : Factorization d a, length (fact_irrs d a Fa) <= n) ->
        divides r a (rmul R r b c) ->
        divides r a c.
  Proof.
    intros H. induction n as [| n IHn].
    - (* Base: a is a unit. *)
      intros a b c Ha Hgcd [Fa Hlen] _.
      destruct Fa as [u ps Hu Hps_irr Ha_eq]. simpl in Hlen.
      assert (Hps_nil : ps = []).
      { destruct ps; [reflexivity | simpl in Hlen; lia]. }
      subst ps. simpl in Ha_eq.
      assert (Ha_unit : is_unit r a).
      { rewrite Ha_eq, rmul_one_r. exact Hu. }
      apply unit_divides_all. exact Ha_unit.
    - intros a b c Ha Hgcd [Fa Hlen] Habc.
      destruct (Nat.eq_dec (length (fact_irrs d a Fa)) 0) as [Hlen0 | Hlenpos].
      { destruct Fa as [u ps Hu Hps_irr Ha_eq]. simpl in Hlen0.
        assert (Hps_nil : ps = []).
        { destruct ps; [reflexivity | simpl in Hlen0; discriminate]. }
        subst ps. simpl in Ha_eq.
        assert (Ha_unit : is_unit r a).
        { rewrite Ha_eq, rmul_one_r. exact Hu. }
        apply unit_divides_all. exact Ha_unit. }
      (* Pick first irreducible p in factorization. *)
      assert (Hex_p : exists p, In p (fact_irrs d a Fa)).
      { destruct (fact_irrs d a Fa) as [| p0 rest0]; [simpl in Hlenpos; lia |].
        exists p0. left. reflexivity. }
      destruct Hex_p as [p Hp_in].
      assert (Hp_irr : is_irreducible d p).
      { apply (fact_irrs_irr d a Fa). exact Hp_in. }
      assert (Hp_prime : is_prime d p).
      { apply ufd_irreducible_prime. exact H. exact Hp_irr. }
      (* Extract a = p * a'. *)
      destruct (extract_irr_from_factorization H a Fa p Ha Hp_in)
        as [a' [Ha_pa' [Ha'_ne [Fa' Hlen']]]].
      (* p | a | b*c, so p | b*c. By primality, p | b or p | c. *)
      assert (Hp_div_a : divides r p a).
      { exists a'. rewrite Ha_pa'. reflexivity. }
      assert (Hp_div_bc : divides r p (rmul R r b c)).
      { apply (divides_trans r p a (rmul R r b c) Hp_div_a Habc). }
      destruct Hp_prime as [Hp0 [Hpu Hp_div_split]].
      destruct (Hp_div_split b c Hp_div_bc) as [Hp_div_b | Hp_div_c].
      + (* p | b: contradicts gcd(a, b) = 1 since p | a too. *)
        exfalso.
        destruct Hgcd as [_ [_ Hgcd_min]].
        assert (Hp_div_one : divides r p (rone R r)).
        { apply Hgcd_min. exact Hp_div_a. exact Hp_div_b. }
        apply Hpu. apply (proj2 (unit_iff_divides_one r comm p)). exact Hp_div_one.
      + (* p | c: c = p * c''. *)
        destruct Hp_div_c as [c'' Hc''].
        change (id_r d) with r in Hc''.
        (* Need a' | b*c'' (after cancelling p from a | b*(p*c'')). *)
        destruct Habc as [k Hk].
        (* Hk : b*c = a*k. Substitute a = p*a', c = p*c'':
               b*(p*c'') = (p*a')*k. We want to show: b*c'' = a'*?, i.e., a' | b*c''. *)
        assert (Hbc'' : rmul R r b c'' = rmul R r a' k).
        { apply (mul_cancel_l r (id_no_zero_div d) p).
          - exact Hp0.
          - (* p*(b*c'') = p*(a'*k) *)
            transitivity (rmul R r b (rmul R r p c'')).
            { rewrite (rmul_assoc R r p b c'').
              rewrite (comm p b).
              rewrite <- (rmul_assoc R r b p c''). reflexivity. }
            rewrite <- Hc''. rewrite Hk.
            rewrite Ha_pa'.
            rewrite <- (rmul_assoc R r p a' k). reflexivity. }
        (* Construct gcd(a', b) = 1. *)
        assert (Hgcd' : is_gcd (rone R r) a' b).
        { destruct Hgcd as [_ [Hone_b Hgcd_min]].
          split; [| split].
          - apply one_divides.
          - apply one_divides.
          - intros h Hha' Hhb.
            apply Hgcd_min; [| exact Hhb].
            apply (divides_trans r h a' a Hha').
            exists p. rewrite Ha_pa'. apply comm. }
        (* Apply IH: a' | c''. *)
        assert (Hlen'_n : length (fact_irrs d a' Fa') <= n) by lia.
        assert (Ha'_div_bc'' : divides r a' (rmul R r b c'')).
        { exists k. exact Hbc''. }
        pose proof (IHn a' b c'' Ha'_ne Hgcd' (ex_intro _ Fa' Hlen'_n) Ha'_div_bc'')
          as Ha'_div_c''.
        (* a = p*a', c = p*c'', a' | c'' ⟹ a | c. *)
        destruct Ha'_div_c'' as [k' Hk'].
        exists k'. rewrite Hc'', Ha_pa'. rewrite Hk'.
        rewrite <- (rmul_assoc R r p a' k'). reflexivity.
  Qed.

  Lemma euclid_lemma_ufd : forall (H : IsUFD d) (a b c : R),
      a <> rzero R r ->
      is_gcd (rone R r) a b ->
      divides r a (rmul R r b c) ->
      divides r a c.
  Proof.
    intros H a b c Ha Hgcd Habc.
    destruct (classic (is_unit r a)) as [Hau | Hau].
    - apply unit_divides_all. exact Hau.
    - destruct (ufd_factorization d H a Ha Hau) as [Fa _].
      apply (euclid_lemma_ufd_aux H (length (fact_irrs d a Fa)) a b c Ha Hgcd).
      + exists Fa. lia.
      + exact Habc.
  Qed.

  Theorem ufd_lcm_exists : forall (H : IsUFD d) (a b : R),
      a <> rzero R r -> b <> rzero R r ->
      exists l : R, is_lcm l a b.
  Proof.
    intros H a b Ha Hb.
    (* Get gcd g of (a, b). *)
    destruct (ufd_gcd_exists H a b Ha Hb) as [g [Hga [Hgb Hgmin]]].
    (* g <> 0 since g | a and a <> 0. *)
    assert (Hg_ne : g <> rzero R r).
    { intro Hg0. apply Ha. destruct Hga as [k Hk]. rewrite Hk, Hg0.
      apply rmul_zero_l. }
    (* Extract m, n: a = g*m, b = g*n. *)
    destruct Hga as [m Hm]. destruct Hgb as [n Hn].
    (* Define l := a*n = g*m*n = b*m. *)
    set (l := rmul R r a n).
    (* l = b*m, useful for showing b | l. *)
    assert (Hl_bm : l = rmul R r b m).
    { unfold l. rewrite Hm, Hn.
      (* (g*m)*n = (g*n)*m: both = g*m*n by assoc/comm. *)
      transitivity (rmul R r g (rmul R r m n)).
      { symmetry. apply rmul_assoc. }
      transitivity (rmul R r g (rmul R r n m)).
      { f_equal. apply comm. }
      apply rmul_assoc. }
    (* m, n nonzero (cofactors of nonzero by nonzero). *)
    assert (Hm_ne : m <> rzero R r).
    { intro Hm0. apply Ha. rewrite Hm, Hm0. apply rmul_zero_r. }
    assert (Hn_ne : n <> rzero R r).
    { intro Hn0. apply Hb. rewrite Hn, Hn0. apply rmul_zero_r. }
    (* Cofactor coprimality: gcd(m, n) = 1. *)
    assert (Hcop : is_gcd (rone R r) m n).
    { split; [| split].
      - apply one_divides.
      - apply one_divides.
      - intros h Hhm Hhn.
        (* g*h | a, g*h | b, so g*h | g. Hence h is a unit. *)
        assert (Hgh_a : divides r (rmul R r g h) a).
        { destruct Hhm as [m' Hm']. exists m'.
          rewrite Hm, Hm'.
          apply rmul_assoc. }
        assert (Hgh_b : divides r (rmul R r g h) b).
        { destruct Hhn as [n' Hn']. exists n'.
          rewrite Hn, Hn'.
          apply rmul_assoc. }
        pose proof (Hgmin (rmul R r g h) Hgh_a Hgh_b) as Hgh_g.
        (* g = (g*h)*k = g*(h*k) for some k. Cancel g: 1 = h*k. *)
        destruct Hgh_g as [k Hk].
        assert (Hhk1 : rmul R r h k = rone R r).
        { apply (mul_cancel_l r (id_no_zero_div d) g).
          - exact Hg_ne.
          - rewrite rmul_one_r.
            rewrite (rmul_assoc R r g h k).
            symmetry. exact Hk. }
        (* h is a unit with right inverse k, hence h | 1. *)
        apply (proj1 (unit_iff_divides_one r comm h)).
        exists k. split; [exact Hhk1 | rewrite (comm k h); exact Hhk1]. }
    exists l. split; [| split].
    - (* a | l: l = a*n. *)
      exists n. unfold l. reflexivity.
    - (* b | l: l = b*m. *)
      exists m. exact Hl_bm.
    - (* Minimality: a | c, b | c ⟹ l | c. *)
      intros c Hac Hbc.
      (* c = a*x. Then b | a*x, b = g*n, a = g*m, so n*y = m*x for some y.
         Hence n | m*x. By cofactor coprimality + Euclid, n | x.
         Then x = n*z, and c = a*n*z = l*z. *)
      destruct Hac as [x Hx].
      (* n | m*x: from g*n | g*m*x = a*x = c, and b | c gives b | a*x. *)
      assert (Hn_div_mx : divides r n (rmul R r m x)).
      { (* b | c = a*x = g*m*x. b = g*n. So g*n | g*m*x. Cancel g: n | m*x. *)
        destruct Hbc as [y Hy].
        assert (Hgny : rmul R r g (rmul R r n y) = rmul R r g (rmul R r m x)).
        { rewrite (rmul_assoc R r g n y).
          rewrite <- Hn.
          rewrite <- Hy, Hx, Hm.
          rewrite <- (rmul_assoc R r g m x). reflexivity. }
        assert (Hny_mx : rmul R r n y = rmul R r m x).
        { apply (mul_cancel_l r (id_no_zero_div d) g).
          - exact Hg_ne.
          - exact Hgny. }
        exists y. symmetry. exact Hny_mx. }
      (* By Euclid, n | x. (Need is_gcd 1 n m, swap from Hcop.) *)
      assert (Hcop' : is_gcd (rone R r) n m).
      { destruct Hcop as [Hm1 [Hn1 Hcop_min]].
        split; [exact Hn1 | split; [exact Hm1 |]].
        intros h Hhn Hhm. apply Hcop_min; assumption. }
      assert (Hn_div_x : divides r n x).
      { apply (euclid_lemma_ufd H n m x Hn_ne Hcop' Hn_div_mx). }
      destruct Hn_div_x as [z Hz].
      exists z. rewrite Hx, Hz. unfold l.
      apply rmul_assoc.
  Qed.

  (** GCD * LCM = a * b (up to associates) in a UFD *)
  Theorem ufd_gcd_lcm_product : forall (H : IsUFD d) (a b g l : R),
      is_gcd g a b ->
      is_lcm l a b ->
      is_associate d (rmul R r g l) (rmul R r a b).
  Proof.
    intros H a b g l Hgcd Hlcm.
    (* Case split on a = 0. *)
    destruct (classic (a = rzero R r)) as [Ha0 | Ha_ne].
    { (* a = 0: l must be 0 (since 0 | l from is_lcm). g*l = 0 = a*b. *)
      destruct Hlcm as [Hal _].
      rewrite Ha0 in Hal.
      pose proof (zero_divides r l Hal) as Hl0.
      rewrite Ha0, Hl0, rmul_zero_r, rmul_zero_l. apply associate_refl. }
    destruct (classic (b = rzero R r)) as [Hb0 | Hb_ne].
    { (* b = 0: l must be 0 (since 0 | l from is_lcm). g*l = 0 = a*b. *)
      destruct Hlcm as [_ [Hbl _]].
      rewrite Hb0 in Hbl.
      pose proof (zero_divides r l Hbl) as Hl0.
      rewrite Hb0, Hl0, rmul_zero_r, rmul_zero_r. apply associate_refl. }
    (* Both nonzero. *)
    destruct Hgcd as [Hga [Hgb Hgmin]].
    (* g <> 0 since g | a and a <> 0. *)
    assert (Hg_ne : g <> rzero R r).
    { intro Hg0. apply Ha_ne. destruct Hga as [k Hk]. rewrite Hk, Hg0.
      apply rmul_zero_l. }
    (* Extract m, n: a = g*m, b = g*n. *)
    destruct Hga as [m Hm]. destruct Hgb as [n Hn].
    (* m, n nonzero. *)
    assert (Hm_ne : m <> rzero R r).
    { intro Hm0. apply Ha_ne. rewrite Hm, Hm0. apply rmul_zero_r. }
    assert (Hn_ne : n <> rzero R r).
    { intro Hn0. apply Hb_ne. rewrite Hn, Hn0. apply rmul_zero_r. }
    (* Define l0 := a*n. Show is_lcm l0 a b. *)
    set (l0 := rmul R r a n).
    (* l0 = b*m, useful for showing b | l0. *)
    assert (Hl0_bm : l0 = rmul R r b m).
    { unfold l0. rewrite Hm, Hn.
      transitivity (rmul R r g (rmul R r m n)).
      { symmetry. apply rmul_assoc. }
      transitivity (rmul R r g (rmul R r n m)).
      { f_equal. apply comm. }
      apply rmul_assoc. }
    (* Cofactor coprimality: gcd(m, n) = 1.  (Reuses Round 10's argument.) *)
    assert (Hcop : is_gcd (rone R r) m n).
    { split; [| split].
      - apply one_divides.
      - apply one_divides.
      - intros h Hhm Hhn.
        assert (Hgh_a : divides r (rmul R r g h) a).
        { destruct Hhm as [m' Hm']. exists m'.
          rewrite Hm, Hm'.
          apply rmul_assoc. }
        assert (Hgh_b : divides r (rmul R r g h) b).
        { destruct Hhn as [n' Hn']. exists n'.
          rewrite Hn, Hn'.
          apply rmul_assoc. }
        pose proof (Hgmin (rmul R r g h) Hgh_a Hgh_b) as Hgh_g.
        destruct Hgh_g as [k Hk].
        assert (Hhk1 : rmul R r h k = rone R r).
        { apply (mul_cancel_l r (id_no_zero_div d) g).
          - exact Hg_ne.
          - rewrite rmul_one_r.
            rewrite (rmul_assoc R r g h k).
            symmetry. exact Hk. }
        apply (proj1 (unit_iff_divides_one r comm h)).
        exists k. split; [exact Hhk1 | rewrite (comm k h); exact Hhk1]. }
    (* Show is_lcm l0 a b. *)
    assert (Hlcm0 : is_lcm l0 a b).
    { split; [| split].
      - exists n. unfold l0. reflexivity.
      - exists m. exact Hl0_bm.
      - intros c Hac Hbc.
        destruct Hac as [x Hx].
        assert (Hn_div_mx : divides r n (rmul R r m x)).
        { destruct Hbc as [y Hy].
          assert (Hgny : rmul R r g (rmul R r n y) = rmul R r g (rmul R r m x)).
          { rewrite (rmul_assoc R r g n y).
            rewrite <- Hn.
            rewrite <- Hy, Hx, Hm.
            rewrite <- (rmul_assoc R r g m x). reflexivity. }
          assert (Hny_mx : rmul R r n y = rmul R r m x).
          { apply (mul_cancel_l r (id_no_zero_div d) g).
            - exact Hg_ne.
            - exact Hgny. }
          exists y. symmetry. exact Hny_mx. }
        assert (Hcop' : is_gcd (rone R r) n m).
        { destruct Hcop as [Hm1 [Hn1 Hcop_min]].
          split; [exact Hn1 | split; [exact Hm1 |]].
          intros h Hhn Hhm. apply Hcop_min; assumption. }
        assert (Hn_div_x : divides r n x).
        { apply (euclid_lemma_ufd H n m x Hn_ne Hcop' Hn_div_mx). }
        destruct Hn_div_x as [z Hz].
        exists z. rewrite Hx, Hz. unfold l0.
        apply rmul_assoc. }
    (* By lcm uniqueness, l ~ l0. *)
    pose proof (lcm_unique_up_to_associate l l0 a b Hlcm Hlcm0) as Hassoc_ll0.
    (* g*l0 = a*b. *)
    assert (Hgl0_ab : rmul R r g l0 = rmul R r a b).
    { unfold l0. rewrite Hn.
      (* Goal: g * (a * n) = a * (g * n) *)
      rewrite (rmul_assoc R r g a n).
      rewrite (comm g a).
      rewrite <- (rmul_assoc R r a g n).
      reflexivity. }
    (* g*l ~ g*l0 (multiplying associates by g). *)
    destruct Hassoc_ll0 as [u [Hu Hl_eq]].
    exists u. split; [exact Hu |].
    rewrite <- Hgl0_ab.
    rewrite Hl_eq.
    change (id_r d) with r.
    (* Goal: g * (u * l) = u * (g * l) *)
    rewrite (rmul_assoc R r g u l).
    rewrite (comm g u).
    rewrite <- (rmul_assoc R r u g l).
    reflexivity.
  Qed.

End GCD.

Arguments is_gcd {R} d g a b.
Arguments is_lcm {R} d l a b.
