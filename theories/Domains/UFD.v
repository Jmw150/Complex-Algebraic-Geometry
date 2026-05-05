(** * Domains/UFD.v — Unique Factorization Domains

    Formalizes UFDs: every nonzero nonunit has a factorization into
    irreducibles, unique up to permutation and associates.

    Reference: Dummit & Foote §8.3. *)

From CAG Require Import Rings.Ring Domains.Divisibility Domains.Associates
                        Domains.IrreduciblePrime.
From Stdlib Require Import Arith Lia List Permutation.
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

  (** In a UFD, irreducible implies prime *)
  (** This is a key theorem: stated here as an axiom on a UFD *)
(* CAG zero-dependent Axiom ufd_irreducible_prime theories/Domains/UFD.v:82 BEGIN
  Axiom ufd_irreducible_prime : forall (H : IsUFD) (p : R),
      is_irreducible d p -> is_prime d p.
   CAG zero-dependent Axiom ufd_irreducible_prime theories/Domains/UFD.v:82 END *)

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

  (** UFD divisibility in terms of prime factorizations:
      a | b iff every irreducible factor of a (counted with multiplicity)
      appears among the irreducible factors of b.

      Stated as a Conjecture pending exponent-pattern infrastructure
      (counted multiplicity / multiset matching of `fact_irrs`).
      Reference: Dummit & Foote §8.3 Proposition 13. *)
(* CAG zero-dependent Conjecture ufd_divisibility_exponents theories/Domains/UFD.v:153 BEGIN
  Conjecture ufd_divisibility_exponents : forall (H : IsUFD) (a b : R),
      a <> rzero R r -> b <> rzero R r ->
      ~ is_unit r a -> ~ is_unit r b ->
      divides r a b ->
      forall (Fa : Factorization a) (Fb : Factorization b),
        (* Every irreducible factor of a is associate to some factor of b.
           Stated multiplicity-blind here; multiplicity ≤ comparison
           pending counted-membership infrastructure. *)
        forall p, In p (fact_irrs a Fa) ->
          exists q, In q (fact_irrs b Fb) /\ is_associate d p q.
   CAG zero-dependent Conjecture ufd_divisibility_exponents theories/Domains/UFD.v:153 END *)

End UFDDef.

Arguments list_product {R} d ps.
Arguments IsUFD {R} d.
Arguments Factorization {R} d a.
