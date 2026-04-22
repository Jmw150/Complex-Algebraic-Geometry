(** * Category/Examples/Poset.v
    Posets as categories; meets = products, joins = coproducts,
    top = terminal, bottom = initial. *)

Require Import CAG.Category.Core.
Require Import CAG.Category.Products.
Require Import CAG.Category.Coproducts.
From Stdlib Require Import Logic.ProofIrrelevance.

Unset Universe Polymorphism.
Open Scope cat_scope.

(** ** A preorder as a category

    Objects: elements of a type X.
    Hom(a, b): proof that a ≤ b (a proposition, so at most one morphism).
*)

Record Preorder : Type := {
  po_carrier : Type;
  po_le      : po_carrier -> po_carrier -> Prop;
  po_refl    : forall x, po_le x x;
  po_trans   : forall x y z, po_le x y -> po_le y z -> po_le x z;
}.

Definition PreorderCat (P : Preorder) : Category := {|
  Ob  := P.(po_carrier);
  Hom := fun a b => P.(po_le) a b;
  id  := fun a => P.(po_refl) a;
  comp := fun a b c h g => P.(po_trans) a b c g h;
  comp_assoc := fun a b c d f g h => proof_irrelevance _ _ _;
  id_left    := fun a b f => proof_irrelevance _ _ _;
  id_right   := fun a b f => proof_irrelevance _ _ _;
|}.

(** ** Terminal = top element *)

Definition top_is_terminal (P : Preorder) (top : P.(po_carrier))
    (h_top : forall x, P.(po_le) x top) :
    @IsTerminal (PreorderCat P) top.
Proof.
  refine (Build_IsTerminal (PreorderCat P) top (fun A => h_top A) _).
  intros A f. exact (proof_irrelevance (P.(po_le) A top) f (h_top A)).
Defined.

(** ** Initial = bottom element *)

Definition bot_is_initial (P : Preorder) (bot : P.(po_carrier))
    (h_bot : forall x, P.(po_le) bot x) :
    @IsInitial (PreorderCat P) bot.
Proof.
  refine (Build_IsInitial (PreorderCat P) bot (fun A => h_bot A) _).
  intros A f. exact (proof_irrelevance (P.(po_le) bot A) f (h_bot A)).
Defined.

(** ** Meet = binary product

    In a preorder-as-category, a meet of a and b is an object m such that
    m ≤ a, m ≤ b, and for all x, x ≤ a /\ x ≤ b -> x ≤ m. *)

Definition meet_is_product (P : Preorder) (a b m : P.(po_carrier))
    (h1 : P.(po_le) m a)
    (h2 : P.(po_le) m b)
    (h_univ : forall x, P.(po_le) x a -> P.(po_le) x b -> P.(po_le) x m) :
    @IsBinaryProduct (PreorderCat P) a b m.
Proof.
  refine (Build_IsBinaryProduct (PreorderCat P) a b m
    h1 h2 (fun X f g => h_univ X f g) _ _ _).
  - intros X f g. cbn. apply proof_irrelevance.
  - intros X f g. cbn. apply proof_irrelevance.
  - intros X h.   cbn. apply proof_irrelevance.
Defined.

(** ** Join = binary coproduct *)

Definition join_is_coproduct (P : Preorder) (a b j : P.(po_carrier))
    (i1 : P.(po_le) a j)
    (i2 : P.(po_le) b j)
    (h_univ : forall x, P.(po_le) a x -> P.(po_le) b x -> P.(po_le) j x) :
    @IsBinaryCoproduct (PreorderCat P) a b j.
Proof.
  refine (Build_IsBinaryCoproduct (PreorderCat P) a b j
    i1 i2 (fun X f g => h_univ X f g) _ _ _).
  - intros X f g. cbn. apply proof_irrelevance.
  - intros X f g. cbn. apply proof_irrelevance.
  - intros X h.   cbn. apply proof_irrelevance.
Defined.
