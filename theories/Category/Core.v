(** * Category/Core.v
    Basic category definition, opposite category, isomorphisms. *)

Set Universe Polymorphism.

(** ** Category record *)

Record Category : Type := {
  Ob   : Type;
  Hom  : Ob -> Ob -> Type;
  id   : forall A, Hom A A;
  comp : forall {A B D}, Hom B D -> Hom A B -> Hom A D;

  comp_assoc : forall {A B D E} (f : Hom D E) (g : Hom B D) (h : Hom A B),
    comp f (comp g h) = comp (comp f g) h;
  id_left  : forall {A B} (f : Hom A B), comp (id B) f = f;
  id_right : forall {A B} (f : Hom A B), comp f (id A) = f;
}.

(** Make the Category argument implicit for field accessors. *)
Arguments id   {c} A.
Arguments comp {c A B D} f g.

Declare Scope cat_scope.
Open Scope cat_scope.

Notation "C ⟦ A , B ⟧" := (Hom C A B) (at level 50) : cat_scope.
Notation "f ∘ g"        := (comp f g)   (at level 40, left associativity) : cat_scope.

(** ** Opposite category *)

Definition op (C : Category) : Category := {|
  Ob   := C.(Ob);
  Hom  := fun A B => C.(Hom) B A;
  id   := C.(id);
  comp := fun A B D f g => C.(comp) g f;
  comp_assoc := fun A B D E f g h => eq_sym (C.(comp_assoc) h g f);
  id_left    := fun A B f => C.(id_right) f;
  id_right   := fun A B f => C.(id_left) f;
|}.

Notation "C ^op" := (op C) (at level 5) : cat_scope.

(** ** Isomorphism *)

Record Isomorphism {C : Category} (A B : C.(Ob)) : Type := {
  iso_fwd     : C⟦A, B⟧;
  iso_bwd     : C⟦B, A⟧;
  iso_fwd_bwd : iso_bwd ∘ iso_fwd = C.(id) A;
  iso_bwd_fwd : iso_fwd ∘ iso_bwd = C.(id) B;
}.

Arguments iso_fwd     {C A B} i.
Arguments iso_bwd     {C A B} i.
Arguments iso_fwd_bwd {C A B} i.
Arguments iso_bwd_fwd {C A B} i.

Notation "A ≅[ C ] B" := (@Isomorphism C A B) (at level 70) : cat_scope.

Definition iso_refl {C : Category} (A : C.(Ob)) : A ≅[C] A := {|
  iso_fwd     := C.(id) A;
  iso_bwd     := C.(id) A;
  iso_fwd_bwd := C.(id_left) (C.(id) A);
  iso_bwd_fwd := C.(id_left) (C.(id) A);
|}.

Definition iso_sym {C : Category} {A B : C.(Ob)} (i : A ≅[C] B) : B ≅[C] A := {|
  iso_fwd     := i.(iso_bwd);
  iso_bwd     := i.(iso_fwd);
  iso_fwd_bwd := i.(iso_bwd_fwd);
  iso_bwd_fwd := i.(iso_fwd_bwd);
|}.

Definition iso_trans {C : Category} {A B D : C.(Ob)}
    (i : A ≅[C] B) (j : B ≅[C] D) : A ≅[C] D.
Proof.
  refine {|
    iso_fwd := j.(iso_fwd) ∘ i.(iso_fwd);
    iso_bwd := i.(iso_bwd) ∘ j.(iso_bwd);
  |}.
  - rewrite C.(comp_assoc).
    rewrite <- (C.(comp_assoc) (i.(iso_bwd)) (j.(iso_bwd)) (j.(iso_fwd))).
    rewrite j.(iso_fwd_bwd).
    rewrite C.(id_right).
    exact i.(iso_fwd_bwd).
  - rewrite C.(comp_assoc).
    rewrite <- (C.(comp_assoc) (j.(iso_fwd)) (i.(iso_fwd)) (i.(iso_bwd))).
    rewrite i.(iso_bwd_fwd).
    rewrite C.(id_right).
    exact j.(iso_bwd_fwd).
Defined.

(** ** Terminal and initial objects *)

Record IsTerminal {C : Category} (T : C.(Ob)) : Type := {
  term_arr  : forall A, C⟦A, T⟧;
  term_uniq : forall A (f : C⟦A, T⟧), f = term_arr A;
}.

Record IsInitial {C : Category} (I : C.(Ob)) : Type := {
  init_arr  : forall A, C⟦I, A⟧;
  init_uniq : forall A (f : C⟦I, A⟧), f = init_arr A;
}.


(** Terminal objects are unique up to isomorphism. *)
Lemma terminal_unique {C : Category} {T T' : C.(Ob)}
    (hT : IsTerminal T) (hT' : IsTerminal T') : T ≅[C] T'.
Proof.
  refine {|
    iso_fwd := term_arr T' hT' T;
    iso_bwd := term_arr T hT T';
  |}.
  - etransitivity; [ apply (term_uniq T hT T _) | symmetry; apply (term_uniq T hT T _) ].
  - etransitivity; [ apply (term_uniq T' hT' T' _) | symmetry; apply (term_uniq T' hT' T' _) ].
Defined.

(** Initial objects are unique up to isomorphism. *)
Lemma initial_unique {C : Category} {I I' : C.(Ob)}
    (hI : IsInitial I) (hI' : IsInitial I') : I ≅[C] I'.
Proof.
  refine {|
    iso_fwd := init_arr I hI I';
    iso_bwd := init_arr I' hI' I;
  |}.
  - etransitivity; [ apply (init_uniq I hI I _) | symmetry; apply (init_uniq I hI I _) ].
  - etransitivity; [ apply (init_uniq I' hI' I' _) | symmetry; apply (init_uniq I' hI' I' _) ].
Defined.
