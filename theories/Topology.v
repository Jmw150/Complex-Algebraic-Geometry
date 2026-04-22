
(** Sets

   Types do not have classical unions. They instead have tagged union.

   So instead we are defining sets as properties of types.
*)
From Stdlib Require Import Logic.IndefiniteDescription.

Definition set (X : Type) := X -> Prop.

(*Set Printing Universes.*)
(*Check set.*)

(* Canonical binary intersection/union of sets-as-predicates *)
Definition intersection {X : Type} (U V : set X) : set X :=
  fun x => U x /\ V x.

Definition union {X : Type} (U V : set X) : set X :=
  fun x => U x \/ V x.

Definition empty {A : Type} : A -> Prop :=
  fun _ => False.

Definition full {A : Type} : A -> Prop :=
  fun _ => True.

Definition In {A : Type} (X : A -> Prop) (x : A) := X x.

Definition subset {X} (A B : set X) : Prop :=
  forall x, A x -> B x.

Notation "X ∩ Y" := (intersection X Y) (at level 50).
Notation "X ∪ Y" := (union X Y) (at level 60).
Notation "X ∈ Y" := (In X Y) (at level 30).
Notation "X ⊆ Y" := (subset X Y) (at level 30).

(* Any type, and not type1 = sets *)
Record Topology (X : Type) := {
  is_open : set X -> Prop;

  open_full : is_open (fun _ => True);
  open_empty : is_open (fun _ => False);

  (* This can only be applied finite number of times *)
  open_inter :
    forall U V,
      is_open U ->
      is_open V ->
      is_open (fun x => U x /\ V x);

  open_union :
    forall (I : Type) (F : I -> set X),
      (forall i, is_open (F i)) ->
      is_open (fun x => exists i, F i x)
}.

Arguments is_open {X} _ _.

Definition covers {X} (T : Topology X) (U : set X) (I : Type) (Ui : I -> set X) 
  : Prop 
  := (forall i, is_open T (Ui i)) /\ (forall x, U x -> exists i, Ui i x).

Definition Hausdorff {X} (T : Topology X) : Prop :=
  forall x y : X,
    x <> y ->
    exists U V : set X,
      is_open T U /\
      is_open T V /\
      U x /\
      V y /\
      (forall z, U z -> V z -> False).

Definition is_basis {X}
  (T : Topology X)
  (I : Type)
  (B : I -> set X) 
  : Prop 
  := (forall i, is_open T (B i)) /\
       (forall U,
           is_open T U ->
           forall x, U x ->
                exists i, B i x /\ subset (B i) U).

Definition countable (I : Type) : Prop :=
  exists f : I -> nat,
    forall i j, f i = f j -> i = j.

Definition SecondCountable {X} (T : Topology X) : Prop :=
  exists I (B : I -> set X),
    countable I /\
    is_basis T I B.

Definition Subspace (X : Type) (U : set X) :=
  { x : X | U x }.

Definition preimage {X Y}
  (f : X -> Y)
  (V : set Y) : set X :=
  fun x => V (f x).

Definition continuous
  {X Y}
  (TX : Topology X)
  (TY : Topology Y)
  (f : X -> Y) 
  : Prop :=
  forall V : set Y, 
    is_open TY V ->
    is_open TX (preimage f V).

Lemma continuous_id :
  forall {X} (T : Topology X),
    continuous T T (fun x => x).
Proof.
  intros X T V HV.
  (* preimage id V = V definitionally *)
  exact HV.
Qed.

Lemma continuous_comp :
  forall {X Y Z}
    (TX : Topology X)
    (TY : Topology Y)
    (TZ : Topology Z)
    (f : X -> Y)
    (g : Y -> Z),
      continuous TX TY f ->
      continuous TY TZ g ->
      continuous TX TZ (fun x => g (f x)).
Proof.
  intros X Y Z TX TY TZ f g Hf Hg V HV.
  exact (Hf (fun y => V (g y)) (Hg V HV)).
Qed.

Definition subspace_topology
  {X}
  (TX : Topology X)
  (U : set X)
  : Topology { x : X | U x }.
Proof.
  refine {|
    is_open := fun V =>
      exists W : set X, is_open TX W /\ forall p : {x : X | U x}, V p <-> W (proj1_sig p);
    open_full  := _;
    open_empty := _;
    open_inter := _;
    open_union := _;
  |}.
  - (* full is open *)
    exists (fun _ => True). split.
    + exact (open_full X TX).
    + intro p. split; intro; exact I.
  - (* empty is open *)
    exists (fun _ => False). split.
    + exact (open_empty X TX).
    + intro p. split; intro H; exact H.
  - (* intersection *)
    intros V1 V2 [W1 [HW1 H1]] [W2 [HW2 H2]].
    exists (fun x => W1 x /\ W2 x). split.
    + exact (open_inter X TX W1 W2 HW1 HW2).
    + intro p. split.
      * intros [HV1 HV2]. split.
        -- exact (proj1 (H1 p) HV1).
        -- exact (proj1 (H2 p) HV2).
      * intros [HW1p HW2p]. split.
        -- exact (proj2 (H1 p) HW1p).
        -- exact (proj2 (H2 p) HW2p).
  - (* union: use indefinite description to extract W witnesses *)
    intros I F Hopen.
    set (Wi := fun i =>
      proj1_sig (constructive_indefinite_description
        (fun W => is_open TX W /\ forall p : {x : X | U x}, F i p <-> W (proj1_sig p))
        (Hopen i))).
    set (Hwi := fun i =>
      proj2_sig (constructive_indefinite_description
        (fun W => is_open TX W /\ forall p : {x : X | U x}, F i p <-> W (proj1_sig p))
        (Hopen i))).
    exists (fun x => exists i : I, Wi i x). split.
    + apply (open_union X TX). intro i. exact (proj1 (Hwi i)).
    + intro p. split.
      * intros [i HFi].
        exists i. exact (proj1 (proj2 (Hwi i) p) HFi).
      * intros [i HWi].
        exists i. exact (proj2 (proj2 (Hwi i) p) HWi).
Qed.
(** Note: uses constructive_indefinite_description for the open_union axiom. *)

Record Homeomorphism
  {X Y}
  (TX : Topology X)
  (TY : Topology Y) := {

  f : X -> Y; (* f and g are now specific topology functions... *)
  g : Y -> X;

  f_cont : continuous TX TY f;
  g_cont : continuous TY TX g;

  left_inv : forall x, g (f x) = x;
  right_inv : forall y, f (g y) = y;
}.


Definition is_homeomorphic {X Y}
  (TX : Topology X) (TY : Topology Y) : Prop :=
  exists _ : Homeomorphism TX TY, True.
