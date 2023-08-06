Set Implicit Arguments.

CoInductive CoList (A : Type) :=
  | conil : CoList A
  | cocons : A -> CoList A -> CoList A.

Arguments conil {A}.
Arguments cocons {A} a l.

Declare Scope colist_scope.
Delimit Scope colist_scope with CoList.
Bind Scope colist_scope with CoList.

Infix "::" := cocons (at level 60, right associativity) : colist_scope.

Local Open Scope colist_scope.

Module CoListNotations.
  Notation "[ ]" := conil (format "[ ]") : colist_scope.
  Notation "[ x ]" := (cocons x conil) : colist_scope.
  Notation "[ x ; y ; .. ; z ]" := (cocons x (cocons y .. (cocons z conil) ..))
    (format "[ '[' x ; '/' y ; '/' .. ; '/' z ']' ]") : colist_scope.
End CoListNotations.

Import CoListNotations.

Section CoLists.
  Variable A B C : Type.

  Definition hd (default:A) (l:CoList A) :=
    match l with
      | [] => default
      | x :: _ => x
    end.

  Fixpoint of_list (l : list A) :=
    match l with
      | nil => []
      | cons x l => x :: of_list l
    end.

  CoFixpoint repeat (x : A) : CoList A := x :: repeat x.

  CoFixpoint comap (f : A -> B) (l : CoList A) : CoList B :=
    match l with
      | [] => []
      | x :: l => f x :: comap f l
    end.

  CoFixpoint zipWith (f : A -> B -> C) (la : CoList A) (lb : CoList B) : CoList C :=
    match la, lb with
      | [], _ | _, [] => []
      | x :: la, y :: lb => f x y :: zipWith f la lb
    end.

  CoInductive EqCoList : CoList A -> CoList A -> Prop :=
    | EqCoNil : EqCoList [] []
    | EqCoCons (x : A) (cl cl' : CoList A) : EqCoList cl cl' -> EqCoList (x :: cl) (x :: cl').

  Axiom CoList_ext : forall { cl1 cl2 : CoList A }, EqCoList cl1 cl2 -> cl1 = cl2.

  Definition CoList_dunf (l : CoList A) : CoList A :=
    match l with
      | [] => []
      | x :: l => x :: l
    end.

  Theorem CoList_unf : forall (l : CoList A), l = CoList_dunf l.
  Proof.
    intros l; destruct l; simpl; trivial.
  Qed.
End CoLists.

Ltac colist_unf colist := erewrite (CoList_unf colist); simpl.
Ltac colist_fld colist := erewrite <- (CoList_unf colist); simpl.

Lemma comap_conil : forall {A B} (f : A -> B), comap f [] = [].
Proof.
  intros.
  colist_unf (comap f []).
  trivial.
Qed.

Lemma comap_cocons : forall {A B} (f : A -> B) (x : A) (l : CoList A), comap f (x :: l) = f x :: comap f l.
Proof.
  intros.
  colist_unf (comap f (x :: l)).
  trivial.
Qed.

Lemma zipWith_conil_l : forall {A B C} (f : A -> B -> C) (l : CoList B), zipWith f [] l = [].
Proof.
  intros.
  colist_unf (zipWith f [] l).
  trivial.
Qed.

Lemma zipWith_conil_r : forall {A B C} (f : A -> B -> C) (l : CoList A), zipWith f l [] = [].
Proof.
  intros.
  colist_unf (zipWith f l []).
  destruct l; trivial.
Qed.

Lemma zipWith_cocons : forall {A B C} (f : A -> B -> C) (x : A) (la : CoList A) (y : B) (lb : CoList B),
    zipWith f (x :: la) (y :: lb) = (f x y) :: zipWith f la lb.
Proof.
  intros.
  colist_unf (zipWith f (x :: la) (y :: lb)).
  trivial.
Qed.
