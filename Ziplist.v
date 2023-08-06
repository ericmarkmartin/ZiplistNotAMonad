From Coq.Program Require Import Basics.
From ExtLib Require Import Structures.Functor
                           Structures.FunctorLaws
                           Structures.Applicative.

From ZlistNotAMonad Require Import CoList
                                   ApplicativeLaws.

Import ApplicativeNotation.

Local Open Scope colist_scope.
Import CoListNotations.

Section Functor.
  Instance Functor_colist : Functor CoList :=
    { fmap := @comap }.

  Lemma colist_fmap_id' : forall {A} (l : CoList A), EqCoList (fmap id l) l.
  Proof.
    unfold fmap, Functor_colist.
    cofix CIH.
    destruct l.
    - (* l = conil *)
      rewrite comap_conil.
      constructor.
    - (* l = cocons *)
      rewrite comap_cocons.
      constructor.
      apply CIH.
  Qed.

  Lemma colist_fmap_id : forall {A} (l : CoList A), fmap id l = l.
  Proof.
    intros.
    apply CoList_ext.
    apply colist_fmap_id'.
  Qed.

  Lemma colist_fmap_compose' : forall {A B C} (f : A -> B) (g : B -> C) (l : CoList A),
      EqCoList (fmap (compose g f) l) (fmap g (fmap f l)).
  Proof.
    unfold fmap, Functor_colist.
    cofix CIH.
    destruct l.
    - (* l = conil *)
      repeat rewrite comap_conil.
      constructor.
    - (* l = cocons *)
      repeat rewrite comap_cocons.
      constructor.
      apply CIH.
  Qed.

  Lemma colist_fmap_compose : forall {A B C} (f : A -> B) (g : B -> C) (l : CoList A),
      fmap (compose g f) l = fmap g (fmap f l).
  Proof.
    intros.
    apply CoList_ext.
    apply colist_fmap_compose'.
  Qed.

  Instance FunctorLaws_colist : FunctorLaws Functor_colist :=
    { fmap_id      := @colist_fmap_id
    ; fmap_compose := @colist_fmap_compose
    }.
End Functor.

Section Applicative.
  CoFixpoint colist_ap {A B} (f : CoList (A -> B)) (x : CoList A) : CoList B :=
    match f, x with
      | [], _ | _, [] => []
      | f' :: f, x' :: x => f' x' :: colist_ap f x
    end.

  Instance Applicative_colist : Applicative CoList :=
    { pure := @repeat
    ; ap   := fun _ _ f x => zipWith apply f x
    }.

  Lemma colist_ap_of_pure_id' : forall { X } (v : CoList X), EqCoList (pure id <*> v) v.
  Proof.
    unfold pure, ap, Applicative_colist.
    cofix CIH.
    destruct v.
    - (* conil *)
      rewrite zipWith_conil_r.
      constructor.
    - (* cocons *)
      colist_unf (@repeat (X -> X) id).
      rewrite zipWith_cocons.
      constructor.
      apply CIH.
  Qed.

  Lemma colist_ap_of_pure_id : forall { X } (v : CoList X), pure id <*> v = v.
  Proof.
    intros.
    apply CoList_ext.
    apply colist_ap_of_pure_id'.
  Qed.
End Applicative.
