From Coq.Program Require Import Basics.
From Coq.Logic Require Import FunctionalExtensionality.
From ExtLib Require Import
            Structures.Applicative
            Structures.Monad
            Structures.MonadLaws
            Data.List.

Import ApplicativeNotation.

From ZlistNotAMonad Require Import ApplicativeLaws.

Set Implicit Arguments.
Set Strict Implicit.
Set Universe Polymorphism.

Section Instances.
  Universe d c.
  Context (m : Type@{d} -> Type@{c}) {M : Monad m} {ML : MonadLaws M}.

  Lemma ap_of_pure_id : forall { X } (v : m X), ap (pure id) v = v.
  Proof.
    intros.
    unfold pure, ap, Applicative_Monad, apM, liftM, id.
    rewrite (bind_of_return _).
    change (fun x => ?h x) with h.
    rewrite (return_of_bind _).
    reflexivity.
  Qed.

  Lemma ap_of_pure_to_pure : forall { X Y } (x : X) (f : X -> Y), ap (@pure m _ _ f) (pure x) = pure (f x).
  Proof.
    intros.
    unfold pure, ap, Applicative_Monad, apM, liftM.
    rewrite 2 (bind_of_return _).
    reflexivity.
  Qed.

  Lemma ap_interchange : forall { X Y } (v : m (X -> Y)) (x : X),
    ap v (pure x) = ap (pure (flip apply x)) v.
  Proof.
    intros.
    unfold pure, ap, Applicative_Monad, apM, liftM, flip, apply.
    rewrite (bind_of_return _).
    f_equal.
    extensionality f.
    rewrite (bind_of_return _).
    reflexivity.
  Qed.

  Lemma ap_compose : forall { X Y Z } (u : m (Y -> Z)) (v : m (X -> Y)) (w : m X),
    pure compose <*> u <*> v <*> w = u <*> (v <*> w).
  Proof.
    intros.
    unfold pure, ap, Applicative_Monad, apM, liftM.
    rewrite 2 (bind_associativity _).
    rewrite (bind_of_return _).
    rewrite (bind_associativity _).
    f_equal.
    intros.
    rewrite H4.
    reflexivity.
    extensionality f.
    rewrite (bind_of_return _).
    rewrite 2 (bind_associativity _).
    f_equal.
    extensionality a.
    rewrite (bind_of_return _).
    rewrite (bind_associativity _).
    f_equal.
    intros.
    rewrite H4.
    reflexivity.
    extensionality x.
    rewrite (bind_of_return _).
    reflexivity.
  Qed.

  Global Instance ApplicativeLaws_MonadLaws@{} : ApplicativeLaws (Applicative_Monad (m:=m)) :=
    {
      ap_of_pure_id := @ap_of_pure_id
    ; ap_of_pure_to_pure := @ap_of_pure_to_pure
    ; ap_interchange := @ap_interchange
    ; ap_compose := @ap_compose
    }.
End Instances.
