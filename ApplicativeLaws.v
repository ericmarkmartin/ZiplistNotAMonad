From Coq.Program Require Import Basics.
From ExtLib Require Import Structures.Applicative.

Import ApplicativeNotation.

Set Implicit Arguments.
Set Strict Implicit.

Section ApplicativeLaws.
  Variable a : Type -> Type.
  Variable A : Applicative a.

  Class ApplicativeLaws :=
    { ap_of_pure_id : forall { X } (v : a X),
        ap (pure id) v = v
    ; ap_of_pure_to_pure : forall { X Y } (x : X) (f : X -> Y),
        ap (pure f) (pure x) = pure (f x)
    ; ap_interchange : forall { X Y } (v : a (X -> Y)) (x : X),
        ap v (pure x) = ap (pure (flip apply x)) v
    ; ap_compose : forall { X Y Z } (u : a (Y -> Z)) (v : a (X -> Y)) (w : a X),
        pure compose <*> u <*> v <*> w = u <*> (v <*> w)
    }.
End ApplicativeLaws.
