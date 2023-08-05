From Coq.Program Require Import Basics.
From ExtLib Require Import
            Structures.Applicative
            Data.List.

Import ApplicativeNotation.

From ZlistNotAMonad Require Import ApplicativeLaws.

Section ListApplicative.
  Instance App_list_cart : Applicative list :=
    { pure := fun _ x => x :: nil
    ; ap   := fun _ _ f x => map (fun f_and_x => (fst f_and_x) (snd f_and_x)) (list_prod f x)
    }.

  Lemma map_compose : forall { X Y Z } (f : Y -> Z) (g : X -> Y) (x : list X), map f (map g x) = map (compose f g) x.
  Proof.
    induction x.
    - reflexivity.
    - repeat (rewrite map_cons).
      f_equal.
      assumption.
  Qed.

  Lemma list_prod_cons : forall { A B } (l : list A) (l' : B),
      list_prod l (l' :: nil) = map (fun l => (l, l')) l.
  Proof.
    intros.
    induction l.
    - reflexivity.
    - f_equal.
      cbn.
      f_equal.
      apply IHl.
  Qed.

  Lemma cart_identity : forall { X } (v : list X), pure id <*> v = v.
  Proof.
    intros.
    cbn.
    ssimpl_list.
    rewrite map_compose.
    unfold compose.
    cbn.
    induction v.
      - reflexivity.
      - rewrite map_cons.
        f_equal.
        apply IHv.
  Qed.

  Lemma cart_homomorphism : forall { X Y } (x : X) (f : X -> Y), pure f <*> pure x = pure (f x).
  Proof.
    intuition.
  Qed.

  Lemma cart_interchange : forall { X Y } (v : list (X -> Y)) (x : X),
      v <*> pure x = pure (flip apply x) <*> v.
  Proof.
    intros.
    induction v.
    - reflexivity.
    - cbn.
      ssimpl_list.
      f_equal.
      rewrite map_compose.
      unfold compose.
      cbn.
      rewrite list_prod_cons.
      rewrite map_compose.
      reflexivity.
  Qed.

  Lemma ap_cons : forall { X Y } (f : X -> Y) (fs : list (X -> Y)) (xs : list X),
      (f :: fs) <*> xs = map f xs ++ (fs <*> xs).
  Proof.
    intros.
    cbn.
    rewrite map_app.
    f_equal.
    rewrite map_compose.
    reflexivity.
  Qed.

  Lemma ap_nil_r : forall { X Y } (x : list (X -> Y)), x <*> nil = nil.
  Proof.
    induction x.
    - reflexivity.
    - rewrite ap_cons.
      apply IHx.
  Qed.

  Lemma ap_nil_l : forall { X Y } (x : list X), (@nil (X -> Y)) <*> x = nil.
  Proof.
    induction x.
    - reflexivity.
    - cbn.
      reflexivity.
  Qed.

  Lemma ap_pure : forall { X Y } (f : X -> Y) (xs : list X),
      pure f <*> xs = map f xs.
  Proof.
    intros.
    unfold pure, App_list_cart.
    rewrite ap_cons.
    apply app_nil_r.
  Qed.

  Lemma ap_app : forall { A B } (x : list (A -> B)) (y : list (A -> B)) (z : list A),
      (x ++ y) <*> z = x <*> z ++ y <*> z.
  Proof.
    induction x.
    - reflexivity.
    - intros.
      rewrite <- app_comm_cons.
      rewrite ap_cons.
      rewrite IHx.
      rewrite ap_cons.
      rewrite app_assoc.
      reflexivity.
    Qed.

  Lemma map_ap : forall { X Y Z } (u : list (X -> Y)) (v : list X) (f : Y -> Z),
      map f (u <*> v) = map (compose f) u <*> v.
  Proof.
    induction u.
    - reflexivity.
    - intros.
      rewrite map_cons.
      rewrite ap_cons.
      rewrite ap_cons.
      rewrite map_app.
      rewrite map_compose.
      f_equal.
      apply IHu.
  Qed.

  Lemma cart_compose : forall { X Y Z } (u : list (Y -> Z)) (v : list (X -> Y)) (w : list X),
      pure compose <*> u <*> v <*> w = u <*> (v <*> w).
  Proof.
    induction u, v, w; try now repeat (rewrite ap_nil_l || rewrite ap_nil_r).
    rewrite ap_cons.
    rewrite ap_pure.
    rewrite map_cons.
    rewrite ap_cons.
    rewrite ap_app.
    rewrite <- IHu.
    rewrite ap_pure.
    f_equal.
    rewrite map_ap.
    reflexivity.
  Qed.


  Instance App_laws_list_cart : ApplicativeLaws App_list_cart :=
    { ap_of_pure_id := @cart_identity
    ; ap_of_pure_to_pure := @cart_homomorphism
    ; ap_interchange := @cart_interchange
    ; ap_compose := @cart_compose
    }.

End ListApplicative.
