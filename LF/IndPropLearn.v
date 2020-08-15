(** * IndProp: Inductively Defined Propositions *)

Set Warnings "-notation-overridden,-parsing".
From LF Require Export Logic.
Require Coq.omega.Omega.

Inductive even : nat -> Prop :=
| ev_0 : even 0
| ev_SS (n : nat) (H: even n) : even (S (S n))
.

Check ev_SS.
Theorem ev_4 : even 4.
Proof.
  apply (ev_SS 2).
  apply (ev_SS 0).
  apply ev_0.
Qed.

Theorem ev_4' : even 4.
Proof.
  apply (ev_SS 2 (ev_SS 0 ev_0)).
Qed.

Theorem ev_plus_4:
  forall n:nat, even n -> even (4 + n).
Proof.
  intros n H.
  exact (ev_SS (2 + n) (ev_SS n H)).
Qed.

Theorem ev_inversion :
  forall (n : nat), even n ->
    (n = 0) \/ (exists n', n = S (S n') /\ even n').
Proof.
  intros n Hn.
  destruct Hn as [|n' H'].
  - left. reflexivity.
  - right. exists n'. split. reflexivity. exact H'.
Qed.

Theorem ev_minus2 : forall n,
  even n -> even (pred (pred n)).
Proof.
  intros n Hn.
  destruct Hn as [|n' H'].
  - simpl. exact ev_0.
  - simpl. exact H'.
Qed.

Theorem evSS_ev : forall n,
  even (S (S n)) -> even n.
Proof.
  intros n Hn.
  apply ev_inversion in Hn.
  destruct Hn as [H' | H'].
  - discriminate H'.
  - destruct H' as [n' [Hl Hr]].
    injection Hl as Hl'.
    rewrite <- Hl' in Hr.
    exact Hr.
Qed.

Theorem evSS_ev' : forall n,
  even (S (S n)) -> even n.
Proof.
  intros n E.
  inversion E as [|n' E'].
  exact E'.
Qed.

Theorem one_not_even : ~ even 1.
Proof.
  unfold "~".
  intros H.
  inversion H.
Qed.
