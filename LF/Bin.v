From Coq Require Export String.

Theorem plus_O_n : forall n : nat, 0 + n = n.
Proof.
  intros n. simpl. reflexivity.  Qed.

Theorem plus_O_n' : forall n : nat, 0 + n = n.
Proof.
  intros n. reflexivity. Qed.

Theorem plus_1_l : forall n:nat, 1 + n = S n.
Proof.
  intros n. reflexivity.  Qed.

Theorem mult_0_l : forall n:nat, 0 * n = 0.
Proof.
  intros n. reflexivity.  Qed.

Theorem plus_id_example : forall n m:nat,
  n = m ->
  n + n = m + m.
Proof.
  (* move both quantifiers into the context: *)
  intros n m.
  (* move the hypothesis into the context: *)
  intros H.
  (* rewrite the goal using the hypothesis: *)
  rewrite -> H.
  reflexivity.  Qed.

Theorem plus_n_0_eq_n:
  forall n:nat, n + 0 = n.
Proof.
  intros n.
  induction n as [|n'].
  - simpl. reflexivity.
  - simpl. (* (plus (S n') 0) = (S n') => S (plus n' 0) = S n' *)
    rewrite -> IHn'.
    reflexivity.
Qed.

Theorem mult_n_1_eq_n :
  forall n:nat, n * 1 = n.
Proof.
  intros n.
  induction n as [|n' IH].
  - simpl. reflexivity.
  - simpl. (* (S n') * 1 = S n' => (plus 1 (mult n' 1)) *)
    rewrite -> IH.
    reflexivity.
Qed.

Inductive bin : Type :=
  | Z
  | A (n : bin)
  | B (n : bin).

(** (a) Complete the definitions below of an increment function [incr]
        for binary numbers, and a function [bin_to_nat] to convert
        binary numbers to unary numbers. *)

Fixpoint incr (m:bin) : bin := match m with
| Z => B Z
| B b' => A (incr b')
| A b' => B b'
end.

Fixpoint bin_to_nat (m:bin) : nat := match m with
| Z => O
| B b' => plus 1 (mult 2 (bin_to_nat b'))
| A b' => mult 2 (bin_to_nat b')
end.

Example incr_1: incr Z = B Z.
Proof. reflexivity. Qed.
Example incr_2: incr (B Z) = A (B Z).
Proof. reflexivity. Qed.
Example incr_3: incr (A (B Z)) = B (B Z).
Proof. reflexivity. Qed.
Example incr_4: incr (B (B Z)) = A (A (B Z)).
Proof. reflexivity. Qed.
Example bin_to_nat_1: bin_to_nat Z = O.
Proof. reflexivity. Qed.
Example bin_to_nat_2: bin_to_nat (B Z) = S O.
Proof. reflexivity. Qed.
Example bin_to_nat_3: bin_to_nat (A (B Z)) = S (S O).
Proof. reflexivity. Qed.
Example bin_to_nat_4: bin_to_nat (B (B Z)) = S (S (S O)).
Proof. reflexivity. Qed.

Theorem mult_2_eq_n_plus_n:
  forall n:nat, mult 2 n = n + n.
Proof.
  intros n.
  assert(mult_S_n': forall n m:nat, mult (S n) m = plus m (mult n m)).
  { reflexivity. }
  rewrite -> mult_S_n'.
  rewrite -> mult_S_n'.
  rewrite -> mult_0_l.
  rewrite -> plus_n_0_eq_n.
  reflexivity.
Qed.

Theorem plus_is_commutative:
  forall a b:nat, a + b = b + a.
Proof.
  (* a' + b = b + a' *)
  (* S a' + b = b + S a' *)
  induction a as [|a'].
  - (* Case a = O *)
    induction b as [|b'].
    + (* Case b = O *)
      reflexivity.
    + (* Case b = S b' *)
      (* IHb':  Z + b' = b' + Z *)
      (* INIT: Z + S b' = S b' + Z *)
      simpl.
      (*     : S b' = S (b + Z) *)
      rewrite <- IHb'.
      reflexivity.
  - (* Case a = S a' *)
    induction b as [|b'].
    + (* Case b = O *)
      (* IHa': a' + O = O + a' *)
      (* S a' + O = O + S a' *)
      simpl.
      (* S (a' + O) = S a' *)
      rewrite -> IHa'.
      reflexivity.
    + (* Case b = S b' *)
      (* IHa': forall b, a' + b = b + a' *)
      (* IHb': S a' + b' = b' + S a' *)
      (* init: S a' + S b' = S b' + S a' *)
      simpl.
      (*     : S (a' + S b') = S (b' + S a') *)
      rewrite -> IHa'.
      (*     : S (S b' + a') = S (b' + S a') *)
      simpl.
      (*     : S (S (b' + a')) = S (b' + S a') *)
      rewrite <- (IHa' b').
      (*     : S (S (a' + b')) = S (b' + S a') *)
      rewrite <- IHb'.
      reflexivity.
Qed.

(* mult 2 (S (bin_to_nat b')) = S (plus 1 (mult 2 (bin_to_nat b'))) *)
Theorem mult_shit:
  forall n:nat, mult 2 (S n) = S (1 + 2 * n).
Proof.
  induction n as [|n'].
  - reflexivity.
  - (* Case n = S n' *)
    (* IHn': mult 2 (S n') = S (1 + 2 * n') *)
    (* mult 2 (S n) = S (1 + 2 * n). *)
    simpl.
    (* S (S (plus n' (S (S (plus n' 0))))) = 
    *  S (S (S (n' + S (n' + 0)))) *)
    rewrite <- (plus_is_commutative (S (n' + 0)) n').
    rewrite <- (plus_is_commutative 0 n').
    simpl.
    rewrite <- (plus_is_commutative (S (S n')) n').
    simpl.
    reflexivity.
Qed.

Theorem incr_and_bin_to_nat_is_right:
  forall n:bin, bin_to_nat (incr n) = S (bin_to_nat n).
Proof.
  intros n.
  induction n as [|b'|b'].
  - simpl. (* bin_to_nat *)
    reflexivity.
  - (* IHb': bin_to_nat (incr b') = S (bin_to_nat b') *)
    (* ---------------------------------------------- *)
    (* bin_to_nat (incr (A b')) = S (bin_to_nat (A b')) *)
    simpl.
    reflexivity.
  - (* IHb': bin_to_nat (incr b') = S (bin_to_nat b') *)
    (* ---------------------------------------------- *)
    (* bin_to_nat (incr (B b')) = S (bin_to_nat (B b')) *)
    assert (incr_B_b:forall b:bin, incr (B b) = A (incr b)).
    { reflexivity. }
    rewrite -> incr_B_b.
    (* bin_to_nat (A (incr b')) = S (bin_to_nat (B b')) *)
    assert (bin_to_nat_A_b: forall b:bin, bin_to_nat (A b) = mult 2 (bin_to_nat b)).
    { reflexivity. }
    rewrite -> bin_to_nat_A_b.
    (* mult 2 (bin_to_nat (incr b')) = S (bin_to_nat (B b')) *)
    rewrite -> IHb'.
    (* mult 2 (S (bin_to_nat b')) = S (bin_to_nat (B b')) *)
    assert (bin_to_nat_B_b: forall b:bin, bin_to_nat (B b) = plus 1 (mult 2 (bin_to_nat b))).
    { reflexivity. }
    rewrite -> bin_to_nat_B_b.
    (* 2 * (S (bin_to_nat b')) = S (1 + (2 * (bin_to_nat b'))) *)
    rewrite <- (mult_shit (bin_to_nat b')).
    reflexivity.
Qed.

(* FILL IN HERE *)

(* Do not modify the following line: *)
Definition manual_grade_for_binary : option (nat*string) := None.
(** [] *)

(* Wed Jan 9 12:02:44 EST 2019 *)


