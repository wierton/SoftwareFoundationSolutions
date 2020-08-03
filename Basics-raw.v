Inductive day : Type :=
| monday
| tuesday
| wednesday
| thursday
| friday
| saturday
| sunday.

Definition next_weekday (d:day) : day :=
match d with
| monday => tuesday
| tuesday => wednesday
| wednesday => thursday
| thursday => friday
| friday => saturday
| saturday => sunday
| sunday => monday
end.

Compute (next_weekday friday).
(* ==> monday : day *)

Compute (next_weekday (next_weekday saturday)).
(* ==> tuesday : day *)

Example test_next_weekday:
  (next_weekday (next_weekday sunday)) = tuesday.

Proof. simpl. reflexivity.  Qed.

Module BoolWorkbench.
Inductive bool : Type :=
| true
| false.
End BoolWorkbench.

Definition negb (b:bool) : bool := match b with
| true => false
| false => true
end.

Definition andb(b1:bool)(b2:bool) : bool := match b1 with
| true => b2
| false => false
end.

Definition orb(b1:bool)(b2:bool) : bool := match b1 with
| false => b2
| true => true
end.

Compute (negb true).
Compute (andb true true).
Compute (orb (andb true false) true).

Example test_orb1: (orb true true) = true.
Proof. simpl. reflexivity. Qed.
Example test_orb2: (orb true false) = true.
Proof. simpl. reflexivity. Qed.
Example test_orb3: (orb false true) = true.
Proof. simpl. reflexivity. Qed.
Example test_orb4: (orb false false) = false.
Proof. simpl. reflexivity. Qed.

Notation "x && y" := (and x y).
Notation "x || y" := (orb x y).
Example test_andb1: (true || true) = true.
Proof. simpl. reflexivity. Qed.

(* Ex.1 standard(nandb) *)

Definition notb(b1:bool) : bool := match b1 with
| true => false
| false => true
end.
(* ~a || ~b *)
Definition nandb(b1:bool)(b2:bool) : bool := (notb (andb b1 b2)).

Example test_nandb1: (nandb true false) = true.
Proof. simpl. reflexivity. Qed.
Example test_nandb2: (nandb false false) = true.
Proof. simpl. reflexivity. Qed.
Example test_nandb3: (nandb false true) = true.
Proof. simpl. reflexivity. Qed.
Example test_nandb4: (nandb true true) = false.
Proof. simpl. reflexivity. Qed.

Definition andb3(b1:bool)(b2:bool)(b3:bool):bool := (andb (andb b1 b2) b3) .

Example test_andb31: (andb3 true true true) = true.
Proof. simpl. reflexivity. Qed.
Example test_andb32: (andb3 false true true) = false.
Proof. simpl. reflexivity. Qed.
Example test_andb33: (andb3 true false true) = false.
Proof. simpl. reflexivity. Qed.
Example test_andb34: (andb3 true true false) = false.
Proof. simpl. reflexivity. Qed.

Check andb.
Check andb3.
Compute ((andb3 true true) true).

Inductive rgb : Type :=
| red
| green
| blue.

Inductive color:Type :=
| white
| black
| primary (p:rgb).

Definition monochrome(c:color):bool := match c with
| white => false
| black => false
| primary _ => false
end.

Definition isred(c:color):bool := match c with
| (primary red) => true
| primary _ => false
| _ => false
end.

Inductive bit:Type :=
| B0
| B1.

Inductive mybble:Type:=
| bits (b0 b1 b2 b3:bit).

Check bits.
Check bits B1.

Definition allzero(nb:mybble):bool := match nb with
| (bits B0 B0 B0 B0) => true
| (bits _ _ _ _) => false
end.

Compute allzero (bits B0 B0 B0 B0).
Compute allzero (bits B0 B0 B0 B1).
Compute (bits B0 B0 B0 B1).

Module NatPlayground.
(* natural number *)
Inductive nat:Type :=
| O
| S (n:nat).

Compute S (S (S O)).

Definition pred(v:nat):nat := match v with
| O => O
| S n => n
end.

Compute pred (S (S O)).

Definition minustwo(v:nat):nat := match v with
| O => O
| S O => O
| S (S n) => n
end.

Definition std_minustwo(v:Datatypes.nat):Datatypes.nat := match v with
| Datatypes.O => Datatypes.O
| Datatypes.S Datatypes.O => Datatypes.O
| Datatypes.S (Datatypes.S n) => n
end.

Check (S (S (S (S O)))).
Compute (std_minustwo 4).

Fixpoint evenb(v:nat):bool := match v with
| O => true
| S O => false
| S (S n') => evenb n'
end.

Definition oddb(v:nat):bool := negb (evenb v).

Example test_oddb1: oddb (S O) = true.
Proof. simpl. reflexivity. Qed.
Example test_oddb2: oddb (S (S (S (S O)))) = false.
Proof. simpl. reflexivity. Qed.

End NatPlayground.

Definition nat_pred(v:Datatypes.nat):Datatypes.nat := match v with
| Datatypes.O => Datatypes.O
| Datatypes.S n' => n'
end.

Definition nat_suc(v:Datatypes.nat):Datatypes.nat := match v with
| Datatypes.O => Datatypes.S Datatypes.O
| n' => Datatypes.S n'
end.

Fixpoint nat_add(a:Datatypes.nat)(b:Datatypes.nat):Datatypes.nat := match a with
| Datatypes.O => b
| Datatypes.S a' => nat_add a' (nat_suc b)
end.

Example test_add1: (nat_add 0 0) = 0.
Proof. simpl. reflexivity. Qed.
Example test_add2: (nat_add 0 1) = 1.
Proof. simpl. reflexivity. Qed.
Example test_add3: (nat_add 0 2) = 2.
Proof. simpl. reflexivity. Qed.
Example test_add4: (nat_add 1 0) = 1.
Proof. simpl. reflexivity. Qed.
Example test_add5: (nat_add 1 1) = 2.
Proof. simpl. reflexivity. Qed.
Example test_add6: (nat_add 1 2) = 3.
Proof. simpl. reflexivity. Qed.
Example test_add7: (nat_add 2 0) = 2.
Proof. simpl. reflexivity. Qed.
Example test_add8: (nat_add 2 1) = 3.
Proof. simpl. reflexivity. Qed.
Example test_add9: (nat_add 2 2) = 4.
Proof. simpl. reflexivity. Qed.

Fixpoint nat_mul_helper(i:Datatypes.nat)(a:Datatypes.nat)(b:Datatypes.nat):Datatypes.nat := match i with
| Datatypes.O => a
| Datatypes.S Datatypes.O => nat_add a b
| Datatypes.S i' => nat_mul_helper i' (nat_add a b) b
end.

Definition nat_mul(a:Datatypes.nat)(b:Datatypes.nat):Datatypes.nat := match a with
| Datatypes.O => Datatypes.O
| Datatypes.S Datatypes.O => b
| Datatypes.S a' => nat_mul_helper (Datatypes.S a') 0 b
end.

Example test_mul1: (nat_mul 0 0) = 0.
Proof. simpl. reflexivity. Qed.
Example test_mul2: (nat_mul 0 1) = 0.
Proof. simpl. reflexivity. Qed.
Example test_mul3: (nat_mul 0 2) = 0.
Proof. simpl. reflexivity. Qed.
Example test_mul4: (nat_mul 1 0) = 0.
Proof. simpl. reflexivity. Qed.
Example test_mul5: (nat_mul 1 1) = 1.
Proof. simpl. reflexivity. Qed.
Example test_mul6: (nat_mul 1 2) = 2.
Proof. simpl. reflexivity. Qed.
Example test_mul7: (nat_mul 2 0) = 0.
Proof. simpl. reflexivity. Qed.
Example test_mul8: (nat_mul 2 1) = 2.
Proof. simpl. reflexivity. Qed.
Example test_mul9: (nat_mul 2 2) = 4.
Proof. simpl. reflexivity. Qed.

Fixpoint factorial(n:Datatypes.nat):Datatypes.nat := match n with
| 0 => 1
| 1 => 1
| 2 => 2
| Datatypes.S n' => nat_mul (Datatypes.S n') (factorial n')
end.

Example test_factorial1: (factorial 3) = 6.
Proof. simpl. reflexivity. Qed.
Example test_factorial2: (factorial 5) = (mult 10 12).
Proof. simpl. reflexivity. Qed.

Theorem plus_0_n: forall n:nat, nat_add 0 n = n.
Proof. intros n. simpl. reflexivity. Qed.

Check 2 > 0.
Theorem mul_0_n : forall n:nat, (mult 0 n) = 0.
Proof. intros n. reflexivity. Qed.

Theorem plus_same_mn : forall m n:nat, m = n -> m + m = n + n.
Proof. intros m n. intros H. rewrite <- H. reflexivity. Qed.

Theorem plus_id_exercise : forall n m o : nat,
  n = m -> m = o -> n + m = m + o.
Proof.
  intros n m o.
  intros H.
  rewrite -> H.
  intros L.
  rewrite -> L.
  reflexivity.
Qed.

Theorem std_plus_0_n:
  forall n:nat, (plus 0 n) = n.
Proof.
  intros n.
  simpl.
  reflexivity.
Qed.

Eval simpl in (plus 0 3).
Theorem plus_n_0:
  forall n:nat, (plus n 0) = n.
Proof.
Admitted.

Fixpoint plus (n : nat) (m : nat) : nat :=
  match n with
    | O => m
    | S n' => S (plus n' m)
  end.

Fixpoint mult (n m : nat) : nat :=
  match n with
    | O => O
    | S n' => plus m (mult n' m)
  end.

(* (S n') + 0 => (plus (S n') 0) => (S (plus n' m)) *)
(* (mult (S n') 1) => plus 1 (mult n' 1) *)
Theorem mul_n_1 :
  forall n:nat, (mult n 1) = n.
Proof.
  intros n.
  induction n as [|n'].
  - reflexivity.
  - simpl.
    rewrite -> IHn'.
    reflexivity.
Qed.

Theorem mult_S_1:
  forall n m:nat, m = S n -> m * (1 + n) = m * m.
Proof.
  simpl.
  intros n m H.
  rewrite <- H.
  reflexivity.
Qed.

(*
Theorem plus_1_neq_0_firsttry :
  forall n:Datatypes.nat ((n + 1) =? 0) = false.
Proof.
  intros n.
  destruct n as [| n'] eqn:E.
  - reflexivity.
  - reflexivity.
Qed.
*)

Module BoolEx.
Inductive bool:Type :=
| true
| false
.

Definition andb(b1:bool)(b2:bool) : bool := match b1 with
| true => b2
| false => false
end.

Theorem andb_true_elim2:
  forall b c:bool, andb b c = true -> c = true.
Proof.
  intros b c.
  destruct b eqn:Eb.
  - simpl. intros H. rewrite -> H. reflexivity.
  - simpl.
    destruct c eqn:Ec.
    + intros H.
      reflexivity.
    + intros H.
      rewrite <- H.
      reflexivity.
Qed.

(*
* andb true c = true
* andb false c = true -> c = true.
* false = true -> c = true.
*)
Definition orb(b1:bool)(b2:bool) : bool := match b1 with
| false => b2
| true => true
end.

Theorem andb_eq_orb :
  forall (b c : bool), (andb b c = orb b c) -> b = c.
Proof.
  intros b c.
  destruct b eqn:Eb.
  - simpl. intros H. rewrite <- H. reflexivity.
  - simpl. intros H. rewrite <- H. reflexivity.
Qed.

(*
* - b = true.
*   (andb true c = orb true c) -> true = c.
*   c = true -> true = c.
* - b = false.  
*   (andb false c = orb false c) -> false = c.
*   false = c -> false = c.
* *)

Theorem identity_fn_applied_twice :
  forall (f : bool -> bool),
    (forall (x : bool), f x = x) ->
    forall (b : bool), f (f b) = b.
Proof.
  intros f.
  intros H.
  intros b.
  destruct b.
  rewrite -> H.
  rewrite -> H.
  reflexivity.
  rewrite -> H.
  rewrite -> H.
  reflexivity.
Qed.

End BoolEx.

Fixpoint eqb (n m : nat) : bool :=
  match n with
  | O => match m with
         | O => true
         | S m' => false
         end
  | S n' => match m with
            | O => false
            | S m' => eqb n' m'
            end
  end.

Theorem zero_nbeq_plus_1 :
  forall n:nat, (eqb 0 (n + 1)) = false.
Proof.
  intros n.
  destruct n eqn:En.
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

(*
* eqb 0 1 = false
* eqb 0 (S n' + 1) = false
* *)
