From LF Require Export Induction.

Module NatList.

Inductive natprod : Type := 
| pair (n1 n2 : nat).

Check pair.
Check pair 3.
Check pair 3 5.

Definition fst(p:natprod):nat := match p with
| pair x y => x
end.

Definition snd(p:natprod):nat := match p with
| pair x y => y
end.

Compute fst (pair 1 2).
Compute snd (pair 1 2).

Notation "( x , y )" := (pair x y).

Compute fst (1, 2).

(*
Fixpoint minus(p:natprod):nat := match p with
| pair O _ => O
| pair (S x) O => (S x)
| pair (S x) (S y) => minus (pair x y)
end.
*)

Definition bad_fst(p: natprod):nat :=
  match p with
  | (x, y) => x
  end.

Theorem surjective_pairing' :
  forall (n m:nat), (n, m) = (fst (n, m), snd (n, m)).
Proof.
  reflexivity.
Qed.

Theorem surjective_pairing_stuck:
  forall p:natprod, p = (fst p, snd p).
Proof.
  destruct p as [x y].
  - reflexivity.
Qed.

Inductive natlist :=
| nil
| cons (n:nat) (l:natlist).

Definition mylist := (cons 2 (cons 1 nil)).

Notation "x :: l" := (cons x l) (at level 60, right associativity).

Compute 1 :: nil.
Compute 1 :: 2 :: nil.
Compute 1 + 3 :: 2 :: nil.

Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

Compute [1;2;3;4].

Fixpoint repeat(n count:nat):natlist :=
  match count with
  | O => nil
  | S count' => n :: (repeat n count')
  end.

Fixpoint length(l:natlist):nat :=
  match l with
  | nil => O
  | cons e l => 1 + length l
  end.

Fixpoint app(l1 l2:natlist):natlist :=
  match l1 with
  | nil => l2
  | cons e l => cons e (app l l2)
  end.

Notation "x ++ y" := (app x y).

Compute repeat 3 10.
Compute length (repeat 3 10).
Compute (repeat 3 10) ++ (repeat 4 3).

Theorem app_assoc:
  forall l1 l2 l3:natlist, l1 ++ (l2 ++ l3) = (l1 ++ l2) ++ l3.
Proof.
  induction l1 as [|e l IHl].
  - (* Case l1 = nil *)
    reflexivity.
  - (* Case l1 = cons e l *)
    (* IHl: l ++ (l2 ++ l3) = (l + l2) ++ l3 *)
    (* (cons e l) ++ (l2 ++ l3) = ((cons e l) ++ l2) ++ l3 *)
    simpl.
    (* e :: l ++ l2 ++ l3 = e :: (l ++ l2) ++ l3 *)
    intros l2 l3.
    rewrite <- (IHl l2 l3).
    reflexivity.
Qed.

End NatList.
