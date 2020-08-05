Set Warnings "-notation-overridden,-parsing".
From LF Require Export Lists.

Module ListWorkbench.
Inductive list(T:Type):Type :=
| nil
| cons (e:T) (l:list T)
.

Inductive boollist:Type :=
| boolnil
| boolcons (e:bool) (l:boollist)
.

Check boolnil.
Check boolcons.
Check list.
Check nil.
Check nil nat.
Check cons.
Check cons nat.
Check cons nat 2 (nil nat).
Check cons nat 2 (cons nat 1 (nil nat)).
Definition nat_nil := nil nat.
Definition nat_cons := cons nat.
Check nat_cons 2 (nat_cons 1 (nat_nil)).

Fixpoint repeat(T:Type) (x:T) (count:nat): list T :=
  match count with
  | 0 => nil T
  | S n' => cons T x (repeat T x n')
  end.

Compute repeat nat 12 3.

Example test_repeat1 :
  repeat nat 4 2 = cons nat 4 (cons nat 4 (nil nat)).
Proof. reflexivity. Qed.

Example test_repeat2 :
  repeat bool false 1 = cons bool false (nil bool).
Proof. reflexivity. Qed.

Arguments nil {T}.
Arguments cons {T} _ _.
Arguments repeat {T} _ _.

Compute repeat true 3.

Fixpoint repeat'{T:Type} (x:T) (count:nat): list T :=
  match count with
  | 0 => nil
  | S n' => cons x (repeat x n')
  end.

Compute repeat' true 3.

Check @nil.
Check nil.
Definition mytest(l:list nat):list nat := @nil nat.

Arguments list {T}.
Definition mytest'(l:@list nat):@list nat := @nil nat.

End ListWorkbench.
