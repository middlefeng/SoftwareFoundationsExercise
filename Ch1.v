


Inductive bool : Type :=
	| true : bool
	| false : bool.


(*Inductive nat : Type :=
	| O : nat
	| S : nat -> nat.*)

Definition pred (n : nat) : nat :=
	match n with
		| O => O
		| S n' => n'
	end.

Fixpoint evenb (n:nat) : bool :=
	match n with
		| O => true
		| S O => false
		| S (S n') => evenb n'
	end.

Eval compute in S.
Eval compute in O.
Eval compute in (S O).
Eval compute in (S (S O)).
Eval compute in (pred (S (S O))).
Eval compute in 4.


Eval compute in (evenb 4).

(*Check S.*)


Fixpoint plus (n m : nat) : nat :=
	match n with
		| O => m
		| S n' => S (plus n' m)
	end.


Eval compute in (plus 56 66).

