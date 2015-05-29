

Fixpoint plus (n m : nat) : nat :=
	match n with
		| O => m
		| S n' => S (plus n' m)
	end.

Fixpoint mul (n m : nat) : nat :=
	match n with
		| O => O
		| S O => m
		| S n' => (plus m (mul n' m))
	end.



Fixpoint factoria (n : nat) : nat :=
	match n with
		| O => (S O)
		| S n' => (mul n (factoria n'))
	end.

(*Notation "x + y" := (plus x y) : nat_scope.*)


Eval compute in (mul 3 8).
Eval compute in (factoria 3).
Eval compute in (22 + 11).
Eval compute in (eq 22 22).
