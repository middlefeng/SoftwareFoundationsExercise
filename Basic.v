

Inductive bool : Type :=
	| true : bool
	| false : bool.


Definition andb (a b : bool) : bool :=
	match a with
		| true => b
		| false => false
	end.
