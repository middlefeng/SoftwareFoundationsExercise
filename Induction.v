

Require Basic.


Theorem andb_true_elim2 : forall b c : bool,
	andb b c = true -> c = true.
Proof.

	intros b c.

	destruct b.

		(* b - true *)
		simpl.
		intros H.
		rewrite H.	
		reflexivity.

		(* b - false *)
		simpl.

		destruct c.

			reflexivity.

			simpl.
			intros H.
			rewrite H.
			reflexivity.

Qed.

