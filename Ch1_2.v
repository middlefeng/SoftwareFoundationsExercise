

Theorem plus_O_n : forall n : nat, 0 + n = n.
Proof.
  intro n. reflexivity. Qed.

Theorem plus_1_l : forall n:nat, 1 + n = S n.
Proof.
  intros n. reflexivity. Qed.


Theorem plus_id_example : forall n m:nat,
	n = m -> n + n = m + m.
Proof.
	intros n.
	intros m.
	intros N1.
	rewrite -> N1.
	reflexivity. Qed.


Theorem plus_id_exercise : forall n m o : nat,
	n = m -> m = o -> n + m = m + o.
Proof.
	intros n m o.
	intros M N.
	rewrite M.
	rewrite N.
	reflexivity. Qed.


Theorem mult_0_plus : forall n m : nat,
  	(0 + n) * m = n * m.
Proof.
  	intros n m.
	rewrite -> plus_O_n.
	reflexivity. Qed.



Theorem mult_S_1 : forall n m : nat,
	m = S n ->
	m * (1 + n) = m * m.
Proof.
  	intros n m.
  	intros H.
  	rewrite -> H.
  	reflexivity. Qed.



Fixpoint beq_nat (n m : nat) : bool :=
	match n with
		| O => 		match m with
						| O => true
						| S m' => false
					end
		| S n' => 	match m with
            			| O => false
						| S m' => beq_nat n' m'
					end
	end.

Eval compute in (beq_nat 0 0).
Eval compute in (beq_nat 0 1).


Theorem plus_1_neq_0_firsttry : forall n : nat,
	beq_nat (n + 1) 0 = false.
Proof.
	intros n.
  	destruct n as [| n'].
    reflexivity.
    reflexivity.
Qed.






Theorem zero_nbeq_plus_1 : forall n : nat,
	beq_nat 0 (n + 1) = false.
Proof.
	intros n.
	destruct n as [ | n'].
	reflexivity.
	reflexivity.
Qed.


Definition andb (a b : bool) : bool :=
	match a with
		| true => b
		| false => false
	end.


Definition orb (a b : bool) : bool :=
	match a with
		| false => b
		| true => true
	end.



Theorem andb_false : forall b c : bool,
	c = false ->
	(andb b c) = false.
Proof.
	intros b c.
	intros H.
	rewrite -> H.
	destruct b.
	reflexivity. reflexivity.
Qed.

Theorem andb_true : forall b c : bool,
	c = true ->
	(andb b c) = b.
Proof.
	intros b c.
	intros H.
	rewrite -> H.
	destruct b.
	reflexivity. reflexivity.
Qed.


Theorem orb_true : forall b c : bool,
	c = true ->
	(orb b c) = true.
Proof.
	intros b c.
	intros H.
	rewrite -> H.
	destruct b.
	reflexivity. reflexivity.
Qed.

Theorem orb_false : forall b c : bool,
	c = false ->
	(orb b c) = b.
Proof.
	intros b c.
	intros H.
	rewrite -> H.
	destruct b.
	reflexivity. reflexivity.
Qed.



Theorem andb_eq_true : forall b : bool,
	(andb b true) = (orb b true) ->
	b = true.
Proof.
	intros b.
	destruct b.
		reflexivity.
		simpl.
		intros H.
		rewrite -> H.
		reflexivity.
Qed.



Theorem andb_eq_c_true : forall b c : bool,
	c = true ->
	(andb b c) = (orb b c) ->
	b = true.
Proof.
	intros b c.
	simpl.
	intros H.
	rewrite -> H.
	destruct b.
		
		reflexivity.

		simpl.
		intros L.
		rewrite -> L.
		reflexivity.
Qed.



Theorem andb_eq_orb :  forall (b c : bool),
  	(andb b c = orb b c) ->
  	b = c.
Proof.
	intros b c.
	destruct b.
	destruct c.
		(* b - true, c - true *)
		reflexivity.
		
		(* b - true, c - false *)
		simpl.
		intro H.
		rewrite -> H.
		reflexivity.
		
		(* b - false, c - true *)
		simpl.
		intro H.
		rewrite -> H.
		reflexivity.
Qed.






Theorem identity_fn_applied_twice : forall (f : bool -> bool), 
	(forall (x : bool), f x = x) ->
  	forall (b : bool), f (f b) = b.
Proof.
	intros f.
	intros H.
	intros b.

		rewrite -> H.
		rewrite -> H.
		reflexivity.

Qed.












