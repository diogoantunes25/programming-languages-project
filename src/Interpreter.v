From Coq Require Import Lia.
From Coq Require Import Arith.Arith.
From Coq Require Import List.
Import ListNotations.
From FirstProject Require Import Imp Maps.


Inductive interpreter_result : Type :=
  | Success (s: state * (list (state*com)))
  | Fail
  | OutOfGas.

(** We can improve the readability of this version by introducing a
    bit of auxiliary notation to hide the plumbing involved in
    repeatedly matching against optional states. *)


Notation "'LetSuc' ( st , cont ) '<==' e1 'in' e2"
  := (match e1 with
          | Success (st,cont) => e2
          | Fail => Fail
          | OutOfGas => OutOfGas
       end)
(right associativity, at level 60).


Fixpoint ceval_step (st : state) (c : com) (continuation: list (state * com)) (i : nat)
                    : interpreter_result :=
  match i with
  | O => OutOfGas
  | S i' => match c with
    | <{ skip }> => Success (st, continuation)
    | <{ x := y }> => Success ((x !-> aeval st y; st), continuation)
    | <{ (c1 !! c2) ; c3 }> =>
      LetSuc ( st' , cont' ) <== (ceval_step st c1 continuation i') in
        (ceval_step st' c3 ((st, <{ c2; c3 }>)::cont') i')
    | <{ c1 ; c2 }> =>
      LetSuc (st', cont') <== (ceval_step st c1 continuation i') in
        (ceval_step st' c2 cont' i')
    | <{ if b then c1 else c2 end }> =>
      if (beval st b)
      then ceval_step st c1 continuation i'
      else ceval_step st c2 continuation i'
    | <{ while b do c1 end }> =>
      if (beval st b)
      then LetSuc (st', cont') <== (ceval_step st c1 continuation i') in
        (ceval_step st' c cont' i')
      else Success (st,continuation)
    | <{ c1 !! c2 }> =>
      (* c1 is executed first *)
        LetSuc (st', cont') <== (ceval_step st c1 continuation i') in
          Success (st', (st, c2) :: cont')
    | <{ b -> c1 }> =>
      if beval st b
      then ceval_step st c1 continuation i'
      else
        match continuation with
        | [] => Fail   
        | (st', c') :: cont' => ceval_step st' c' cont' i' 
        end
    end
  end.

(* Helper functions that help with running the interpreter *)
Inductive show_result : Type :=
  | OK (st: list (string*nat))
  | KO
  | OOG.

Open Scope string_scope.
Definition run_interpreter (st: state) (c:com) (n:nat) :=
  match (ceval_step st c [] n) with
    | OutOfGas => OOG
    | Fail => KO
    | Success (st', _) => OK [("X", st' X); ("Y", st' Y); ("Z", st' Z)]
  end.

(* Tests are provided to ensure that your interpreter is working for these examples *)

Example test_1: 
  run_interpreter (X !-> 5) <{skip}> 1 = OK [("X", 5); ("Y", 0); ("Z", 0)].
Proof. auto. Qed.

Example test_2: 
  run_interpreter (X !-> 5) <{ X:= X+1 }> 1 = OK [("X", 6); ("Y", 0); ("Z", 0)].
Proof. auto. Qed.

Example test_3: 
  run_interpreter (X !-> 5) <{ X:= X+1; X:=X+2; Y:=Y+1 }> 3 = OK [("X", 8); ("Y", 1); ("Z", 0)].
Proof. auto. Qed.

Example test_4: 
  run_interpreter (X !-> 5) <{ X:= X+1; X:=X+2; Y:=Y+1 }> 2 = OOG.
Proof. auto. Qed.

Example test_5:
  run_interpreter (X !-> 5) <{ X:= X+1; X=5 -> skip }> 2 = KO.
Proof. auto. Qed.

Example test_6:
  run_interpreter (X !-> 5) <{ X:= X+1; X=5 -> skip }> 1 = OOG.
Proof. auto. Qed.

Example test_7:
  run_interpreter (X !-> 5) <{ X:= X+1; X=6 -> skip }> 3 = OK [("X", 6); ("Y", 0); ("Z", 0)].
Proof. auto. Qed.

Example test_8:
  run_interpreter (X !-> 5) <{ (X := 1 !! X := 2); (X = 2) -> X:=3 }> 4 = OOG.
Proof. auto. Qed.

Example test_9:
  run_interpreter (X !-> 5) <{ (X := 1 !! X := 2); (X = 2) -> X:=3 }> 5 = OK [("X", 3); ("Y", 0); ("Z", 0)].
Proof. auto. Qed.

Example test_10:
  run_interpreter (X !-> 5) <{ (X:=1 !! (X:=2; Y:=1)); X=2 -> skip }> 5 = OK [("X", 2); ("Y", 1); ("Z", 0)].
Proof. auto. Qed.

Example test_11:
  run_interpreter (X !-> 5) 
  <{  while ~(X = 0) do 
        X:=X-1; Y:=Y+1
      end;
      Y=5 -> skip
  }>
  8 
  = OK [("X", 0); ("Y", 5); ("Z", 0)].
Proof. auto. Qed.

(**
  2.2. TODO: Prove p1_equals_p2. Recall that p1 and p2 are defined in Imp.v
*)

(* The interpreter result of p1 and p2 is the same, i.e, it returns for both cases Success (X !-> 2; st, cont), if and only if in the 
non-deterministic operator (c1 !! c2) we first choose c1 *)

Theorem p1_equals_p2: forall st cont,
  (exists i0,
    (forall i1, i1 >= i0 -> ceval_step st p1 cont i1 =  ceval_step st p2 cont i1)).
Proof.
  intros st cont. exists 5. intros.
  do 6 (destruct i1; try lia; auto).
Qed.

(**
  2.3. TODO: Prove ceval_step_more.
*)

(* For all i1 and i2 such that the interpreter result of ceval_step st c cont i1 is Success(st', cont) and i1 <= i2, then the interpreter result 
of ceval_step st c cont i2 is also Success(st', cont). *)

Theorem ceval_step_more: forall i1 i2 st st' c cont cont',
  i1 <= i2 ->
  ceval_step st c cont i1 = Success (st', cont') ->
  ceval_step st c cont i2 = Success (st', cont').
Proof.
  induction i1 as [|i1 IHi1].
  - simpl ceval_step. intros. discriminate.
  - intros.
    -- destruct i2 as [|i2'] eqn:Ei2.
       --- lia.
       --- assert (Hle: i1 <= i2') by lia. 
           destruct c.
           (* skip *)
           ---- trivial.
           (* x := a *)
           ---- trivial.
           (* c1;c2 *)
           ---- destruct c1.
                ----- simpl. simpl in H0.
                      (* i want to apply IHi1, for that I need to show that is
                      a success *)
                      destruct (ceval_step st _ cont i1) eqn:Eceval.
                      ------ destruct s. apply (IHi1 i2') in Eceval. rewrite Eceval.
                             apply (IHi1 i2') in H0. assumption. assumption. assumption.
                      ------ discriminate.
                      ------ discriminate.
                ----- simpl. simpl in H0.
                      destruct (ceval_step st <{ x := a }> cont i1) eqn:Eceval.
                      ------ destruct s. apply (IHi1 i2') in Eceval. rewrite Eceval.
                             apply (IHi1 i2') in H0. assumption. assumption. assumption.
                      ------ discriminate.
                      ------ discriminate.
                ----- simpl. simpl in H0.
                      destruct (ceval_step st <{ c1_1; c1_2 }> cont i1) eqn:Eceval.
                      ------ destruct s. apply (IHi1 i2') in Eceval. rewrite Eceval.
                             apply (IHi1 i2') in H0. assumption. assumption. assumption.
                      ------ discriminate.
                      ------ discriminate.
                ----- simpl. simpl in H0.
                      destruct (ceval_step st <{ if b then c1_1 else c1_2 end }> cont i1) eqn:Eceval.
                      ------ destruct s. apply (IHi1 i2') in Eceval. rewrite Eceval.
                             apply (IHi1 i2') in H0. assumption. assumption. assumption.
                      ------ discriminate.
                      ------ discriminate.
                ----- simpl. simpl in H0.
                      destruct (ceval_step st <{ while b do c1 end }> cont i1) eqn:Eceval.
                      ------ destruct s. apply (IHi1 i2') in Eceval. rewrite Eceval.
                             apply (IHi1 i2') in H0. assumption. assumption. assumption.
                      ------ discriminate.
                      ------ discriminate.
                ----- simpl. simpl in H0. 
                      destruct (ceval_step st <{ c1_1 !! c1_2; c2 }> cont i1) eqn:Eceval.
                      ------ destruct s. apply (IHi1 i2') in Eceval.
                             destruct (ceval_step st c1_1 cont i1) eqn:Eceval2.
                             ------- destruct s0. apply (IHi1 i2') in Eceval2. rewrite Eceval2.
                                     apply (IHi1 i2') in H0. assumption. assumption. assumption.
                             ------- discriminate.
                             ------- discriminate.
                             ------- assumption.
                      ------ destruct (ceval_step st c1_1 cont i1) eqn:Eceval2.
                             ------- destruct s. apply (IHi1 i2') in Eceval2. rewrite Eceval2.
                                     apply (IHi1 i2') in H0. assumption. assumption. assumption.
                             ------- discriminate.
                             ------- discriminate.
                      ------ destruct (ceval_step st c1_1 cont i1) eqn:Eceval2.
                             ------- destruct s. apply (IHi1 i2') in Eceval2. rewrite Eceval2.
                                     apply (IHi1 i2') in H0. assumption. assumption. assumption.
                             ------- discriminate.
                             ------- discriminate.
                ----- simpl. simpl in H0.
                      destruct (ceval_step st <{ b -> c1 }> cont i1) eqn:Eceval.
                      ------ destruct s. apply (IHi1 i2') in Eceval. rewrite Eceval.
                             apply (IHi1 i2') in H0. assumption. assumption. assumption.
                      ------ discriminate.
                      ------ discriminate.
           (* if b then c1 else c2 end *)
           ---- simpl. destruct (beval st b) eqn: Ebeval.
                ----- apply IHi1. assumption. simpl in H0. rewrite Ebeval in H0. assumption.
                ----- apply IHi1. assumption. simpl in H0. rewrite Ebeval in H0. assumption.
           (* while b do c end *)
           ---- simpl. simpl in H0. destruct (beval st b) eqn: Ebeval.
                (* TODO: understand why destruct of function worked, but not the explicit call *)
                ----- destruct ceval_step eqn: Eceval.
                      ------ destruct s. apply (IHi1 i2') in Eceval. rewrite Eceval.
                             apply (IHi1 i2') in H0. assumption. assumption. assumption.
                      ------ discriminate.
                      ------ discriminate.
                ----- assumption.
          (* c1 !! c2 *)
           ---- simpl. simpl in H0. destruct ceval_step eqn: Eceval.
                (* First command succeded *)
                ----- destruct s. apply (IHi1 i2') in Eceval. rewrite Eceval. assumption. assumption.
                (* First command failed/ran out of gas *)
                ----- discriminate.
                ----- discriminate.
           ---- simpl. simpl in H0. destruct (beval st b).
                ----- apply (IHi1 i2') in H0. assumption. assumption.
                ----- destruct cont.
                      ------ discriminate.
                      ------ destruct p. apply (IHi1 i2') in H0. assumption. assumption.
Qed.
