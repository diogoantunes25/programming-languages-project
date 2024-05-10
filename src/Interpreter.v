From Coq Require Import Lia.
From Coq Require Import Arith.Arith.
From Coq Require Import List.
Import ListNotations.
From FirstProject Require Import Imp Maps.


Inductive interpreter_result : Type :=
  (* final state, final continuation, number of steps remaining *)
  | Success (s: state * (list (state*com)) * nat) 
  | Fail
  | OutOfGas.

(** We can improve the readability of this version by introducing a
    bit of auxiliary notation to hide the plumbing involved in
    repeatedly matching against optional states. *)


Notation "'LetSuc' ( st , cont ) '<==' e1 'in' e2"
  := (match e1 with
          | Success (st,cont,i) => e2
          | Fail => Fail
          | OutOfGas => OutOfGas
       end)
(right associativity, at level 60).


Fixpoint ceval_step (st : state) (c : com) (continuation: list (state * com)) (i : nat)
                    : interpreter_result :=
  match i with
  | O => OutOfGas
  | S i' => match c with
    | <{ skip }> => Success (st, continuation, i')
    | <{ x := y }> => Success ((x !-> aeval st y; st), continuation, i')
    | <{ (c1 !! c2) ; c3 }> =>
      LetSuc ( st' , cont') <== (ceval_step st c1 continuation i') in
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
      else Success (st,continuation, i')
    | <{ c1 !! c2 }> =>
      (* c1 is executed first *)
        LetSuc (st', cont') <== (ceval_step st c1 continuation i') in
          Success (st', (st, c2) :: cont', i')
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
  | OK (st: ((list (string*nat)) * nat))
  | KO
  | OOG.

Open Scope string_scope.
Definition run_interpreter (st: state) (c:com) (n:nat) :=
  match (ceval_step st c [] n) with
    | OutOfGas => OOG
    | Fail => KO
    | Success (st', _, i) => OK ([("X", st' X); ("Y", st' Y); ("Z", st' Z)], (n - i))
  end.

(* Tests are provided to ensure that your interpreter is working for these examples *)

Example test_dsa_1:
  run_interpreter (X !-> 5) <{ X=5 -> X:=10 }> 5 = OK [("X", 10); ("Y", 0); ("Z", 0)].
Proof. auto. Qed.

Example test_dsa_2:
  run_interpreter (X !-> 5) <{ X=5 -> X:=10 }> 5 = OK [("X", 10); ("Y", 0); ("Z", 0)].
Proof. auto. Qed.

Example test_dsa_3:
  run_interpreter (X !-> 5) <{ X=10 -> X:=11 }> 5 = KO.
Proof. auto. Qed.

(* Compute *)
(*   run_interpreter (X !-> 5) <{ *)
(*     if true then (X := 1 !! X := 2) else skip end; *)
(*     Y := X + 1; *)
(*     (X = 2 -> Z := 3) *)
(*   }> 300. *)
(**)
(* (* the size of the continuation to the left doesn't change, but the continuatoin is different*) *)
(* (* Compute *) *)
(* (*   run_interpreter (X !-> 5) <{ *) *)
(* (*     (X:=1 !! X:=2); *) *)
(* (*     ( *) *)
(* (*       (X = 2 -> Z := 3); *) *)
(* (*       (Y:=1 !! Y:=2); *) *)
(* (*       (Y = 1 -> W := 3) *) *)
(* (*     ) *) *)
(* (*     ; *) *)
(* (*     (Z := 4) *) *)
(* (*   }> 300. *) *)
(*   *)
(* Compute *)
(*   run_interpreter (X !-> 0) <{ *)
(*     (X := 1 !! X := 2); *)
(*     Y := X + 1; *)
(*     X = 2 -> Z := 3 *)
(*   }> 20. *)
(**)
(* Compute *)
(*   run_interpreter (X !-> 0) <{ *)
(*     if true then (X := 1 !! X := 2) else skip end; *)
(*     Y := X + 1; *)
(*     X = 2 -> Z := 3 *)
(*   }> 20. *)
(**)
(* Compute *)
(*   run_interpreter (X !-> 0) <{ *)
(*     if true then *)
(*       if true then (X := 1 !! X := 2) else skip end *)
(*     else *)
(*       skip *)
(*     end; *)
(*     Y := X + 1; *)
(*     X = 2 -> Z := 3 *)
(*   }> 10. *)
(**)
(* Compute *)
(*   run_interpreter (X !-> 0) <{ *)
(*   X := 1 !! X :=2; *)
(*   Y := 1 !! Y :=2; *)
(*   Z := 3; *)
(*   Y=2 -> skip; *)
(*   X=2 -> skip *)
(* }> 20. *)
(**)
(* Compute *)
(*   run_interpreter (X !-> 0) <{ *)
(*   X := 1 !! X :=2; *)
(*   W := 4; *)
(*   Y := 1 !! Y :=2; *)
(*   Z := 3; *)
(*   Y=2 -> skip; *)
(*   X=2 -> skip *)
(* }> 20. *)
(**)
(* Unset Printing Notations. *)
(* Definition a132 := (<{ *)
(*     if true then (X := 1 !! X := 2) else skip end; *)
(*     Y := X + 1; *)
(*     X = 2 -> X := 3 *)
(*   }>). *)
(* Print a132. *)
(* Set Printing Notations. *)
(**)
(* Example test_dsa_4: *)
(*   run_interpreter (X !-> 5) <{ X:=7; X=10 -> X:=11 }> 10 = KO. *)
(* Proof. auto. Qed. *)

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
(**)
(* Lemma ceval_step_one_extra: forall i st st' c cont cont', *)
(*   ceval_step st c cont i = Success (st', cont') -> *)
(*   ceval_step st c cont (S i) = Success (st', cont'). *)
(* Proof. *)
(*   intros i. *)
(*   destruct i. *)
(*   - intros. simpl  in H. discriminate. *)
(*   - intros. *)
(*     generalize dependent st. *)
(*     generalize dependent st'. *)
(*     generalize dependent cont. *)
(*     generalize dependent cont'. *)
(*     induction c. *)
(*     -- auto. *)
(*     -- auto. *)
(*     -- intros scont' scont sst' sst. intros H. *)
(**)
(**)
(*   induction c. *)
(*   (* skip *) *)
(*   - destruct i. *)
(*     -- simpl. intros H. discriminate. *)
(*     -- auto.  *)
(*   (* x := a *) *)
(*   - destruct i. *)
(*     -- simpl. intros H. discriminate. *)
(*     -- auto.  *)
(*   (* c1; c2 *) *)
(*   - destruct i. *)
(*     -- simpl. intros H. discriminate. *)
(*     -- intros H. simpl. asser *)
(*        ---   *)
(**)
(*   destruct i. *)
(*   - simpl. intros H. discriminate. *)
(*   - destruct c. *)
(*     -- simpl. intros H. assumption. *)
(*     -- simpl. intros H. assumption. *)
(*     -- intros H.  *)
(*    *)

(*

general idea: for each type of construct, check value of subconstruct and use
i1's result for that
*)

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
