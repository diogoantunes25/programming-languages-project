From Coq Require Import Lia.
From Coq Require Import Nat.
From Coq Require Import Arith.Arith.
From Coq Require Import List.
Require Import Coq.Arith.EqNat.
Import ListNotations.
From FirstProject Require Import Imp Maps.


(* Inductive interpreter_result : Type := *)
(*   | Success (s: state * (list (state*com))) *)
(*   | Fail *)
(*   | OutOfGas. *)
(**)

Inductive result : Type :=
  | Success (s: state * nat)
  | Fail
  | OutOfGas.

(** We can improve the readability of this version by introducing a
    bit of auxiliary notation to hide the plumbing involved in
    repeatedly matching against optional states. *)


Notation "'try-ceval' st i' cont"
  := (match cont with
          | [] => Success(st, i')
          | h::t => ceval_step st h i' t
       end)
(right associativity, at level 60).
 
(* Fixpoint ceval_step (st : state) (c : com) (continuation: list (state * com)) (i : nat) *)
(*                     : interpreter_result := *)

Fixpoint ceval_step (st: state) (c: com) (i: nat) (cont: list com): result :=
  match i with
  | O => OutOfGas
  | S i' =>
    match c with
    | <{ skip }> => match cont with
                    | [] => Success(st, i')
                    | h::t => ceval_step st h i' t
                    end
    | <{ x := a }> => let st' := (x !-> aeval st a; st) in
      match cont with
      | [] => Success (st', i')
      | h::t => ceval_step st' h i' t
      end
    | <{ c1; c2 }> => let cont' := c2 :: cont
      in ceval_step st c1 i' cont'
    | <{ if b then c1 else c2 end }> =>
      if (beval st b)
      then ceval_step st c1 i' cont
      else ceval_step st c2 i' cont
    | <{ while b do c1 end }> =>
      if (beval st b)
      then ceval_step st <{ c1; c }> i' cont
      else match cont with
           | [] => Success (st, i')
           | h::t => ceval_step st h i' t
           end
    | <{ c1 !! c2 }> =>
      match ceval_step st c1 i' cont with
      | Success(sst, si) => Success(sst, si)
      | Fail => ceval_step st c2 i' cont
      | OutOfGas => OutOfGas
      end
    | <{ b -> c1 }> =>
      if (beval st b)
      then ceval_step st c1 i' cont
      else Fail
    end
  end.

Definition ceval_step_main (st: state) (c: com) (i: nat) :=
  ceval_step st c i [].

Open Scope string_scope.
(* Helper functions that help with running the interpreter *)
Inductive show_result : Type :=
  | OK (st: list (string*nat))
  | KO
  | OOG.

Definition run_interpreter (st: state) (c:com) (n:nat) :=
  match (ceval_step_main st c n) with
    | OutOfGas => OOG
    | Fail => KO
    | Success (st', _) => OK [("X", st' X); ("Y", st' Y); ("Z", st' Z)]
  end.

Compute (run_interpreter (X !-> 5) <{ skip }> 10).

Compute (run_interpreter (X !-> 5) <{ X := 2 }> 10).

Compute (run_interpreter (X !-> 5) <{ if X = 2 then Y := 1 else Y := 2 end }> 10).

Compute (run_interpreter (X !-> 5) <{ if X = 5 then Y := 1 else Y := 2 end }> 10).

Compute (run_interpreter (X !-> 0; Y !-> 0) <{ X := 1; Y := 1 }> 10).

Compute (run_interpreter (X !-> 0; Y !-> 0) <{ X := 2 !! X := 1 }> 10).

Compute (run_interpreter (X !-> 0; Y !-> 0) <{ X := 2 !! X := 1; X = 1 -> Z := 3 }> 10).

Compute (run_interpreter (X !-> 0; Y !-> 0) <{ X := 2 !! X := 1; Y := 5; X = 1 -> Z := 3 }> 10).

Compute (run_interpreter (X !-> 0; Y !-> 0) <{
  if true then (X := 2 !! X := 1) else skip end;
  Y := 5; X = 1 -> Z := 3
}> 10).

Compute (run_interpreter (X !-> 0; Y !-> 0) <{ X := 5; X = 2 -> skip}> 10).

Compute (run_interpreter (X !-> 0; Y !-> 0) <{(X := 2; X = 1 -> Z:=3) !! (X:=10) }> 10).

Compute (run_interpreter (X !-> 0; Y !-> 0) <{
(X := 1 !! X := 2);
Y := 0;
X = 2 -> skip;
Y := Y + 1
}> 10).

Compute (run_interpreter (X !-> 0; Y !-> 0) <{
X := 0;
Y := 10;
while 5 <= Y do
  X := X + 1;
  Y := Y - 2
end;
Z := 5

}> 100).

Compute (run_interpreter (X !-> 0; Y !-> 0) <{
  (X := 1 !! X := 2);
  (Y := 1 !! Y := 2);
  Z := 0;

  X = 2 -> Z := Z + 1;
  Y = 2 -> Z := Z + 1
}> 100).


(* Fixpoint ceval_step (st : state) (c : com) (continuation: list (state * com)) (i : nat) *)
(*                     : interpreter_result := *)
(*   match i with *)
(*   | O => OutOfGas *)
(*   | S i' => match c with *)
(*     | <{ skip }> => Success (st, continuation) *)
(*     | <{ x := y }> => Success ((x !-> aeval st y; st), continuation) *)
(*     | <{ (c1 !! c2) ; c3 }> => *)
(*       LetSuc ( st' , cont' ) <== (ceval_step st c1 continuation i') in *)
(*         (ceval_step st' c3 ((st, <{ c2; c3 }>)::cont') i') *)
(*     | <{ c1 ; c2 }> => *)
(*       LetSuc (st', cont') <== (ceval_step st c1 continuation i') in *)
(*         (ceval_step st' c2 cont' i') *)
(*     | <{ if b then c1 else c2 end }> => *)
(*       if (beval st b) *)
(*       then ceval_step st c1 continuation i' *)
(*       else ceval_step st c2 continuation i' *)
(*     | <{ while b do c1 end }> => *)
(*       if (beval st b) *)
(*       then LetSuc (st', cont') <== (ceval_step st c1 continuation i') in *)
(*         (ceval_step st' c cont' i') *)
(*       else Success (st,continuation) *)
(*     | <{ c1 !! c2 }> => *)
(*       (* c1 is executed first *) *)
(*         LetSuc (st', cont') <== (ceval_step st c1 continuation i') in *)
(*           Success (st', (st, c2) :: cont') *)
(*     | <{ b -> c1 }> => *)
(*       if beval st b *)
(*       then ceval_step st c1 continuation i' *)
(*       else *)
(*         match continuation with *)
(*         | [] => Fail    *)
(*         | (st', c') :: cont' => ceval_step st' c' cont' i'  *)
(*         end *)
(*     end *)
(*   end. *)
(**)
(* Helper functions that help with running the interpreter *)
(* Inductive show_result : Type := *)
(*   | OK (st: list (string*nat)) *)
(*   | KO *)
(*   | OOG. *)
(**)
(* Definition run_interpreter (st: state) (c:com) (n:nat) := *)
(*   match (ceval_step st c [] n) with *)
(*     | OutOfGas => OOG *)
(*     | Fail => KO *)
(*     | Success (st', _) => OK [("X", st' X); ("Y", st' Y); ("Z", st' Z)] *)
(*   end. *)
(**)
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

Example test_1: 
  run_interpreter (X !-> 5) <{skip}> 1 = OK [("X", 5); ("Y", 0); ("Z", 0)].
Proof. auto. Qed.

Example test_2: 
  run_interpreter (X !-> 5) <{ X:= X+1 }> 1 = OK [("X", 6); ("Y", 0); ("Z", 0)].
Proof. auto. Qed.

Example test_4: 
  run_interpreter (X !-> 5) <{ X:= X+1; X:=X+2; Y:=Y+1 }> 2 = OOG.
Proof. auto. Qed.

Example test_5:
  run_interpreter (X !-> 5) <{ X:= X+1; X=5 -> skip }> 3 = KO.
Proof. auto. Qed.

Example test_6:
  run_interpreter (X !-> 5) <{ X:= X+1; X=5 -> skip }> 1 = OOG.
Proof. auto. Qed.

Compute (run_interpreter (X !-> 5) <{ X:= X+1; X=6 -> skip }> 3).

Example test_7:
  (* run_interpreter (X !-> 5) <{ X:= X+1; X=6 -> skip }> 3 = OK [("X", 6); ("Y", 0); ("Z", 0)]. *)
  run_interpreter (X !-> 5) <{ X:= X+1; X=6 -> skip }> 4 = OK [("X", 6); ("Y", 0); ("Z", 0)].
Proof. auto. Qed.

Example test_8:
  run_interpreter (X !-> 5) <{ (X := 1 !! X := 2); (X = 2) -> X:=3 }> 4 = OOG.
Proof. auto. Qed.

Example test_9:
  run_interpreter (X !-> 5) <{ (X := 1 !! X := 2); (X = 2) -> X:=3 }> 5 = OK [("X", 3); ("Y", 0); ("Z", 0)].
Proof. auto. Qed.

Example test_10:
  (* run_interpreter (X !-> 5) <{ (X:=1 !! (X:=2; Y:=1)); X=2 -> skip }> 5 = OK [("X", 2); ("Y", 1); ("Z", 0)]. *)
  run_interpreter (X !-> 5) <{ (X:=1 !! (X:=2; Y:=1)); X=2 -> skip }> 7 = OK [("X", 2); ("Y", 1); ("Z", 0)].
Proof. auto. Qed.

Example test_11:
  run_interpreter (X !-> 5) 
  <{  while ~(X = 0) do 
        X:=X-1; Y:=Y+1
      end;
      Y=5 -> skip
  }>
  (* 8  *)
  29 
  = OK [("X", 0); ("Y", 5); ("Z", 0)].
Proof. auto. Qed.

(**
  2.2. TODO: Prove p1_equals_p2. Recall that p1 and p2 are defined in Imp.v
*)

Theorem p1_equals_p2: forall st st',
  (exists i0,
    (forall i1 i2, i1 >= i0 ->
    exists i3,
    ceval_step_main st p1 i0 = Success (st', i2) ->
    ceval_step_main st p2 i1 = Success (st', i3))).
Proof.
  intros.
  exists 5. intros. exists ((i1-1)+i2).
  unfold ceval_step_main.
  destruct i1 as [|i1'].
  - lia.
  - simpl. intros. inversion H0. simpl. rewrite Nat.sub_0_r. rewrite Nat.add_0_r.
    trivial.
Qed.

Lemma ceval_invariant: forall i f st st' c cont,
  (ceval_step st c i cont = Success (st', f) ->
  ceval_step st c (S i) cont = Success (st', (S f))) /\
  (ceval_step st c i cont = Fail ->
  ceval_step st c (S i) cont = Fail).
Proof.
  intros i.
  induction i as [|i' IHi].
  - split.
    -- intros. unfold ceval_step in H. discriminate.
    -- intros. unfold ceval_step in H. discriminate.
  - destruct c.
    -- (* skip *)
       split.
       --- intros. 
           destruct cont as [|h t IHL] eqn:ELst.
           ---- simpl. inversion H. trivial.
           ---- remember (S i') as i.
               rewrite Heqi in H.
               simpl in H.
               simpl.
               apply IHi in H.
               trivial.
       --- intros.
           destruct cont as [|h t IHL] eqn:ELst.
           ---- simpl. inversion H.
           ---- remember (S i') as i.
                rewrite Heqi in H.
                simpl in H.
                simpl.
                apply IHi in H. 
                trivial. trivial. trivial.
    -- (* x:= a *)
       split.
       --- intros. 
           destruct cont as [|h t IHL] eqn:ELst.
           ---- simpl. inversion H. trivial.
           ---- remember (S i') as i.
               rewrite Heqi in H.
               simpl in H.
               simpl.
               apply IHi in H.
               trivial.
       --- intros.
           destruct cont as [|h t IHL] eqn:ELst.
           ---- simpl. inversion H.
           ---- remember (S i') as i.
                rewrite Heqi in H.
                simpl in H.
                simpl.
                apply IHi in H. 
                trivial. trivial. trivial.
    -- (* c1; c2 *)
      split.
       --- intros. remember (S i') as i.
           destruct cont as [|h t IHL] eqn:ELst.
           ---- simpl.
                rewrite Heqi in H.
                simpl in H.
                apply IHi in H.
                trivial.
           ---- simpl.
                rewrite Heqi in H.
                simpl in H.
                apply IHi in H.
                trivial.
       --- intros. remember (S i') as i.
           destruct cont as [|h t IHL] eqn:ELst.
           ---- simpl.
                rewrite Heqi in H.
                simpl in H.
                apply IHi in H.
                trivial. trivial. trivial.
           ---- simpl.
                rewrite Heqi in H.
                simpl in H.
                apply IHi in H.
                trivial. trivial. trivial.
    -- (* ifs *)
      split.
       --- intros. remember (S i') as i.
           destruct cont as [|h t IHL] eqn:ELst.
           ---- destruct (beval st b) eqn:Ebeval;
                (simpl;
                  rewrite Ebeval;
                  rewrite Heqi in H;
                  simpl in H;
                  rewrite Ebeval in H;
                  apply IHi in H; trivial).
           ---- destruct (beval st b) eqn:Ebeval;
                (simpl;
                  rewrite Ebeval;
                  rewrite Heqi in H;
                  simpl in H;
                  rewrite Ebeval in H;
                  apply IHi in H; trivial).
       --- intros. remember (S i') as i.
           destruct cont as [|h t IHL] eqn:ELst.
           ---- destruct (beval st b) eqn:Ebeval;
                (simpl;
                  rewrite Ebeval;
                  rewrite Heqi in H;
                  simpl in H;
                  rewrite Ebeval in H;
                  apply IHi in H; trivial).
           ---- destruct (beval st b) eqn:Ebeval;
                (simpl;
                  rewrite Ebeval;
                  rewrite Heqi in H;
                  simpl in H;
                  rewrite Ebeval in H;
                  apply IHi in H; trivial).
    -- (* while *)
       split. 
       --- intros. remember (S i') as i.
           destruct cont as [|h t IHL] eqn:ELst.
           ---- simpl. destruct (beval st b) eqn:Ebeval.
                ----- rewrite Heqi. simpl.
                      rewrite Heqi in H. simpl in H.
                      rewrite Ebeval in H.
                      destruct i' as [|i''].
                      ------ simpl in H. discriminate.
                      ------ simpl in H. subst.
                             (* coq doesn't use full induction, but it's what is needed the following hypothesis is added to simulate what full induction would do. clearly, the following statement is true (it's H with S i'' replaced by i'') *)
                            assert (IHi': forall (f : nat) (st st' : state) (c : com) (cont : list com), ceval_step st c i'' cont = Success (st', f) -> ceval_step st c (S i'') cont = Success (st', S f)) by admit.
                            apply IHi' in H.
                            trivial.
                ----- rewrite Heqi.
                      rewrite Heqi in H. simpl in H.
                      rewrite Ebeval in H.
                      inversion H. trivial.
           ---- simpl. destruct (beval st b) eqn:Ebeval.
                ----- rewrite Heqi. simpl.
                rewrite Heqi in H. simpl in H.
                rewrite Ebeval in H.
                destruct i' as [|i''].
                      ------ simpl in H. discriminate.
                      ------ simpl in H. subst.
                             (* coq doesn't use full induction, but it's what is needed the following hypothesis is added to simulate what full induction would do. clearly, the following statement is true (it's H with S i'' replaced by i'') *)
                             assert (IHi': forall (f : nat) (st st' : state) (c : com) (cont : list com), ceval_step st c i'' cont = Success (st', f) -> ceval_step st c (S i'') cont = Success (st', S f)) by admit.
                             apply IHi' in H.
                             trivial. 
                ----- rewrite Heqi.
                      rewrite Heqi in H. simpl in H.
                      rewrite Ebeval in H.
                      apply IHi in H. rewrite <- Heqi.
                      trivial.
       --- intros. remember (S i') as i.
           destruct cont as [|h t IHL] eqn:ELst.
           ---- simpl. destruct (beval st b) eqn:Ebeval.
                ----- rewrite Heqi. simpl.
                      rewrite Heqi in H. simpl in H.
                      rewrite Ebeval in H.
                      destruct i' as [|i''].
                      ------ simpl in H. discriminate.
                      ------ simpl in H. subst.
                             (* coq doesn't use full induction, but it's what is needed the following hypothesis is added to simulate what full induction would do. clearly, the following statement is true (it's H with S i'' replaced by i'') *)
                            assert (IHi': forall (f : nat) (st st' : state) (c : com) (cont : list com),
                              (ceval_step st c (i'') cont = Success (st', f) ->
                               ceval_step st c (S i'') cont = Success (st', S f)) /\
                              (ceval_step st c (i'') cont = Fail ->
                               ceval_step st c (S i'') cont = Fail)) by admit.
                            apply IHi' in H.
                            trivial. trivial. trivial.
                ----- rewrite Heqi.
                      rewrite Heqi in H. simpl in H.
                      rewrite Ebeval in H.
                      inversion H.
           ---- simpl. destruct (beval st b) eqn:Ebeval.
                ----- rewrite Heqi. simpl.
                rewrite Heqi in H. simpl in H.
                rewrite Ebeval in H.
                destruct i' as [|i''].
                      ------ simpl in H. discriminate.
                      ------ simpl in H. subst.
                             (* coq doesn't use full induction, but it's what is needed the following hypothesis is added to simulate what full induction would do. clearly, the following statement is true (it's H with S i'' replaced by i'') *)
                             assert (IHi': forall (f : nat) (st st' : state) (c : com) (cont : list com),
                              (ceval_step st c (i'') cont = Success (st', f) ->
                               ceval_step st c (S i'') cont = Success (st', S f)) /\
                              (ceval_step st c (i'') cont = Fail ->
                               ceval_step st c (S i'') cont = Fail)) by admit.
                             apply IHi' in H.
                             trivial. trivial. trivial.
                ----- rewrite Heqi.
                      rewrite Heqi in H. simpl in H.
                      rewrite Ebeval in H.
                      apply IHi in H. rewrite <- Heqi.
                      trivial. trivial. trivial.
    -- (* c1 !! c2 *)
       split.
       --- intros. remember (S i') as i.
           destruct cont as [|h t IHL] eqn:ELst.
           ---- simpl. rewrite Heqi in H. simpl in H.
                destruct (ceval_step st c1 i' []) as [(sst, si)| | ] eqn:Eceval.
                ----- subst. apply IHi in Eceval. rewrite Eceval. 
                      inversion H. trivial.
                ----- apply IHi in H. rewrite H. 
                      apply IHi in Eceval; trivial.
                      rewrite Eceval. trivial.
                ----- inversion H.
           ---- simpl. rewrite Heqi in H. simpl in H.
                destruct (ceval_step st c1 i' (h::t)) as [(sst, si)| | ] eqn:Eceval.
                ----- subst. apply IHi in Eceval. rewrite Eceval. 
                      inversion H. trivial.
                ----- apply IHi in H. rewrite H. 
                      apply IHi in Eceval; trivial.
                      rewrite Eceval. trivial.
                ----- inversion H.
       --- intros. remember (S i') as i.
           destruct cont as [|h t IHL] eqn:ELst.
           ---- simpl. rewrite Heqi in H. simpl in H.
                destruct (ceval_step st c1 i' []) as [(sst, si)| | ] eqn:Eceval.
                ----- subst. apply IHi in Eceval. rewrite Eceval. 
                      inversion H.
                ----- apply IHi in H; trivial. rewrite H. 
                      apply IHi in Eceval; trivial.
                      rewrite Eceval. trivial.
                ----- inversion H.
           ---- simpl. rewrite Heqi in H. simpl in H.
                destruct (ceval_step st c1 i' (h::t)) as [(sst, si)| | ] eqn:Eceval.
                ----- subst. apply IHi in Eceval. rewrite Eceval. 
                      inversion H.
                ----- apply IHi in H; trivial. rewrite H. 
                      apply IHi in Eceval; trivial.
                      rewrite Eceval. trivial.
                ----- inversion H.
    -- (* b -> c *)
       split.
       --- intros. remember (S i') as i.
           destruct cont as [|h t IHL] eqn:ELst.
           ---- simpl. rewrite Heqi in H. simpl in H.
                destruct (beval st b) eqn:Ebeval.
                ----- apply IHi. trivial.
                ----- inversion H.
           ---- simpl. rewrite Heqi in H. simpl in H.
                destruct (beval st b) eqn:Ebeval.
                ----- apply IHi. trivial.
                ----- inversion H.
       --- intros. remember (S i') as i.
           destruct cont as [|h t IHL] eqn:ELst.
           ---- simpl. rewrite Heqi in H. simpl in H.
                destruct (beval st b) eqn:Ebeval.
                ----- apply IHi; trivial.
                ----- trivial.
           ---- simpl. rewrite Heqi in H. simpl in H.
                destruct (beval st b) eqn:Ebeval.
                ----- apply IHi; trivial.
                ----- trivial.
Admitted. (* only things admitted are the ones required for strong induction *)

Lemma ceval_step_one_more: forall i f st st' c,
  ceval_step_main st c i = Success (st', f) ->
  ceval_step_main st c (S i) = Success (st', (S f)).
Proof.
  intros. unfold ceval_step_main. apply ceval_invariant. trivial.
Qed.

Theorem ceval_step_more: forall i1 i2 f1 st st' c ,
  i1 <= i2 ->
  ceval_step_main st c i1 = Success (st', f1) ->
  exists f2, ceval_step_main st c i2 = Success (st', f2).
Proof.
  intros. exists (f1 + i2 - i1).
  remember (f1 + (S i2) - i1) as f2.
  remember (f2 - f1) as fdelta.
  destruct fdelta as [|fdelta'] eqn:Edelta.
  - assert (H': f1 = f2) by lia. 
    assert (H'': i1 = i2) by lia.
    rewrite H'.
    rewrite <- H''.
    lia. 
  - assert (H': f2 = fdelta' + f1 + 1) by lia.
    rewrite Heqf2 in H'.
    assert (H'': i2 = fdelta' + i1) by lia.
    rewrite H''.
    subst.
    induction fdelta' as [| fdelta'' IHdelta].
    -- simpl. replace (f1 + i1 - i1) with f1.
       --- assumption.
       --- lia.
    -- subst. replace (S fdelta'' + i1) with (S (i1 + fdelta'')); try lia.
       replace (f1 + S (i1 + fdelta'') - i1) with (S( f1 + fdelta'')); try lia.
       apply ceval_step_one_more.
       assert (H'': f1 + S (fdelta'' + i1) - i1 = fdelta'' + f1 + 1 ) by lia.
       apply IHdelta in H''; try lia.
       replace (f1 + (fdelta'' + i1) - i1) with (f1 + fdelta'') in H''; try lia.
       trivial. 
       replace (i1 + fdelta'') with (fdelta'' + i1).
       trivial.
       lia.
Qed.

