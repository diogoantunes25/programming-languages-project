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

(*
Notation "'LETOPT' x <== e1 'IN' e2"
  := (match e1 with
          | Some x => e2
          | None => None
       end)
(right associativity, at level 60).
*)

(**
  2.1. TODO: Implement ceval_step as specified. To improve readability,
             you are strongly encouraged to define auxiliary notation.
             See the notation LETOPT in the ImpCEval chapter.
*)

(* LETINTRES -> Let interpreter result. Aux notation for ceval_step *)
Notation "'LETINTRES' ( st , cont ) <== e1 'IN' e2"
  := (match e1 with
        | Success (st, cont) => e2
        | Fail => Fail
        | OutOfGas => OutOfGas
        end)
(right associativity, at level 60).

Fixpoint ceval_step (st : state) (c : com) (continuation : list (state * com)) (i : nat)
                        : interpreter_result :=
  match i with
  | O => OutOfGas
  | S i' =>
    match c with
    | <{ skip }> => Success (st, continuation)
    | <{ x := a }> =>
      let st' := x !-> (aeval st a) ; st in
      Success (st', continuation)
    | <{ (c1 !! c2) ; c3 }> => (* ; is right-associative *)
      LETINTRES (st', cont') <== ceval_step st c1 continuation i' IN
        ceval_step st' c3 ((st, <{ c2 ; c3 }>)::cont') i'
    | <{ c1 ; c2 }> =>
      LETINTRES (st', cont') <== ceval_step st c1 continuation i' IN
        ceval_step st' c2 cont' i'
    | <{ (c1 !! c2) }> =>
      ceval_step st c1 ((st, c2)::continuation) i'
    | <{ if b then c1 else c2 end }> =>
      if (beval st b) then
        ceval_step st c1 continuation i'
      else
        ceval_step st c2 continuation i'
    | <{ while b do c end }> =>
      if beval st b then
        LETINTRES (st', cont') <== ceval_step st c continuation i' IN
          ceval_step st' <{while b do c end}> cont' i'
      else
        Success (st, continuation)
    | <{ b -> c }> =>
      if (beval st b) then
        ceval_step st c continuation i'
      else
        (* backtrack *)
        match continuation with
        | [] => Fail
        | (st', c') :: continuation' =>
          ceval_step st' c' continuation' i'
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
  exists 5. (* p1 takes 5 to execute *)
  intros.
  destruct i1. try lia.
  destruct i1. try lia.
  destruct i1. try lia.
  destruct i1. try lia.
  destruct i1. try lia.
  simpl.
  reflexivity.
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
  induction i1 as [|i1']; intros i2 st st' c cont cont' Hle Hceval.
  - simpl in Hceval. discriminate Hceval.
  - destruct i2 as [|i2']. inversion Hle.
    assert ( Hle' : i1' <= i2' ) by lia.
    destruct c.
    all: simpl in Hceval. 
    all: simpl.
    (* skip *)
    + assumption.  (* goal already in context *)
    (* x := a *)
    + assumption.  (* goal already in context *) 
    (* c1 ; c2 *)
    + destruct c1.
      all: destruct ceval_step eqn:Hqest1'o; try discriminate Hceval.
      all: destruct s.
      all: apply (IHi1' i2') in Hqest1'o; try assumption.
      all: rewrite Hqest1'o.
      all: apply (IHi1' i2') in Hceval; assumption.
    (* if b then c1 else c2 end *)
    + destruct (beval st b); apply IHi1'; assumption.
    (* while b do c1 end *)
    + destruct (beval st b).
      destruct ceval_step eqn:Hqest1'o; try discriminate Hceval.
      destruct s.
      apply (IHi1' i2') in Hqest1'o; try assumption.
      rewrite Hqest1'o.
      apply (IHi1' i2') in Hceval.
      all: assumption.
    (* c1 !! c2 *)
    + apply (IHi1' i2') in Hceval; assumption.
    (* b -> c *)
    + destruct (beval st b). try intuition.
      destruct cont. try discriminate.
      destruct p.
      apply (IHi1' i2') in Hceval; assumption.
Qed.
