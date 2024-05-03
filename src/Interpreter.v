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

Fixpoint ceval_step (st : state) (c : com) (continuation: list (state * com)) (i : nat)
                    : interpreter_result :=
  match i with
  | O => OutOfGas
  | S i' => match c with
    | <{ skip }> => Success (st, continuation)
    | <{ x := y }> => Success ((x !-> aeval st y; st), continuation)
    (* c2's most recent continuation will be c1's extended with c1 itself *)
    | <{ c1 ; c2 }> =>
      match (ceval_step st c1 continuation i') with
      | Success (st', cont') =>
          let new_continuation := 
            match cont' with
            | [] => []
            | (st'', c') :: t => ((st'', <{ c' ; c2 }>) :: t)
            end
          in
          ceval_step st' c2 new_continuation i'
      | Fail => Fail
      | OutOfGas => OutOfGas
      end
    | <{ if b then c1 else c2 end }> =>
      if (beval st b)
      then ceval_step st c1 continuation i'
      else ceval_step st c2 continuation i'
    | <{ while b do c1 end }> =>
      if (beval st b)
      then match (ceval_step st c continuation i') with
           | Success(st', c') => ceval_step st' c c' i'
           | Fail => Fail
           | OutOfGas => OutOfGas
           end
      else Success (st,continuation)
    | <{ c1 !! c2 }> =>
      (* c1 is executed first *)
      match (ceval_step st c1 continuation i') with
      | Success (st', c') => Success (st', (st, c2) :: continuation)
      | Fail => Fail
      | OutOfGas => OutOfGas
      end
    | <{ b -> c1 }> =>
      if beval st b
      then ceval_step st c1 continuation i'
      else
        match continuation with
        | [] => Fail   
        (* FIXME: I think this is wrong - i don't have a way to resume *)
        | (st', c') :: continuation' => ceval_step st' c' continuation' i' 
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

Example test_dsa_1:
  run_interpreter (X !-> 5) <{ X=5 -> X:=10 }> 5 = OK [("X", 10); ("Y", 0); ("Z", 0)].
Proof. auto. Qed.

Example test_dsa_2:
  run_interpreter (X !-> 5) <{ X=5 -> X:=10 }> 5 = OK [("X", 10); ("Y", 0); ("Z", 0)].
Proof. auto. Qed.

Example test_dsa_3:
  run_interpreter (X !-> 5) <{ X=10 -> X:=11 }> 5 = KO.
Proof. auto. Qed.

(* Example test_dsa_4: *)
(* Compute *)
(*   run_interpreter (X !-> 5) <{ *)
(*     if true then (X := 1 !! X := 2) else skip end; *)
(*     Y := X + 1; *)
(*     X = 2 -> Z := 5; *)
(*     X := 3  *)
(*   }> 20. *)
 
Compute
  run_interpreter (X !-> 0) <{
    (X := 1 !! X := 2);
    Y := X + 1;
    X = 2 -> Z := 3
  }> 20.

Compute
  run_interpreter (X !-> 0) <{
    if true then (X := 1 !! X := 2) else skip end;
    Y := X + 1;
    X = 2 -> Z := 3
  }> 20.

Compute
  run_interpreter (X !-> 0) <{
    if true then
      if true then (X := 1 !! X := 2) else skip end
    else
      skip
    end;
    Y := X + 1;
    X = 2 -> Z := 3
  }> 10.

Compute
  run_interpreter (X !-> 0) <{
  X := 1 !! X :=2;
  Y := 1 !! Y :=2;
  Z := 3;
  Y=2 -> skip;
  X=2 -> skip
}> 20.

Compute
  run_interpreter (X !-> 0) <{
  X := 1 !! X :=2;
  W := 4;
  Y := 1 !! Y :=2;
  Z := 3;
  Y=2 -> skip;
  X=2 -> skip
}> 20.

Unset Printing Notations.
Definition a132 := (<{
    if true then (X := 1 !! X := 2) else skip end;
    Y := X + 1;
    X = 2 -> X := 3
  }>).
Print a132.
Set Printing Notations.

Example test_dsa_4:
  run_interpreter (X !-> 5) <{ X:=7; X=10 -> X:=11 }> 10 = KO.
Proof. auto. Qed.

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

Unset Printing Notations.
Compute run_interpreter (X !-> 5) <{ (X := 1 !! X := 2) }> 4.
Compute run_interpreter (X !-> 5) <{ (X := 1 !! X := 2); (X=2) -> skip }> 5.
Compute run_interpreter (X !-> 5) <{ (X := 1 !! X := 2); (X=2) -> X := 3 }> 5.
Definition a1 := (<{ (X := 1 !! X := 2); (X = 2) -> X:=3 }>).
Print a1.
Set Printing Notations.

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
  (* TODO *)
Qed.


(**
  2.3. TODO: Prove ceval_step_more.
*)

Theorem ceval_step_more: forall i1 i2 st st' c cont cont',
  i1 <= i2 ->
  ceval_step st c cont i1 = Success (st', cont') ->
  ceval_step st c cont i2 = Success (st', cont').
Proof.
  (* TODO *)
Qed.
