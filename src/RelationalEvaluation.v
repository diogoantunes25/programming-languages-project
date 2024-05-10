From FirstProject Require Import Maps Imp.
From Coq Require Import Lists.List. Import ListNotations.
From Coq Require Import Logic.FunctionalExtensionality.

Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".


(* ================================================================= *)
(** ** Evaluation as a Relation *)

(** We'll use the notation [st1 / q1 =[ c ]=> st2 / q2 / r] for the [ceval] relation:
    [st1 / q1 =[ c ]=> st2 / q2 / r] means that executing program [c] in a starting
    state [st1] with continuations [q1] results in an ending state [st2] with unexplored
    continuations [q2]. Moreover the result of the computation will be [r].*)

(* Type of result *)
Inductive result : Type :=
| Success
| Fail.

(* Notation that we use *)
Reserved Notation "st1 '/' q1 '=[' c ']=>' st2 '/' q2 '/' r"
(at level 40,
 q1 constr at next level,
 c custom com at level 99, 
 st2 constr at next level,
 q2 constr at next level,
 r constr at next level).

(* 
3. TODO: Define the relational semantics (ceval) to support the required constructs.
*)

Inductive ceval : com -> state -> list (state * com) -> 
          result -> state -> list (state * com) -> Prop :=
| E_Skip : forall st q,
    st / q =[ skip ]=> st / q / Success
| E_Asgn: forall st q a n x,
    aeval st a = n -> 
    st / q =[ x := a ]=> (x !-> n; st) / q / Success
| E_Seq_Suc: forall st st' st'' q q' q'' c1 c2 r,
    st / q =[ c1 ]=> st' / q' / Success ->
    st' / q' =[ c2 ]=> st'' / q'' / r ->
    st / q =[ c1;c2 ]=> st'' / q'' / r
| E_Seq_Fail_1: forall st st' st'' q q' q'' c1 c2,
    st / q =[ c1 ]=> st' / q' / Fail ->
    st / q =[ c1;c2 ]=> st'' / q'' / Fail
| E_If_True: forall st st' b q q' c1 c2 r,
    beval st b = true  ->
    st / q =[ c1 ]=> st' / q' / r ->
    st / q =[ if b then c1 else c2 end ]=> st' / q'/ r
| E_If_False: forall st st' b q q' c1 c2 r,
    beval st b = false  ->
    st / q =[ c2 ]=> st' / q' / r ->
    st / q =[ if b then c1 else c2 end ]=> st' / q'/ r
| E_While_False: forall st b q c1,
    beval st b = false  ->
    st / q =[ while b do c1 end ]=> st / q / Success
| E_While_True_Suc: forall st st' st'' b q q' q'' c1 r,
    beval st b = true  ->
    st / q =[ c1 ]=> st' / q' / Success ->
    st' / q' =[ while b do c1 end ]=> st'' / q'' / r ->
    st / q =[ while b do c1 end ]=> st'' / q'' / r
| E_While_True_Fail: forall st st' st'' b q q' q'' c1,
    beval st b = true  ->
    st / q =[ c1 ]=> st' / q' / Fail ->
    st / q =[ while b do c1 end ]=> st'' / q'' / Fail
| E_Choice_L: forall st st' q q' c1 c2 r,
    (* continuation from inside left side is discarded *)
    st / q =[ c1 ]=> st' / q' / r ->
    let q'' := (st,c2)::q in st / q =[ c1 !! c2 ]=> st'/ q'' / r
| E_Choice_R: forall st st' q q' c1 c2 r,
    (* continuation from inside right side is discarded *)
    st / q =[ c2 ]=> st' / q' / r ->
    let q'' := (st,c1)::q in st / q =[ c1 !! c2 ]=> st'/ q'' / r
| E_Guard_True: forall st st' q q' b c1 r,
    beval st b = true  ->
    st / q =[ c1 ]=> st' / q' / r ->
    st / q =[ b -> c1 ]=> st' / q' / r
| E_Guard_Backtrack: forall st st' st'' q q' q'' b c c' r,
    beval st b = false ->
    q = (st', c')::q' ->
    st' / q' =[ c'; b -> c ]=> st'' / q'' / r ->
    st / q =[ b -> c ]=> st'' / q'' / r
| E_Guard_Fail: forall st st' b c,
    beval st b = false ->
    st / [] =[ b -> c ]=> st' / [] / Fail
where "st1 '/' q1 '=[' c ']=>' st2 '/' q2 '/' r" := (ceval c st1 q1 r st2 q2).

(**

  3.1. TODO: Use the new relational semantics to prove the examples
             ceval_example_if, ceval_example_guard1, ceval_example_guard2,
             ceval_example_guard3 and ceval_example_guard4.
*)

Example ceval_example_if:
empty_st / [] =[
X := 2;
if (X <= 1)
  then Y := 3
  else Z := 4
end
]=> (Z !-> 4 ; X !-> 2) / [] / Success.
Proof.
  apply E_Seq_Suc with (st' := (X !-> 2)) (q' := []).
  - (* assignment *)
    apply E_Asgn. trivial.
  - (* if *)
    apply E_If_False.
    -- trivial.
    -- apply E_Asgn. trivial.
Qed.

Example ceval_example_guard1:
empty_st / [] =[
   X := 2;
   (X = 1) -> X:=3
]=> (empty_st) / [] / Fail.
Proof.
  apply E_Seq_Fail_2 with (st' := (X !-> 2)) (q' := []) (st'' := empty_st) (q'' := []).
  - apply E_Asgn. trivial.
  - apply E_Guard_Fail. trivial.
Qed. 

Example ceval_example_guard2:
empty_st / [] =[
   X := 2;
   (X = 2) -> X:=3
]=> (X !-> 3 ; X !-> 2) / [] / Success.
Proof.
  apply E_Seq_Suc with (st' := (X !-> 2)) (q' := []).
  - (* assignment *)
    apply E_Asgn.  trivial.
  - (* guard *)
    apply E_Guard_True.
    -- (* contition *)
       trivial.
    -- (* body *)
       apply E_Asgn. trivial.
Qed. 

(* choose left on the non-deterministic choice so the continuation will be empty in the end *)

Example ceval_example_guard3: exists q,
empty_st / [] =[
   (X := 1 !! X := 2);
   (X = 2) -> X:=3
]=> (X !-> 3) / q / Success.
Proof.
  exists [].
  eapply E_Seq_Suc.
  - (* left part *)
    apply E_Choice_L with (q' := []).
    apply E_Asgn. trivial.
  - (* right part *)
    apply E_Guard_Backtrack with (st' := empty_st) (q' := []) (c' := <{X:=2}>).
    -- (* prove guard false *)
       trivial.
    -- (* prove continuations match *)
       trivial.
    -- apply E_Seq_Suc with (st' := (X !-> 2)) (q' := []).
       --- (* left part *)
           apply E_Asgn. trivial.
       --- (* right part *)
           apply E_Guard_True.
           ---- (* prove condition true *)
                trivial.
           ---- replace (X !-> 3) with (X !-> 3; X !-> 2).
                ----- (* body *)
                      apply E_Asgn. trivial.
                ----- apply functional_extensionality. intros x.
                      unfold t_update.
                      destruct (eqb_string X x); trivial.
Qed.

(* Choose right on the Non-deterministic choice so the continuation at the end is not empty *)

Example ceval_example_guard4: exists q,
empty_st / [] =[
   (X := 1 !! X := 2);
   (X = 2) -> X:=3
]=> (X !-> 3) / q / Success.
Proof.
  eexists.
  apply E_Seq_Suc with (st' := (X !-> 2)) (q' := [(empty_st, <{ X := 1 }>)]).
  - apply E_Choice_R with (q' := []).
    apply E_Asgn. trivial.
  - apply E_Guard_True.
    -- (* prove condition true *)
       trivial.
    -- (* body *)
       replace (X !-> 3) with (X !-> 3; X !-> 2).
       --- apply E_Asgn. trivial.
       --- apply functional_extensionality. intros x.
           unfold t_update.
           destruct (eqb_string X x); trivial.
Qed.

(* 3.2. Behavioral equivalence *)

Definition cequiv_imp (c1 c2 : com) : Prop := 
forall (st1 st2 : state) q1 q2 result,
(st1 / q1 =[ c1 ]=> st2 / q2 / result) ->
exists q3, 
(st1 / q1 =[ c2 ]=> st2 / q3 / result).

Definition cequiv (c1 c2 : com) : Prop :=
cequiv_imp c1 c2 /\ cequiv_imp c2 c1.

Infix "==" := cequiv (at level 99).


(**
  3.2. TODO: Prove the properties below
*)

Lemma cequiv_ex1:
<{ X := 2; X = 2 -> skip }> == 
<{ X := 2 }>.
Proof.
  unfold cequiv. split.
  - unfold cequiv_imp. intros.
    (* need to prove that for H to hold, q2 is the same as q1 *)
    inversion H.
    -- (* composition succeded *)
      inversion H2. inversion H8.
      --- (* guard condition true *)
        inversion H24.  
        (* write st' as function of st *)
        rewrite <- H3 in H14.
        (* write st2 as funciton of st *)
        rewrite <- H14 in H2.
        rewrite H29 in H14.
        rewrite <- H14.
        exists q2.

        (* rewrite continuations *)
        rewrite H15 in H2.
        rewrite <- H30.
        assumption.
      --- (* guard false *)

          (* prove that guard is true *)
          rewrite <- H13 in H14.
          unfold aeval in H14.
          rewrite <- H14 in H18.
          unfold beval in H18. simpl in H18. 
          exfalso. discriminate.
    -- (* first command failed *)
        inversion H7. 
    -- (* second command failed *)
       inversion H8.
      --- (* guard condition true *)
          (* in this case, failing would mean skip failing *)
          inversion H17.
      --- (* guard condition false and continuation *)
          (* in thi case, failing would be in continuation *)
          (* prove that guard doesn't fail - as before *)
          inversion H2.
          rewrite <- H23 in H24.
          unfold aeval in H24.
          rewrite <- H24 in H11.
          unfold beval in H11. simpl in H11.
          exfalso. discriminate.
      --- (* guard condition false and no continuation *)
          inversion H2.
          rewrite <- H20 in H21.
          unfold aeval in H21.
          rewrite <- H21 in H13.
          unfold beval in H13. simpl in H13.
          exfalso. discriminate.
  - unfold cequiv_imp. intros.
    inversion H.
    exists q2.
    apply E_Seq_Suc with (st' := st2) (q' := q2).
    -- destruct result0.
      --- rewrite H6 in H. assumption.
      --- inversion H.
    -- apply E_Guard_True.
      --- rewrite <- H5. rewrite <- H7. unfold aeval. unfold beval. simpl.
          trivial.
      --- rewrite H5. apply E_Skip.
Qed.

Lemma cequiv_ex2:
<{ (X := 1 !! X := 2); X = 2 -> skip }> == 
<{ X := 2 }>.
Proof.
  unfold cequiv. split.
  - unfold cequiv_imp. intros.
    inversion H.
    -- (* use seq_suc *)
       (* this happens to work *)
       (* prove that guard fails*)
       --- inversion H2. 
           ---- (* chose left *)
                 inversion H16.
                 inversion H8.
                 ----- (* guard true *)
                     inversion H32.
                     rewrite <- H22 in H26.
                     rewrite <- H21 in H26. 
                     unfold aeval in H26. unfold beval in H26. simpl in H26.
                     exfalso. discriminate.
                 -----(* guard false *)
                      (* show that most recent continuation is X := 2 *)
                      rewrite <- H15 in H27.
                      inversion H27.
                      rewrite <- H36 in H33.
                      inversion H33.
                      inversion H39.
                      exists q'0.
                      subst.
                      inversion H42.
                      ------ (* guard true - what happens *)
                             subst. simpl aeval in *.
                             inversion H10.
                             apply E_Asgn. trivial.
                      ------ (* guard false - didn't happen *)
                             subst. simpl in H3.
                             exfalso. discriminate.
           ---- (* chose right *)
                inversion H16.
                inversion H8.
                 ----- (* guard true*)
                       inversion H32.
                       rewrite <- H37.
                       exists q'0.
                       rewrite <- H22.
                       apply E_Asgn. 
                       trivial.
                 ----- (* guard false *)
                       (* prove contradiction *)
                       rewrite <- H21 in H22.
                       rewrite <- H22 in H26.
                       unfold beval in H26. unfold aeval in H26. simpl in H26.
                       exfalso. discriminate.
    -- (* use seq_fail_1 *)
       (* this doesn't work *)
       inversion H7.
       --- (* chose left *)
            inversion H15.
       --- (* chose right *)
            inversion H15.
    -- (* use seq_fail_2 - FIXME: this is not right *)
       inversion H2.
       --- (* chose left *)

           (* need to prove that guard fails *)
           inversion H16.
           inversion H8.
           ---- (* guard succeds - false *)
                 rewrite <- H22 in H26.
                 rewrite <- H21 in H26.
                 unfold beval in H26. unfold aeval in H26.
                 simpl in H26.
                 exfalso. discriminate.
           ---- (* guard fails and there's continuation *)
               (* this is what happened *)
               (* show that continuation is what we want *)
               subst.
               inversion H27. 
               rewrite <- H3 in H33.
               inversion H33.
                 ----- (* first failed *)
                       inversion H9. 
                 ----- (* second failed *)
                       inversion H10.
                      ------ (* guard true *)
                             subst.
                             inversion H22.
                      ------ (* guard false but continuation *)
                             subst.
                             inversion H6.
                             subst. unfold aeval in H15.
                             unfold beval in H15. simpl in H15.
                             exfalso. discriminate.
                      ------ (* guard false but continuation *)
                             subst.
                             inversion H6.
                             subst. unfold aeval in H18.
                             simpl in H18.
                             exfalso. discriminate.
           ---- (* guard fails and there's no continuation *)
                subst.
                inversion H27.
       --- (* chose right *)
           inversion H16. inversion H8. subst.
           ---- (* guard succeds - true *)
                inversion H32.
           ---- (* guard fails but continuation - false *)
                subst.
                simpl in H26. exfalso. discriminate.
           ---- (* guard fails with not continuation - false *)
                subst.
                simpl in H28. exfalso. discriminate.
  - unfold cequiv_imp. intros.
    inversion H.
    eexists.
    eapply E_Seq_Suc.
    -- (* prove left *)
       eapply E_Choice_R.
       apply E_Asgn.
       unfold aeval. trivial.
    -- (* prove right *)
      apply E_Guard_True.
       --- (* prove guard true *)
           simpl. trivial.
       --- (* prove body *)
           subst. 
           apply E_Skip.
Qed.

Lemma choice_idempotent: forall c,
<{ c !! c }> == <{ c }>.
Proof.
  intros c.
  unfold cequiv. split.
  - unfold cequiv_imp. intros.
    inversion H;
      exists q';
      assumption.
  - unfold cequiv_imp. intros.
    exists ((st1, c)::q1).
    apply E_Choice_L with (st := st1) (st' := st2) (c1 := c) (c2 := c) (r := result0)
    (q := q1) (q' := q2).
    assumption.
Qed.

(* TODO: rewrite using ;*)

Lemma choice_comm: forall c1 c2,
<{ c1 !! c2 }> == <{ c2 !! c1 }>.
Proof.
  intros c1 c2.
  unfold cequiv. split.
  - unfold cequiv_imp. intros.
    inversion H.
    -- (* chose left *)
       exists q''.
       apply E_Choice_R with (q' := q').
       assumption.
    -- (* chose right *)
       exists q''.
       apply E_Choice_L with (q' := q').
       assumption.
  - unfold cequiv_imp. intros.
    inversion H.
    -- (* chose left *)
       exists q''.
       apply E_Choice_R with (q' := q').
       assumption.
    -- (* chose right *)
       exists q''.
       apply E_Choice_L with (q' := q').
       assumption.
Qed.

Lemma choice_assoc: forall c1 c2 c3,
<{ (c1 !! c2) !! c3 }> == <{ c1 !! (c2 !! c3) }>.
Proof.
  intros.
  unfold cequiv. split.
  - unfold cequiv_imp. intros.
    inversion H.
    -- (* chose left - c1 !! c2 *)
       inversion H7.
       (* TODO: understand this properly, this was some kind of wizardry *)
       --- (* chose left c1 *)
           (* recall that q' is the continuation that comes out of evaulating
              the chosen side *)
           exists ((st1, <{ c2 !! c3 }>)::q1).
           apply E_Choice_L with (q' := q'0).
           assumption.
       --- (* chose right c2 *)
           exists ((st1, <{ c1 }>)::q1).
           apply E_Choice_R with (q' := ((st1, <{ c3 }>)::q1)).
           apply E_Choice_L with (q' := q'0).
           assumption.
    -- (* chose right c3 *)
       exists ((st1, <{ c1 }>)::q1).
       apply E_Choice_R with (q' := (st1, <{ c2 }>)::q1).
       apply E_Choice_R with (q' := q').
       assumption.
  - unfold cequiv_imp. intros.
    inversion H.
    -- (* chose left - c1 *)
       exists ((st1, <{ c3 }>)::q1).
       apply E_Choice_L with (q' := (st1, <{ c2 }>)::q1).
       apply E_Choice_L with (q' := q').
       assumption.
    -- (* chose right - c2 !! c3 *)
       inversion H7.
       --- (* chose left - c2 *)
          exists ((st1, <{ c3 }>)::q1).
          apply E_Choice_L with (q' := (st1, <{ c1 }>)::q1).
          apply E_Choice_R with (q' := q'0).
          assumption.
       --- (* chose right - c3 *)
          exists ((st1, <{ c1 !! c2 }>)::q1).
          apply E_Choice_R with (q' := q'0).
          assumption.
Qed.

Lemma choice_seq_distr_l: forall c1 c2 c3,
<{ c1 ; (c2 !! c3)}> == <{ (c1;c2) !! (c1;c3) }>.
Proof.
  intros.
  unfold cequiv. split.
  - unfold cequiv_imp. intros.
    inversion H.
    -- (* c_seq_suc *)
       inversion H8.
       --- (* chose left - c2 *)
           exists ((st1, <{ c1; c3 }>)::q1).
           apply E_Choice_L with (q' := q'0).
           apply E_Seq_Suc with (st' := st') (q' := q').
           ---- (* left side *)
                assumption.
           ---- (* right side *)
                assumption.
       --- (* chose right - c3 *)
           exists ((st1, <{ c1; c2 }>)::q1).
           apply E_Choice_R with (q' := q'0).
           apply E_Seq_Suc with (st' := st') (q' := q').
           ---- (* left side *)
                assumption.
           ---- (* right side *)
                assumption.
    -- (* c_seq_fail_1 *)
       exists ((st1, <{ c1; c3 }>)::q1).
       apply E_Choice_L with (q' := q').
       apply E_Seq_Fail_1 with (st' := st') (q' := q').
       assumption.
    -- (* c_seq_fail_2 *)
       inversion H8.
       --- (* chose left - c2 *)
       exists ((st1, <{ c1; c3 }>)::q1).
       apply E_Choice_L with (q' := q').
       apply E_Seq_Fail_2 with (st' := st') (q' := q') (st'' := st'') (q'' := q'0).
           ---- (* first goes through *)
                assumption.
           ---- (* second fails *)
                assumption.
       --- (* chose right - c3 *)
       exists ((st1, <{ c1; c2 }>)::q1).
       apply E_Choice_R with (q' := q').
       apply E_Seq_Fail_2 with (st' := st') (q' := q') (st'' := st'') (q'' := q'0).
           ---- (* first goes through *)
                assumption.
           ---- (* second fails *)
                assumption.
  - unfold cequiv_imp. intros.
    inversion H.
    -- (* chose left *)
       inversion H7.
       --- (* success *)
           eexists.
           eapply E_Seq_Suc.
           ---- (* left *)
                eassumption.
           ---- (* right *)
                eapply E_Choice_L.
                eassumption.
       --- (* first failed *)
           eexists.
           eapply E_Seq_Fail_1.
           eassumption.
       --- (* second failed *)
           eexists.
           eapply E_Seq_Fail_2.
           ---- (* first succeded *)
                eassumption.
           ---- (* second failed *)
                eapply E_Choice_L.
                eassumption.
    -- (* chose right *)
       inversion H7.
       --- (* success *)
           eexists.
           eapply E_Seq_Suc.
           ---- (* left *)
                eassumption.
           ---- (* right *)
                eapply E_Choice_R.
                eassumption.
       --- (* first failed *)
           eexists.
           eapply E_Seq_Fail_1.
           eassumption.
       --- (* second failed *)
           eexists.
           eapply E_Seq_Fail_2.
           ---- (* first succeded *)
                eassumption.
           ---- (* second failed *)
                eapply E_Choice_R.
                eassumption.
Unshelve. trivial. trivial. trivial. trivial.
Qed.

Lemma choice_congruence: forall c1 c1' c2 c2',
c1 == c1' -> c2 == c2' ->
<{ c1 !! c2 }> == <{ c1' !! c2' }>.
Proof.
    intros.
    unfold cequiv. split.
    - unfold cequiv_imp. intros.
      inversion H1.
      -- (* chose left *)
         unfold cequiv in H. destruct H as [Hl Hr].

         unfold cequiv_imp in Hl.
         apply Hl in H9.
         destruct H9 as [q4 HQ1].

         exists ((st1, c2')::q1).
         apply E_Choice_L with (q' := q4).
         trivial.
      -- (* chose right *)
         unfold cequiv in H0. destruct H0 as [Hl Hr].

         unfold cequiv_imp in Hl.
         apply Hl in H9.
         destruct H9 as [q4 HQ1].

         exists ((st1, c1')::q1).
         apply E_Choice_R with (q' := q4).
         trivial.
    - unfold cequiv_imp. intros.
      inversion H1.
      -- (* chose left *)
         unfold cequiv in H. destruct H as [Hl Hr].

         unfold cequiv_imp in Hr.
         apply Hr in H9.
         destruct H9 as [q4 HQ1].

         exists ((st1, c2)::q1).
         apply E_Choice_L with (q' := q4).
         trivial.
      -- (* chose right *)
         unfold cequiv in H0. destruct H0 as [Hl Hr].

         unfold cequiv_imp in Hr.
         apply Hr in H9.
         destruct H9 as [q4 HQ1].

         exists ((st1, c1)::q1).
         apply E_Choice_R with (q' := q4).
         trivial.
Qed.
