(** Variational relational algebra lemmas *)
Set Warnings "-notation-overridden,-parsing".
Import Init.Datatypes.
Import Coq.Init.Nat.
Require Import Maps.
Require Export List.
Require Export Logic.
Import Coq.Lists.List.ListNotations.

Scheme Equality for list.

Print list_beq.

Load VRA_RA_encoding.
Import VRA_RA_encoding.

Module VRA_encoding_lemmas.

(*----------------------sublist_bool_correct--------------------------------*)

Lemma set_mem_In: forall a x, set_mem string_dec a x = true <-> set_In a x.
Proof. split. apply set_mem_correct1. apply set_mem_correct2. Qed.

Lemma In_not_In: forall {X:Type} (x y:X) (A:list X), (In x A) -> (~ In y A) -> x<>y.
Proof. intros. induction A. simpl in H. destruct H. simpl in H. simpl in H0.
       apply Classical_Prop.not_or_and in H0. destruct H0. destruct H. 
       rewrite <- H. assumption. apply  IHA in H. auto. auto. Qed.

Lemma sublist_bool_correct: forall A A' {Ha: NoDup A} {Ha': NoDup A'}, sublist_bool A A' = true
                        <-> sublist A A'.
Proof. intros. split. 
       + intro H. generalize dependent A'. induction A. 
         ++ unfold sublist. intros. simpl in H0. destruct H0.
         ++ intros. unfold sublist_bool in H. destruct (set_mem string_dec a A') eqn: Hmem.
            +++ fold sublist_bool in H. simpl. unfold sublist. intros.
                destruct H0. rewrite <- H0. rewrite set_mem_In in Hmem. 
                unfold set_In in Hmem. assumption. apply IHA in H.
                unfold sublist in H. apply H in H0. apply set_remove_1 in H0.
                assumption. rewrite NoDup_cons_iff in Ha. destruct Ha. assumption.
                apply set_remove_nodup. assumption. 
            +++ discriminate H. 
      + intro H. generalize dependent A'. induction A.
        ++ intros. simpl. reflexivity.
        ++ intros. unfold sublist_bool; fold sublist_bool. 
           destruct (set_mem string_dec a A') eqn: Hmem.
           +++ 
               apply IHA. 
               - rewrite NoDup_cons_iff in Ha. destruct Ha. assumption.
               - apply set_remove_nodup. assumption.
               - 
               unfold sublist. intros. unfold sublist in H.
               rewrite set_mem_In in Hmem. 
               unfold set_In in Hmem. 
               apply (set_remove_3). apply H. simpl. right. assumption.
               rewrite NoDup_cons_iff in Ha. destruct Ha. apply (In_not_In _ _ A).
               assumption. assumption. 
           +++ unfold sublist in H.  rewrite <- Hmem. rewrite set_mem_In.
               unfold set_In. apply H. apply in_eq.
Qed.

(*-----------------------sublist_bool_correct--------------------------------*)




(*---------------------------Equivalence relation--------------*)
  
(*-----------------------------------equiv----------------------------------*)
End VRA_encoding_lemmas.