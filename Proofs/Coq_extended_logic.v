(** Extension lemmas to coq's core logic *)
Set Warnings "-notation-overridden,-parsing".
Require Import Lists.List.
Require Import Lists.ListSet.
Require Import Logic.Classical_Pred_Type.
Import Coq.Lists.List.ListNotations.

Theorem contrapositive : forall P Q:Prop, 
             (P -> Q) -> (~Q -> ~P).
Proof. intros. intro. apply H0. apply H. exact H1. Qed.

Theorem contrapositive_iff : forall P Q:Prop, 
             (P <-> Q) -> (~Q <-> ~P).
Proof. intros. rewrite H. reflexivity. Qed.

Theorem not_or_and_not : forall P Q:Prop, 
             ~(P \/ Q) <-> ~P /\ ~Q.
Proof. intros. split.
apply Classical_Prop.not_or_and.
apply Classical_Prop.and_not_or.
Qed.

Theorem or_distributes_over_and_1 : forall P Q R : Prop,
  P \/ (Q /\ R) -> (P \/ Q) /\ (P \/ R).
Proof.
  intros P Q R. intros H. inversion H as [HP | [HQ HR]].
   split.
      left. apply HP.
      left. apply HP.
    split.
      right. apply HQ.
      right. apply HR.  Qed.

Theorem or_distributes_over_and_2 : forall P Q R : Prop,
  (P \/ Q) /\ (P \/ R) -> P \/ (Q /\ R).
Proof.
  intros P Q R H. inversion H as [[H1P | H1Q] [H2P | H2R]].
  left. apply H1P.
  left. apply H1P.
  left. apply H2P.
  right. split.
    apply H1Q.
    apply H2R.  Qed.

Theorem or_dist_and : forall P Q R : Prop,
  P \/ (Q /\ R) <-> (P \/ Q) /\ (P \/ R).
Proof.
  intros P Q R. split.
  apply or_distributes_over_and_1.
  apply or_distributes_over_and_2.  Qed.

Theorem or_not : forall P Q : Prop,
  P \/ Q -> ~ Q -> P.
Proof.
  intros P Q H1 H2. destruct H1. 
  assumption. contradiction.
Qed.

Theorem dist_exists_or : forall (X:Type) (P Q : X -> Prop),
  (exists x, P x \/ Q x) <-> (exists x, P x) \/ (exists x, Q x).
Proof.
  intros X P Q. split.
  (* Case "->". *)
    intros H. inversion H as [x Hx].
    inversion Hx as [HP | HQ].
    (* SCase "Hx = P x". *)
      left. exists x. apply HP.
    (* SCase "Hx = Q x". *)
      right. exists x. apply HQ.
  (* Case "<-".*)
    intros H. inversion H as [HP | HQ].
    (* SCase "H = HP". *)
      inversion HP as [x Hx]. exists x. left. apply Hx.
    (* SCase "H = HQ". *)
      inversion HQ as [x Hx]. exists x. right. apply Hx.  Qed.


(* Classical_Pred_Type not_ex_all_not *)
(* ~ exists x, P -> forall x, ~ P x *)
Lemma dist_not_exists {X:Type} (P:X->Prop): 
         ~(exists x, P x) -> forall x, ~ P x.
Proof. intro H.
 pose proof (fun x Px => H (ex_intro _ x Px)) as H'; simpl in H'.
 auto.
Qed.

Lemma forall_dist_and (A:Type) (P Q:A-> Prop): (forall x, (P x) /\ (Q x))
<-> (forall x, (P x)) /\ (forall x, (Q x)).
Proof. intros. split; try (intro H); try (intro x); split;
try(intro x); try (specialize H with x); destruct H; auto. 
Qed. 


(*----------------- list logic extension ---------------------*)


Lemma notIn_nil: forall (A:Type) (l:list A), 
              (forall x, ~ In x l) <-> l = [].
Proof. intros. split. intros H. 
induction l as [| a l IHl]. auto. specialize H with (x:=a).
simpl in H. apply Classical_Prop.not_or_and in H.
destruct H. destruct H. reflexivity.
intros. rewrite H. apply in_nil.
Qed.

Lemma cons_injective: forall (A : Type)(a a' : A)(l l' : list A),
   (a = a') /\ (l = l') -> (a :: l) = (a' :: l').
Proof. intros. destruct H. rewrite H, H0. reflexivity. Qed.


Lemma remove_nodup_comm (A:Type) eq_dec (a:A) (l:list A): 
     remove eq_dec a (nodup eq_dec l) = nodup eq_dec (remove eq_dec a l).
Proof. 
induction l as [|x l IHl].
- simpl. reflexivity.
- simpl. destruct (in_dec eq_dec x l) as [HInd | HInd].
  + destruct (eq_dec a x) as [Heqd | Heqd]. apply IHl.
    apply (in_in_remove eq_dec) with (y:=a) in HInd as HInrm.  
    simpl. destruct (in_dec eq_dec x (remove eq_dec a l)).
    apply IHl. contradiction. eauto. 
 +  simpl. destruct (eq_dec a x) as [Heqd | Heqd]. apply IHl.
    simpl. destruct (in_dec eq_dec x (remove eq_dec a l)) 
    as [HIndrm | HIndrm].
    apply in_remove in HIndrm. destruct HIndrm. contradiction.
    rewrite IHl. reflexivity.
Qed.

Lemma In_count_occ_nodup {A:Type} eq_dec (a:A) (l:list A): 
In a l ->
count_occ eq_dec (nodup eq_dec l) a = 1.
Proof.
intro H.
pose (NoDup_nodup eq_dec l) as HNdpl.
rewrite (NoDup_count_occ' eq_dec _) in HNdpl.
apply HNdpl. rewrite nodup_In. assumption.
Qed.


Lemma notIn_count_occ_nodup {A:Type} eq_dec (a:A) (l:list A): 
~ In a l ->
count_occ eq_dec (nodup eq_dec l) a = 0.
Proof.
intro H. rewrite <- (nodup_In eq_dec) in H.
rewrite count_occ_not_In in H. apply H.
Qed.



(*---------------------------------------------------------------*)

(*--------------------- set logic extension ---------------------*)


(*---------------------------------------------------------------*)
