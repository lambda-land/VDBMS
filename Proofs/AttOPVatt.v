(** Operation on attribute of variational att *)
Set Warnings "-notation-overridden,-parsing".


Load extract_lemmas.

(* configVAttSet InAtt *)

Lemma In_InAtt_config: forall a A c, In a (configVAttSet A c) -> InAtt a A.
Proof. 
intros. induction A.
- simpl in H. destruct H. 
- simpl in H. destruct a0 as (a0, e0). 
  destruct (E[[ e0]] c) eqn:He0. 
  + simpl in H. destruct H.
    ++ rewrite H. simpl. eauto.
    ++ simpl. right. apply IHA. (*exists c.*)
       auto.
  + simpl. right. apply IHA. 
    auto.
Qed.  


Lemma notInAtt_notIn_config: forall a A c, ~InAtt a A -> ~In a (configVAttSet A c).
Proof. 
intros a A c H.
pose (In_InAtt_config a A c) as H1.
apply contrapositive in H1. 
auto. auto. 
Qed.

(*----------------------------------------------------------------------*)

(* configVAttSet removeAtt *)

Lemma count_occ_config_removeAtt_eq a A c:
count_occ string_eq_dec (configVAttSet (removeAtt a A) c) a = 0.
Proof. pose (notInAtt_removeAtt A a) as HnInrm.
apply notInAtt_notIn_config with (c:=c) in HnInrm.
rewrite count_occ_not_In in HnInrm.
apply HnInrm.
Qed.

Lemma count_occ_config_removeAtt_neq a a0 A c: a <> a0 -> 
count_occ string_eq_dec (configVAttSet (removeAtt a A) c) a0 = 
count_occ string_eq_dec (configVAttSet A c) a0.
Proof. intro H. induction A as [| a' A IHA].
+ simpl. reflexivity.
+ destruct a' as (a', e'). simpl.
  destruct (string_beq a a') eqn: Heqb;
  try(rewrite stringDecF.eqb_eq in Heqb);
  simpl; destruct (E[[ e']] c) eqn: He';
  try (simpl; try (rewrite Heqb in H); 
       destruct (string_eq_dec a' a0) eqn: Heqdec;
       try (contradiction); try(rewrite IHA; reflexivity);
       apply IHA).
Qed. 

(* remove a  [[ A]]c = [[ removeAtt a A]]c *) 
Lemma remove_removeAtt a A c: 
      remove string_eq_dec a (configVAttSet A c) 
      = configVAttSet (removeAtt a A) c.
Proof. 
induction A as [|a' A IHA].
- simpl. reflexivity.
- simpl. destruct a' as (a', e').
  destruct (E[[ e']] c) eqn:He'.
  + simpl. destruct (string_eq_dec a a').
    ++ rewrite <- e. rewrite stringBEF.eqb_refl.
       exact IHA.
    ++ rewrite <- stringBEF.eqb_neq in n. 
       rewrite n. simpl. rewrite He'. rewrite (IHA).
       reflexivity.
  + destruct (string_beq a a'). 
    ++ exact IHA.
    ++ simpl. rewrite He'. exact IHA.
Qed.

Lemma removeAtt_equiv a A A':
A =va= A' -> removeAtt a A =va= removeAtt a A'.
Proof. 
unfold equiv_vatts.
simpl. unfold equiv_atts. intros.
specialize H with c a0. destruct H as [H H0].
split. 
+ split; intro H1; 
  rewrite <- In_config_exists_true in H1;
  destruct H1 as [e0 H1]; destruct H1 as [H1 H2];
  destruct (string_eq_dec a0 a) as [Heqdec | Heqdec];
  (* a0 = a *)
  try (rewrite Heqdec in H1; apply notIn_removeAtt in H1; destruct H1);
  (* a0 <> a *)
  try (apply In_removeAtt in H1; apply In_config_true with (c:=c) in H1;
  auto; apply H in H1; 
  rewrite <- In_config_exists_true in H1;
  destruct H1 as [e1 H1]; destruct H1 as [H1 H1e1];
  rewrite <- In_config_exists_true; exists e1;
  split; try (apply In_removeAtt; eauto); try(eauto)).
  
+ destruct (string_eq_dec a a0) as [eq | neq].
  rewrite eq. repeat (rewrite count_occ_config_removeAtt_eq).
  reflexivity.
  repeat (rewrite (count_occ_config_removeAtt_neq _ _ neq)).
  assumption.
Qed.

(*----------------------------------------------------------------------*)

(* -- NoDupAtt NoDup -- *)

Lemma NoDupAtt_NoDup: forall A, NoDupAtt A -> NoDup A.
Proof. intros A H. induction H as [| a e l H1 H2 IHa]. 
       + apply NoDup_nil.
       + apply NoDup_cons.
         ++ unfold not. intro H.
            unfold not in H1. apply H1.
            rewrite InAtt_In_exfexp. exists e.
            auto.
         ++ auto.
Qed.

(* *)

Lemma NoDupAtt_NoDup_config: forall A c, NoDupAtt A -> NoDup (configVAttSet A c).
Proof. intros A c H. induction H as [| a e l H1 H2 IHa]. 
       + apply NoDup_nil.
       + simpl. destruct (E[[ e]] c) eqn: He. 
         ++ apply NoDup_cons.
            unfold not. intro H.
            unfold not in H1. apply H1.
            apply In_InAtt_config in H. auto. auto.
         ++ auto.
Qed.

Lemma NoDupAtt_NoDup_configVQ: forall Q c, NoDupAtt (fst Q) -> NoDup (configVQtype Q c).
Proof. intros Q c. destruct Q. simpl.
       intro H. destruct (E[[ f]] c).
       apply NoDupAtt_NoDup_config. apply H.
       apply NoDup_nil.
Qed.

Lemma NoDupAtt_removeAtt: forall a' A,
      NoDupAtt A -> NoDupAtt (removeAtt a' A).
Proof. intros. induction H. 
+ apply NoDupAtt_nil. 
+ simpl. 
  destruct (string_beq a' a) eqn:Heq.
  eauto. 
  rewrite stringBEF.eqb_neq in Heq.
  simpl. apply NoDupAtt_cons.
  ++ rewrite <- InAtt_InAtt_removeAtt.
   auto. eauto.
  ++ auto.
Qed. 

(* -- NoDupAtt In configVAttSet -- *)

Lemma NoDupAtt_In_notIn A a e e':
NoDupAtt A -> In (ae a e) A -> (e <> e') 
-> ~ In (ae a e') A.
Proof. intros. induction A. 
- simpl in H0. destruct H0. 
- simpl in H0. simpl. 
  apply Classical_Prop.and_not_or.
  split; destruct a0 as (a0, e0);
  inversion H; subst; rewrite InAtt_In_exfexp in H4. 
  + destruct H0.
    ++ inversion H0; subst. unfold not.
    intro. inversion H2. contradiction.
    ++ unfold not. intro. inversion H2; subst.
    apply not_ex_all_not with (n:=e) in H4.
    contradiction.
  + destruct H0.
    ++ inversion H0; subst. 
    apply not_ex_all_not with (n:=e') in H4.
    assumption.
    ++ apply IHA. all:assumption.
Qed.

Lemma In_config_false: forall a e A c, NoDupAtt A-> In (ae a e) A ->
           (E[[ e]]c) = false -> ~ In a (configVAttSet A c).
Proof. intros. induction A. 
       - simpl in H0. destruct H0.
       - simpl in H0. inversion H as [|a' e' A' HIn HNodup]; subst.
         destruct H0.
         + inversion H0; subst. simpl. rewrite H1.
           apply notInAtt_notIn_config with(c:=c) in HIn. 
           auto.
         + simpl. destruct (E[[ e']] c) eqn:He'.
           ++ simpl. apply Classical_Prop.and_not_or.
              split. apply In_InAtt_fstVatt in H0.
              simpl in H0. 
              destruct (string_beq a' a) eqn:Haa'.
              rewrite stringDecF.eqb_eq in Haa'.
              rewrite Haa' in HIn. contradiction.
              rewrite stringBEF.eqb_neq in Haa'.
              auto. eauto.
           ++ eauto.
Qed.



(*---------------------------------------------------------------------------*)

(*------------------------------nodupatt-------------------------------------*)

Lemma InAtt_nondupatt: forall x l, InAtt x (nodupatt l) <-> InAtt x l.
Proof. 
intros. split.
- functional induction (nodupatt l) using nodupatt_ind.
+ eauto.
+ intro H. simpl. simpl in H.
destruct H. ++ eauto.
            ++ eauto.
+ intro H. simpl. simpl in H.
destruct H. 
 ++ eauto.
 ++ right. destruct (string_beq x a) eqn: Hxa.
     +++ rewrite stringDecF.eqb_eq in Hxa.
     rewrite  existsbAtt_InAtt in e1.
     rewrite Hxa. auto.
     +++ rewrite stringBEF.eqb_neq in Hxa. 
     apply IHl0 in H. 
     rewrite <- (InAtt_InAtt_removeAtt) in H.
     auto. auto.
- functional induction (nodupatt l) using nodupatt_ind.
+ eauto.
+ intro H. simpl. 
destruct (string_beq x a) eqn: Hxa.
++ rewrite stringDecF.eqb_eq in Hxa.
   symmetry in Hxa. eauto.
++ rewrite stringBEF.eqb_neq in Hxa.
apply InAtt_inv_noteq in H. eauto. simpl. eauto.

+ intro H. simpl. 
destruct (string_beq x a) eqn: Hxa.
++ rewrite stringDecF.eqb_eq in Hxa.
   eauto.
++ rewrite stringBEF.eqb_neq in Hxa.
apply InAtt_inv_noteq in H. right. 
rewrite (InAtt_InAtt_removeAtt) with (y:=a) in H.
apply IHl0 in H. auto. auto. eauto.
Qed.


Lemma In_InAtt_nodupatt : forall a l,
           In a l -> InAtt (fstVatt a) (nodupatt l).
Proof. intros. 
- intros. 
  rewrite InAtt_nondupatt. rewrite InAtt_In_exvatt.
  exists a. split. auto.
  destruct a eqn:Ha. simpl. 
  unfold eqbAtt. simpl.
  rewrite stringBEF.eqb_refl. auto.
Qed.



(* apply well_founded_induction.*)

Lemma NoDupAtt_nodupatt (v:vatts) : NoDupAtt (nodupatt v).
Proof. functional induction (nodupatt v) using nodupatt_ind. 
+ apply NoDupAtt_nil.
+ apply NoDupAtt_cons. rewrite InAtt_nondupatt.
  rewrite <- existsbAtt_InAtt. 
  rewrite e1. apply diff_false_true. auto.
+ apply NoDupAtt_cons. rewrite InAtt_nondupatt.
  apply notInAtt_removeAtt. apply IHl.
Qed.


Lemma nodupatt_fixed_point (v:vatts): NoDupAtt v -> nodupatt v = v.
Proof. intro H. induction H. 
simpl_nodupatt. auto.
apply nodupatt_not_in_cons with (e:=e) in H.
rewrite H. rewrite IHNoDupAtt. auto.
Qed.

Lemma nodup_remove_cons a l: In a l -> nodup string_eq_dec l 
      =a= (a :: nodup string_eq_dec (remove string_eq_dec a l)).
Proof. 
intro H. unfold equiv_atts.
intro a0. split. split.
- intro H1. simpl. destruct (string_eq_dec a a0) as [Heq|Hneq].
  + eauto.
  + right. rewrite <- remove_nodup_comm.
  apply (in_in_remove string_eq_dec). eauto.
  assumption. 
- intro H1. simpl in H1. destruct H1; subst.
  + rewrite nodup_In. exact H.
  + rewrite <- remove_nodup_comm in H0.
    apply (in_remove string_eq_dec) in H0.
    destruct H0. assumption.
- simpl. 
  destruct (string_eq_dec a a0) as [Heq|Hneq]; subst.
  + pose (remove_In string_eq_dec l a0) as HnInrm. 
    rewrite    (In_count_occ_nodup string_eq_dec _ _ H). 
    rewrite (notIn_count_occ_nodup string_eq_dec _ _ HnInrm).
    reflexivity. 
  + destruct (in_dec string_eq_dec a0 l) as [HInd|HInd].
    ++ apply (in_in_remove string_eq_dec) with (y:=a) 
       in HInd as HInrm. 
       rewrite (In_count_occ_nodup string_eq_dec _ _ HInd). 
       rewrite (In_count_occ_nodup string_eq_dec _ _ HInrm). 
       all: eauto.
    ++ assert (HnInrm: ~ In a0 (remove string_eq_dec a l)).
       apply (contrapositive _ _ (in_remove string_eq_dec _ _ _)).
       apply Classical_Prop.or_not_and. eauto.
       rewrite (notIn_count_occ_nodup string_eq_dec _ _ HInd).
       rewrite (notIn_count_occ_nodup string_eq_dec _ _ HnInrm).
       reflexivity.
Qed.

Lemma nodup_nodupatt (v:vatts) (c:config): 
nodup string_eq_dec (configVAttSet v c) =a= (configVAttSet (nodupatt v) c).
Proof.
functional induction (nodupatt v) using nodupatt_ind. 
- simpl. reflexivity.

- simpl. destruct (E[[ e]] c) eqn:He.
  + simpl. not_existsbAtt_InAtt in e1. 
    apply notInAtt_notIn_config with (c:=c) in e1.
    destruct (in_dec string_eq_dec a (configVAttSet vs c)) eqn: Hdec.
    inversion Hdec. contradiction.
    apply cons_equiv_atts. rewrite IHl. auto. reflexivity.
  + auto.

- simpl. destruct (E[[ e]] c) eqn:He.
  (* (E[[ e]] c) = true *)
  + rewrite orb_true_l. simpl. 

   destruct (in_dec string_eq_dec a (configVAttSet vs c)) as [HInd | HInd];
    (* In a [[ vs]]c *)
    try(rewrite (nodup_remove_cons a _ HInd));
    (* ~ In a [[ vs]]c *)
    try(rewrite <- (notin_remove string_eq_dec (configVAttSet vs c) a HInd)); 
     rewrite remove_removeAtt; apply cons_equiv_atts;
     exact IHl.

 (* (E[[ e]] c) = false  *)
 + rewrite orb_false_l.  
   destruct (E[[ extract_e a vs]] c) eqn:Hex.
   ++ apply extract_true_In in Hex as HIn.
      rewrite (nodup_remove_cons a _ HIn).
      rewrite remove_removeAtt; apply cons_equiv_atts;
      exact IHl.
   ++ apply extract_false_notIn in Hex as HIn.
      rewrite <- (notin_remove string_eq_dec (configVAttSet vs c) a HIn).
      rewrite remove_removeAtt. 
      exact IHl.
Qed.


Lemma nodup_equiv A A': A =a= A' -> 
      nodup string_eq_dec A =a= nodup string_eq_dec A'.
Proof. unfold equiv_atts. intros. 
specialize H with a. destruct H. 
split. 
+ repeat (rewrite nodup_In). assumption.
+ destruct (in_dec string_eq_dec a A) as [HInA|HnInA].
  ++ apply H in HInA as HInA'.
  apply (In_count_occ_nodup string_eq_dec) in HInA.
  apply (In_count_occ_nodup string_eq_dec) in HInA'.
  rewrite HInA. rewrite HInA'. reflexivity.
  ++ assert (HnInA' : ~ In a A'). rewrite <- H.
     assumption. 
     apply (notIn_count_occ_nodup string_eq_dec) in HnInA.
     apply (notIn_count_occ_nodup string_eq_dec) in HnInA'.
     rewrite HnInA. rewrite HnInA'. reflexivity.
Qed.


Lemma nodupatt_equiv A A': A =va= A' -> 
      nodupatt A =va= nodupatt A'.
Proof. unfold equiv_vatts. intros. 
repeat (rewrite <- nodup_nodupatt).
apply nodup_equiv. apply H.
Qed.

(** ------------------------------------------------------------
  nodupatt_push_annot
---------------------------------------------------------------*)

Lemma notInAtt_push_annot a A e: ~ InAtt a A ->
~ InAtt a (push_annot A e). 
induction A; intro H.
simpl. simpl in H. auto. destruct a0.
simpl. simpl in H. 
apply Classical_Prop.not_or_and in H.
destruct H.
apply Classical_Prop.and_not_or.
split. assumption. eauto.
Qed.

Lemma NoDupAtt_push_annot: forall A e, NoDupAtt (A) -> NoDupAtt (push_annot A e).
Proof. 
intros A e. induction A; intro H.
simpl. assumption.
destruct a. simpl. simpl in H.
inversion H; subst. apply NoDupAtt_cons.
apply (notInAtt_push_annot _ _ _ H2).
eauto. Qed.

Hint Resolve NoDupAtt_push_annot.

(*------------------------push_annot---------------------------*)