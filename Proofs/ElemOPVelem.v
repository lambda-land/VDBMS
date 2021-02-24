(** Operation on elemribute of variational elem *)
Set Warnings "-notation-overridden,-parsing".


Load get_annot_lemmas.


(* configVElemSet InElem *)

Lemma In_InElem_config: forall a A c, In a (configVElemSet A c) -> InElem a A.
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


Lemma notInElem_notIn_config: forall a A c, ~InElem a A -> ~In a (configVElemSet A c).
Proof. 
intros a A c H.
pose (In_InElem_config a A c) as H1.
apply contrapositive in H1. 
auto. auto. 
Qed.

(*----------------------------------------------------------------------*)

(* configVElemSet removeElem *)

Lemma count_occ_config_removeElem_eq a A c:
count_occ string_eq_dec (configVElemSet (removeElem a A) c) a = 0.
Proof. pose (notInElem_removeElem A a) as HnInrm.
apply notInElem_notIn_config with (c:=c) in HnInrm.
rewrite count_occ_not_In in HnInrm.
apply HnInrm.
Qed.

Lemma count_occ_config_removeElem_neq a a0 A c: a <> a0 -> 
count_occ string_eq_dec (configVElemSet (removeElem a A) c) a0 = 
count_occ string_eq_dec (configVElemSet A c) a0.
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

(* remove a  [[ A]]c = [[ removeElem a A]]c *) 
Lemma remove_removeElem a A c: 
      remove string_eq_dec a (configVElemSet A c) 
      = configVElemSet (removeElem a A) c.
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

Lemma removeElem_equiv a A A':
A =vx= A' -> removeElem a A =vx= removeElem a A'.
Proof. 
unfold equiv_velems.
simpl. unfold equiv_elems. intros.
specialize H with c a0. destruct H as [H H0].
split. 
+ split; intro H1; 
  rewrite <- In_config_exists_true in H1;
  destruct H1 as [e0 H1]; destruct H1 as [H1 H2];
  destruct (string_eq_dec a0 a) as [Heqdec | Heqdec];
  (* a0 = a *)
  try (rewrite Heqdec in H1; apply notIn_removeElem in H1; destruct H1);
  (* a0 <> a *)
  try (apply In_removeElem in H1; apply In_config_true with (c:=c) in H1;
  auto; apply H in H1; 
  rewrite <- In_config_exists_true in H1;
  destruct H1 as [e1 H1]; destruct H1 as [H1 H1e1];
  rewrite <- In_config_exists_true; exists e1;
  split; try (apply In_removeElem; eauto); try(eauto)).
  
+ destruct (string_eq_dec a a0) as [eq | neq].
  rewrite eq. repeat (rewrite count_occ_config_removeElem_eq).
  reflexivity.
  repeat (rewrite (count_occ_config_removeElem_neq _ _ neq)).
  assumption.
Qed.

(*----------------------------------------------------------------------*)

(* -- NoDupElem NoDup -- *)

Lemma NoDupElem_NoDup: forall A, NoDupElem A -> NoDup A.
Proof. intros A H. induction H as [| a e l H1 H2 IHa]. 
       + apply NoDup_nil.
       + apply NoDup_cons.
         ++ unfold not. intro H.
            unfold not in H1. apply H1.
            rewrite InElem_In_exfexp. exists e.
            auto.
         ++ auto.
Qed.

(* *)

Lemma NoDupElem_NoDup_config: forall A c, NoDupElem A -> NoDup (configVElemSet A c).
Proof. intros A c H. induction H as [| a e l H1 H2 IHa]. 
       + apply NoDup_nil.
       + simpl. destruct (E[[ e]] c) eqn: He. 
         ++ apply NoDup_cons.
            unfold not. intro H.
            unfold not in H1. apply H1.
            apply In_InElem_config in H. auto. auto.
         ++ auto.
Qed.

Lemma NoDupElem_NoDup_configVQ: forall Q c, NoDupElem (fst Q) -> NoDup (configVQtype Q c).
Proof. intros Q c. destruct Q. simpl.
       intro H. destruct (E[[ f]] c).
       apply NoDupElem_NoDup_config. apply H.
       apply NoDup_nil.
Qed.

Lemma NoDupElem_removeElem: forall a' A,
      NoDupElem A -> NoDupElem (removeElem a' A).
Proof. intros. induction H. 
+ apply NoDupElem_nil. 
+ simpl. 
  destruct (string_beq a' a) eqn:Heq.
  eauto. 
  rewrite stringBEF.eqb_neq in Heq.
  simpl. apply NoDupElem_cons.
  ++ rewrite <- InElem_InElem_removeElem.
   auto. eauto.
  ++ auto.
Qed. 

(* -- NoDupElem In configVElemSet -- *)

Lemma NoDupElem_In_notIn A a e e':
NoDupElem A -> In (ae a e) A -> (e <> e') 
-> ~ In (ae a e') A.
Proof. intros. induction A. 
- simpl in H0. destruct H0. 
- simpl in H0. simpl. 
  apply Classical_Prop.and_not_or.
  split; destruct a0 as (a0, e0);
  inversion H; subst; rewrite InElem_In_exfexp in H4. 
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

Lemma In_config_false: forall a e A c, NoDupElem A-> In (ae a e) A ->
           (E[[ e]]c) = false -> ~ In a (configVElemSet A c).
Proof. intros. induction A. 
       - simpl in H0. destruct H0.
       - simpl in H0. inversion H as [|a' e' A' HIn HNodup]; subst.
         destruct H0.
         + inversion H0; subst. simpl. rewrite H1.
           apply notInElem_notIn_config with(c:=c) in HIn. 
           auto.
         + simpl. destruct (E[[ e']] c) eqn:He'.
           ++ simpl. apply Classical_Prop.and_not_or.
              split. apply In_InElem_fstVelem in H0.
              simpl in H0. 
              destruct (string_beq a' a) eqn:Haa'.
              rewrite stringDecF.eqb_eq in Haa'.
              rewrite Haa' in HIn. contradiction.
              rewrite stringBEF.eqb_neq in Haa'.
              auto. eauto.
           ++ eauto.
Qed.



(*---------------------------------------------------------------------------*)

(*------------------------------nodupelem-------------------------------------*)

Lemma InElem_nondupelem: forall x l, InElem x (nodupelem l) <-> InElem x l.
Proof. 
intros. split.
- functional induction (nodupelem l) using nodupelem_ind.
+ eauto.
+ intro H. simpl. simpl in H.
destruct H. ++ eauto.
            ++ eauto.
+ intro H. simpl. simpl in H.
destruct H. 
 ++ eauto.
 ++ right. destruct (string_beq x a) eqn: Hxa.
     +++ rewrite stringDecF.eqb_eq in Hxa.
     rewrite  existsbElem_InElem in e1.
     rewrite Hxa. auto.
     +++ rewrite stringBEF.eqb_neq in Hxa. 
     apply IHv in H. 
     rewrite <- (InElem_InElem_removeElem) in H.
     auto. auto.
- functional induction (nodupelem l) using nodupelem_ind.
+ eauto.
+ intro H. simpl. 
destruct (string_beq x a) eqn: Hxa.
++ rewrite stringDecF.eqb_eq in Hxa.
   symmetry in Hxa. eauto.
++ rewrite stringBEF.eqb_neq in Hxa.
apply InElem_inv_noteq in H. eauto. simpl. eauto.

+ intro H. simpl. 
destruct (string_beq x a) eqn: Hxa.
++ rewrite stringDecF.eqb_eq in Hxa.
   eauto.
++ rewrite stringBEF.eqb_neq in Hxa.
apply InElem_inv_noteq in H. right. 
rewrite (InElem_InElem_removeElem) with (y:=a) in H.
apply IHv in H. auto. auto. eauto.
Qed.


Lemma In_InElem_nodupelem : forall a l,
           In a l -> InElem (fstVelem a) (nodupelem l).
Proof. intros. 
- intros. 
  rewrite InElem_nondupelem. rewrite InElem_In_exvelem.
  exists a. split. auto.
  destruct a eqn:Ha. simpl. 
  unfold eqbElem. simpl.
  rewrite stringBEF.eqb_refl. auto.
Qed.



(* apply well_founded_induction.*)

Lemma NoDupElem_nodupelem (v:velems) : NoDupElem (nodupelem v).
Proof. functional induction (nodupelem v) using nodupelem_ind. 
+ apply NoDupElem_nil.
+ apply NoDupElem_cons. rewrite InElem_nondupelem.
  rewrite <- existsbElem_InElem. 
  rewrite e1. apply diff_false_true. auto.
+ apply NoDupElem_cons. rewrite InElem_nondupelem.
  apply notInElem_removeElem. apply IHv0.
Qed.


Lemma nodupelem_fixed_point (v:velems): NoDupElem v -> nodupelem v = v.
Proof. intro H. induction H. 
simpl_nodupelem. auto.
apply nodupelem_not_in_cons with (e:=e) in H.
rewrite H. rewrite IHNoDupElem. auto.
Qed.

Lemma nodup_remove_cons a l: In a l -> nodup string_eq_dec l 
      =x= (a :: nodup string_eq_dec (remove string_eq_dec a l)).
Proof. 
intro H. unfold equiv_elems.
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

Lemma nodup_nodupelem (v:velems) (c:config): 
nodup string_eq_dec (configVElemSet v c) =x= (configVElemSet (nodupelem v) c).
Proof.
functional induction (nodupelem v) using nodupelem_ind. 
- simpl. reflexivity.

- simpl. destruct (E[[ e]] c) eqn:He.
  + simpl. not_existsbElem_InElem in e1. 
    apply notInElem_notIn_config with (c:=c) in e1.
    destruct (in_dec string_eq_dec a (configVElemSet vs c)) eqn: Hdec.
    inversion Hdec. contradiction.
    apply cons_equiv_elems. rewrite IHv0. auto. reflexivity.
  + auto.

- simpl. destruct (E[[ e]] c) eqn:He.
  (* (E[[ e]] c) = true *)
  + rewrite orb_true_l. simpl. 

   destruct (in_dec string_eq_dec a (configVElemSet vs c)) as [HInd | HInd];
    (* In a [[ vs]]c *)
    try(rewrite (nodup_remove_cons a _ HInd));
    (* ~ In a [[ vs]]c *)
    try(rewrite <- (notin_remove string_eq_dec (configVElemSet vs c) a HInd)); 
     rewrite remove_removeElem; apply cons_equiv_elems;
     exact IHv0.

 (* (E[[ e]] c) = false  *)
 + rewrite orb_false_l.  
   destruct (E[[ get_annot a vs]] c) eqn:Hex.
   ++ apply get_annot_true_In in Hex as HIn.
      rewrite (nodup_remove_cons a _ HIn).
      rewrite remove_removeElem; apply cons_equiv_elems;
      exact IHv0.
   ++ apply get_annot_false_notIn in Hex as HIn.
      rewrite <- (notin_remove string_eq_dec (configVElemSet vs c) a HIn).
      rewrite remove_removeElem. 
      exact IHv0.
Qed.


Lemma nodup_equiv A A': A =x= A' -> 
      nodup string_eq_dec A =x= nodup string_eq_dec A'.
Proof. unfold equiv_elems. intros. 
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


Lemma nodupelem_equiv A A': A =vx= A' -> 
      nodupelem A =vx= nodupelem A'.
Proof. unfold equiv_velems. intros. 
repeat (rewrite <- nodup_nodupelem).
apply nodup_equiv. apply H.
Qed.

(** ------------------------------------------------------------
  nodupelem_push_annot
---------------------------------------------------------------*)

Lemma notInElem_push_annot a A e: ~ InElem a A <->
~ InElem a (push_annot A e). 
split; induction A; intro H.
1, 3: simpl; simpl in H; auto. 
1, 2: destruct a0; simpl; simpl in H; 
apply Classical_Prop.not_or_and in H;
destruct H;
apply Classical_Prop.and_not_or;
split; [assumption | eauto].
Qed.

Lemma NoDupElem_push_annot: forall A e, NoDupElem (A) -> NoDupElem (push_annot A e).
Proof. 
intros A e. induction A; intro H.
simpl. assumption.
destruct a. simpl. simpl in H.
inversion H; subst. apply NoDupElem_cons.
rewrite <- notInElem_push_annot; try eauto.
eauto. Qed.

Hint Resolve NoDupElem_push_annot:core.

(*------------------------push_annot---------------------------*)