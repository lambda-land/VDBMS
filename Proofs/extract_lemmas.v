(** -- extract_e lemma on whole list -- *)
Set Warnings "-notation-overridden,-parsing".


Load equiv_lemms.


Lemma simpl_extract_eq a e A: extract_e a ((ae a e)::A) = (e \/(F) (extract_e a A)).
Proof. unfold extract_e. simpl. unfold eqbAtt.
simpl. rewrite stringBEF.eqb_refl.
simpl. reflexivity.
Qed.

Lemma simpl_extract_neq a0 a e A: a0 <> a ->
       extract_e a0 ((ae a e)::A) = (extract_e a0 A).
Proof. intro H. unfold extract_e. simpl. unfold eqbAtt.
simpl. rewrite <- stringBEF.eqb_neq in H.
rewrite H. simpl. reflexivity.
Qed.

Lemma extract_true_In a A c: (E[[ extract_e a A]]c) = true 
<-> In a (configVAttSet A c).
Proof. split. 
{ 
induction A; intro H.
- simpl in H. discriminate H.
- destruct a0 as (a0, e0). 
  destruct (string_eq_dec a a0); subst.
  + rewrite simpl_extract_eq in H. 
    simpl in H. apply orb_prop in H. 
    destruct H. 
    ++ simpl. rewrite H. simpl. eauto.
    ++  simpl. destruct (E[[ e0]] c); try(simpl; 
        right); apply IHA; apply H.
  + rewrite (simpl_extract_neq _ _ n) in H.
    simpl. destruct (E[[ e0]] c); try(simpl; 
        right); apply IHA; apply H.
}
{ 
induction A; intro H.
- simpl in H. destruct H.
- unfold extract_e. simpl. 
  destruct a0 as (a0, e0).
  destruct (eqbAtt a (ae a0 e0))eqn: Haa0;
  unfold eqbAtt in Haa0; simpl in Haa0.
  + simpl. apply orb_true_intro. 
    simpl in H. destruct (E[[ e0]] c). 
    ++ eauto.
    ++ right. apply IHA; apply H.
 + rewrite stringBEF.eqb_neq in Haa0. 
    simpl in H. destruct (E[[ e0]] c). 
    ++ simpl in H. destruct H. eauto.
       apply IHA. apply H.
    ++  apply IHA. apply H.
}
Qed.

Lemma extract_false_notIn a A c: (E[[ extract_e a A]]c) = false 
<-> ~ In a (configVAttSet A c).
Proof. 
pose (extract_true_In a A c) as Hcontra.
apply contrapositive_iff in Hcontra.
rewrite not_true_iff_false in Hcontra.
symmetry in Hcontra. exact Hcontra.
Qed.

Lemma notInAtt_extract: forall a A, ~ InAtt a A -> extract_e a A = litB false.
Proof. 
intros. unfold extract_e. rewrite <- existsbAtt_InAtt in H.
rewrite not_true_iff_false in H. 
assert (Hf: filter (eqbAtt a) A = []). rewrite <- notIn_nil.
apply existsbAtt_filter. auto.
rewrite Hf. simpl. auto.
Qed.

Lemma In_extract a e A (H: NoDupAtt A): In (ae a e) A -> 
extract_e a A = (e \/(F) litB false). 
Proof. intros.
unfold extract_e. induction A.
simpl in H0. destruct H0.
simpl in H0. inversion H; subst.
destruct H0.
+ inversion H0; subst.
simpl filter. unfold eqbAtt at 1.  
rewrite stringBEF.eqb_refl. 
rewrite <- existsbAtt_InAtt in H3.
rewrite not_true_iff_false in H3. 
assert (Hf: filter (eqbAtt a) A = []). rewrite <- notIn_nil.
apply existsbAtt_filter. auto.
rewrite Hf. simpl. auto.
+ simpl filter. unfold eqbAtt at 1.
simpl fstVatt.
pose (In_InAtt_fstVatt _ _ H0) as HInAttA.
simpl in HInAttA. 
destruct (string_beq a a1) eqn:Haa1.
 ++ rewrite stringDecF.eqb_eq in Haa1.
    rewrite Haa1 in HInAttA. contradiction.
 ++ rewrite stringBEF.eqb_neq in Haa1.
    apply IHA. auto. auto.
Qed.

Lemma InAtt_extract a A (HndpAttA: NoDupAtt A): InAtt a A -> 
exists e, In (ae a e) A /\ extract_e a A = (e \/(F) litB false). 
Proof. intros HInAttA.
apply InAtt_In_exfexp in HInAttA.
destruct HInAttA as [e HInA].
(* NoDupAtt A /\ In (ae a' e) A -> extract_e a' A = e *)
apply (In_extract _ _ HndpAttA) in HInA as Hexe.
exists e. eauto. Qed.

Lemma extract_equiv : forall l l' a,
l =va= l' -> extract_e a l =e= extract_e a l'.
Proof.
intros l l' a H.
- unfold equiv_vatts in H. 
unfold equivE. intro c. 
unfold equiv_atts in H. specialize H with c a.
destruct H as [HIniff Hocc].
destruct (in_dec string_eq_dec a (configVAttSet l c)) as [HInl |HnInl].
+ apply HIniff in HInl as HInl'.
  rewrite <- extract_true_In in HInl, HInl'.
  rewrite HInl, HInl'. reflexivity.
+ assert(HnInl': ~ In a (configVAttSet l' c)).
  rewrite HIniff in HnInl. assumption.
  rewrite <- extract_false_notIn in HnInl, HnInl'.
  rewrite HnInl, HnInl'. reflexivity.
Qed.