(** -- get_annot lemma on whole list -- *)
Set Warnings "-notation-overridden,-parsing".


Load Equiv_Lemmas.


Lemma simpl_get_annot_eq a e A: get_annot a ((ae a e)::A) = (e \/(F) (get_annot a A)).
Proof. unfold get_annot. simpl. unfold eqbElem.
simpl. rewrite stringBEF.eqb_refl.
simpl. reflexivity.
Qed.

Lemma simpl_get_annot_neq a0 a e A: a0 <> a ->
       get_annot a0 ((ae a e)::A) = (get_annot a0 A).
Proof. intro H. unfold get_annot. simpl. unfold eqbElem.
simpl. rewrite <- stringBEF.eqb_neq in H.
rewrite H. simpl. reflexivity.
Qed.

Lemma get_annot_true_In a A c: (E[[ get_annot a A]]c) = true 
<-> In a (configVElemSet A c).
Proof. split. 
{ 
induction A; intro H.
- simpl in H. discriminate H.
- destruct a0 as (a0, e0). 
  destruct (string_eq_dec a a0); subst.
  + rewrite simpl_get_annot_eq in H. 
    simpl in H. apply orb_prop in H. 
    destruct H. 
    ++ simpl. rewrite H. simpl. eauto.
    ++  simpl. destruct (E[[ e0]] c); try(simpl; 
        right); apply IHA; apply H.
  + rewrite (simpl_get_annot_neq _ _ n) in H.
    simpl. destruct (E[[ e0]] c); try(simpl; 
        right); apply IHA; apply H.
}
{ 
induction A; intro H.
- simpl in H. destruct H.
- unfold get_annot. simpl. 
  destruct a0 as (a0, e0). simpl.
  destruct (eqbElem a (ae a0 e0))eqn: Haa0;
  unfold eqbElem in Haa0; simpl in Haa0.
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

Lemma get_annot_false_notIn a A c: (E[[ get_annot a A]]c) = false 
<-> ~ In a (configVElemSet A c).
Proof. 
pose (get_annot_true_In a A c) as Hcontra.
apply contrapositive_iff in Hcontra.
rewrite not_true_iff_false in Hcontra.
symmetry in Hcontra. exact Hcontra.
Qed.

Lemma notInElem_get_annot: forall a A, ~ InElem a A -> get_annot a A = litB false.
Proof. 
intros. unfold get_annot. rewrite <- existsbElem_InElem in H.
rewrite not_true_iff_false in H. 
assert (Hf: filter (eqbElem a) A = []). rewrite <- notIn_nil.
apply existsbElem_filter. auto.
rewrite Hf. simpl. auto.
Qed.

Lemma In_get_annot a e A (H: NoDupElem A): In (ae a e) A -> 
get_annot a A = (e \/(F) litB false). 
Proof. intros.
unfold get_annot. induction A.
simpl in H0. destruct H0.
simpl in H0. inversion H; subst.
destruct H0.
+ inversion H0; subst.
simpl filter. unfold eqbElem at 1.  
rewrite stringBEF.eqb_refl. 
rewrite <- existsbElem_InElem in H3.
rewrite not_true_iff_false in H3. 
assert (Hf: filter (eqbElem a) A = []). rewrite <- notIn_nil.
apply existsbElem_filter. auto.
rewrite Hf. simpl. auto.
+ simpl filter. unfold eqbElem at 1.
simpl fstVelem.
pose (In_InElem_fstVelem _ _ H0) as HInElemA.
simpl in HInElemA. 
destruct (string_beq a a1) eqn:Haa1.
 ++ rewrite stringDecF.eqb_eq in Haa1.
    rewrite Haa1 in HInElemA. contradiction.
 ++ rewrite stringBEF.eqb_neq in Haa1.
    apply IHA. auto. auto.
Qed.

Lemma InElem_get_annot a A (HndpElemA: NoDupElem A): InElem a A -> 
exists e, In (ae a e) A /\ get_annot a A = (e \/(F) litB false). 
Proof. intros HInElemA.
apply InElem_In_exfexp in HInElemA.
destruct HInElemA as [e HInA].
(* NoDupElem A /\ In (ae a' e) A -> get_annot a' A = e *)
apply (In_get_annot _ _ HndpElemA) in HInA as Hexe.
exists e. eauto. Qed.

Lemma get_annot_equiv : forall l l' a,
l =vset= l' -> get_annot a l =e= get_annot a l'.
Proof.
intros l l' a H.
- unfold equiv_velems in H. 
unfold equivE. intro c. 
unfold equiv_elems in H. specialize H with c a.
destruct H as [HIniff Hocc].
destruct (in_dec string_eq_dec a (configVElemSet l c)) as [HInl |HnInl].
+ apply HIniff in HInl as HInl'.
  rewrite <- get_annot_true_In in HInl, HInl'.
  rewrite HInl, HInl'. reflexivity.
+ assert(HnInl': ~ In a (configVElemSet l' c)).
  rewrite HIniff in HnInl. assumption.
  rewrite <- get_annot_false_notIn in HnInl, HnInl'.
  rewrite HnInl, HnInl'. reflexivity.
Qed.