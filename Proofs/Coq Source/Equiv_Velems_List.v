(** Equivalence lemmas *)
Set Warnings "-notation-overridden,-parsing".
Require Export Logic.

Load Elem_Op_Velem.

(* list-equivalence *)
Definition equiv_elems_list : relation (list elem) := 
fun A A' => forall a, (In a A <-> In a A').

Infix "=list=" := equiv_elems_list (at level 70) : type_scope.

(* V-set equivalence-list *)
Definition equiv_velems_list : relation velems := 
fun A A' => forall c, (X[[A]]c) =list= (X[[A']]c).

Infix "=vlist=" := equiv_velems_list (at level 70) : type_scope.


(* equiv_qtype is Equivalence relation *)
Remark equiv_elems_list_refl: Reflexive equiv_elems_list.
Proof.
  intros A a. reflexivity.
Qed.

Remark equiv_elems_list_sym : Symmetric equiv_elems_list.
Proof.
  intros A A' H a.
  symmetry;
  apply H.
Qed.

Remark equiv_elems_list_trans : Transitive equiv_elems_list.
Proof.
  intros A A'' A' H1 H2 a.
  try (transitivity (In a A'')); 
         try (transitivity (count_occ string_eq_dec A'' a));
   try (apply H1);
   try (apply H2). 
Qed.

Instance eleml_Equivalence : Equivalence equiv_elems_list := {
    Equivalence_Reflexive := equiv_elems_list_refl;
    Equivalence_Symmetric := equiv_elems_list_sym;
    Equivalence_Transitive := equiv_elems_list_trans }.
    
    (* equiv_velems is Equivalence relation *)

Remark equiv_velems_list_refl: Reflexive equiv_velems_list.
Proof.
  intros A a. reflexivity.
Qed.

Remark equiv_velems_list_sym : Symmetric equiv_velems_list.
Proof.
  intros A A' H a.
  symmetry.
  apply H.
Qed.

Remark equiv_velems_list_trans : Transitive equiv_velems_list.
Proof.
  intros A A'' A' H1 H2 a.
  transitivity (configVElemSet A'' a).
    apply H1.
    apply H2.
Qed.

(** velems equivalence is an equivalence relation. *)
Instance velems_list_Equivalence : Equivalence equiv_velems_list := {
    Equivalence_Reflexive := equiv_velems_list_refl;
    Equivalence_Symmetric := equiv_velems_list_sym;
    Equivalence_Transitive := equiv_velems_list_trans }.

(* equiv_vqtype is Equivalence relation *)

Lemma equiv_list_intro: forall a l, In a l -> (a::l) =list= l.
Proof. intros. 
unfold "=list=". 
intros. split.
simpl. intro. 
destruct H0. rewrite <- H0. auto.
auto. intro. simpl. eauto.
Qed.

Lemma equiv_list_order: forall a a' l, (a::a'::l) =list= (a'::a::l).
Proof. intros. 
unfold "=list=". 
intros. split;
simpl; intro; 
destruct H; eauto;
destruct H; eauto; 
eauto.
Qed.

Lemma cons_equiv_list: forall a l1 l2, l1 =list= l2 -> (a::l1) =list= (a::l2).
Proof. 
intros. 
unfold "=list=" in H.

unfold "=list=". 
intros. split;
specialize H with (a:=a0);
destruct H.

all: simpl; intro H1; destruct H1 as [Haa0 | HIn];
[left; auto | right; eauto].

Qed.

Lemma removeElem_neq_In a a0 vs c: a0 <> a -> In a0 (X[[ vs]]c) <-> In a0 (X[[ removeElem a vs]]c).
Proof. intro Haa0.
functional induction (removeElem a vs) using removeElem_ind.
simpl. intros. reflexivity.
split; intros; simpl in H; destruct (E[[ e']] c).
+ simpl in H. destruct H. Search string_beq.
rewrite stringDecF.eqb_eq in e0. rewrite H in e0.
symmetry in e0. contradiction.
rewrite IHv in H. auto.
+ rewrite IHv in H. auto.
+ simpl. destruct (E[[ e']] c);
simpl; rewrite <-IHv in H; eauto.
+ simpl. destruct (E[[ e']] c);
simpl; rewrite <-IHv in H; eauto.
+ simpl. destruct (E[[ e']] c).
simpl. split; intro.
simpl in H. destruct H. simpl. eauto. 
rewrite IHv in H; eauto.
destruct H. simpl. eauto.
rewrite <- IHv in H; eauto.
assumption.
Qed.

Lemma removeElem_notIn a vs c:  
~ In a (X[[ vs]] c) -> X[[ vs]] c =list= X[[ removeElem a vs]] c.
Proof. intro HnIn.
functional induction (removeElem a vs) using removeElem_ind.
simpl. reflexivity.
simpl. simpl in HnIn. destruct (E[[ e']] c).
simpl in HnIn. apply not_or_and_not in HnIn.
destruct HnIn. rewrite stringDecF.eqb_eq in e0. 
symmetry in e0. contradiction.
eauto.
simpl. simpl in HnIn. destruct (E[[ e']] c).
simpl in HnIn. apply not_or_and_not in HnIn.
destruct HnIn.
apply cons_equiv_list. eauto.
eauto. Qed.

Lemma removeElem_In a vs c:  
In a (X[[ vs]] c) -> X[[ vs]] c =list= a :: X[[ removeElem a vs]] c.
Proof. intro HIn.
functional induction (removeElem a vs) using removeElem_ind.
+ simpl in HIn. inversion HIn.
+ simpl. simpl in HIn. destruct (E[[ e']] c).
simpl in HIn. 
destruct HIn. rewrite H. 
destruct (in_dec stringDecF.eq_dec a (X[[ A']] c)) eqn:HIn.
apply IHv in i as Hl. 
rewrite <- Hl. 
apply equiv_list_intro. auto.
apply removeElem_notIn in n as HnIn.
apply cons_equiv_list. eauto.
rewrite stringDecF.eqb_eq in e0. 
apply IHv in H as Hl. 
rewrite <- Hl.
rewrite <- e0. 
apply equiv_list_intro. auto.
eauto. 
+ simpl. simpl in HIn. destruct (E[[ e']] c).
simpl in HIn. 
destruct HIn. 
Search string_beq.
rewrite stringBEF.eqb_neq in e0. 
symmetry in H. contradiction.
rewrite equiv_list_order.
apply cons_equiv_list. eauto.
eauto.
Qed.

Lemma nodupelem_gen_equiv_velems_list: forall v, v =vlist= (nodupelem v).
Proof. intro v.
functional induction (nodupelem v) using nodupelem_ind;
unfold "=vlist="; unfold "=vlist=" in *; intro c; simpl.
+ reflexivity.
+ destruct (E[[ e]] c) eqn:He;
  [apply cons_equiv_list | ]; auto.
+ destruct (E[[ e]] c) eqn:He.
  (* (E[[ e]] c) = true *)
  ++ rewrite orb_true_l. 
  specialize IHv0 with c. 
  apply cons_equiv_list with (a:=a) in IHv0.
  rewrite <- IHv0. rewrite existsbElem_InElem in e1. 
  unfold "=list=".
  (* Goal: In a0 (a :: X[[ vs]] c) <-> In a0 (a :: X[[ removeElem a vs]] c) *)
  intro a0. split; intro.
  +++ (* -> *) simpl in H. destruct H. rewrite H. simpl. eauto.
  destruct (string_dec a0 a) eqn:Haa0.
  rewrite e0. simpl. eauto. 
  apply removeElem_neq_In with (vs:=vs) (c:=c) in n as HInrm.
  simpl. rewrite HInrm in H. eauto.  
  +++ (* <- *) simpl in H. destruct H. rewrite H. simpl. eauto.
  destruct (string_dec a0 a) eqn:Haa0.
  rewrite e0. simpl. eauto. 
  apply removeElem_neq_In with (vs:=vs) (c:=c) in n as HInrm.
  simpl. rewrite <- HInrm in H. eauto. 
  (* (E[[ e]] c) = false *)
  ++ simpl. destruct (E[[ get_annot a vs]] c) eqn:Hget.
  +++ (* (E[[ get_annot a vs]] c) = false *) specialize IHv0 with c. 
  apply cons_equiv_list with (a:=a) in IHv0.
  rewrite <- IHv0. apply get_annot_true_In in Hget. 
  apply removeElem_In in Hget. auto.
  +++ (* ((E[[ get_annot a vs]] c) = false *) rewrite <-IHv0. 
  apply get_annot_false_notIn in Hget. 
  apply removeElem_notIn in Hget. auto.
Qed.

