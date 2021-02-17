(** Variational relational algebra lemmas *)
Set Warnings "-notation-overridden,-parsing".
Import Init.Datatypes.
Import Coq.Init.Nat.
Require Export List.
Require Export Logic.
Import Coq.Lists.List.ListNotations.

Load configdistUnionInter.

Module VRA_varPrsrvtn_thm.

(** ------------------------------------------------------------
  equiv_qtype_bool correct quiv
---------------------------------------------------------------*)

Lemma equiv_qtype_bool_correct: forall A A', 
   equiv_qtype_bool A A' = true <-> equiv_qtype A A'.
Proof.  intros. split; intro H;
simpl in H; 
generalize dependent A'; induction A as [| a A IHA].
(* -> *)
- intros. simpl in H. destruct A'. simpl. 
split; reflexivity.
discriminate H.
- intros. simpl in H. destruct (set_mem string_eq_dec a A') eqn: Hsetmem.
+ apply IHA in H. apply equiv_qtype_set_remove_cons.
apply (set_mem_correct1 string_eq_dec). all: assumption.
+ discriminate H. 
(* <- *)
- intros A' H. simpl in H. destruct A'. simpl. 
reflexivity. unfold equiv_qtype in H.
unfold equiv_elems in H. 
apply forall_dist_and in H. destruct H.
simpl count_occ in H0 at 1. symmetry in H0.
rewrite count_occ_inv_nil in H0. 
symmetry in H0.
apply nil_cons in H0. destruct H0.
- intros.  simpl. 
destruct (set_mem string_eq_dec a A') eqn: Hsetmem.
apply IHA. rewrite equiv_qtype_set_remove_cons. assumption.
apply (set_mem_correct1 string_eq_dec). assumption.
unfold equiv_qtype in H; unfold equiv_elems in H.
specialize H with a. destruct H.
apply (set_mem_complete1 string_eq_dec) in Hsetmem. 
rewrite <- H in Hsetmem. simpl in Hsetmem.
apply Classical_Prop.not_or_and in Hsetmem. destruct Hsetmem.
contradiction.
Qed.

Lemma equiv_qtype_bool_refl A: equiv_qtype_bool A A = true.
Proof. rewrite equiv_qtype_bool_correct. reflexivity. Qed.

Lemma transitive_prev A A' B B': 
A =a= B -> A' =a= B' -> (A =a= A' <-> B =a= B').
Proof. intros. split; intro H1;
[pose (transitivity (symmetry H) (transitivity H1 H0))|
 pose (transitivity H (transitivity H1 (symmetry H0)))];
assumption. Qed.

Lemma equiv_qtype_bool_equiv A A' B B' (HA: NoDup A) (HA': NoDup A')
(HB: NoDup B) (HB': NoDup B'):
A =a= B -> A' =a= B' -> equiv_qtype_bool A A' = equiv_qtype_bool B B'.
Proof. intros. 
destruct (equiv_qtype_bool A A') eqn: Htf;
[|rewrite <- not_true_iff_false in Htf];
rewrite equiv_qtype_bool_correct in Htf;
rewrite (transitive_prev H H0) in Htf;
rewrite  <- equiv_qtype_bool_correct in Htf;
[|rewrite not_true_iff_false in Htf];
rewrite Htf; reflexivity. 
Qed.

(** ------------------------------------------------------------
  sublist_bool correct
---------------------------------------------------------------*)

Lemma sublist_bool_correct: forall A A' , sublist_bool A A' = true
                        <-> sublist A A'.
Proof. 
intros A A'. generalize dependent A'. induction A. 
+ split; intro H.
  ++ unfold sublist. intro x. split.
     simpl. intro HIn. destruct HIn.
     simpl. Lia.lia.
  ++ simpl. reflexivity.
+ intro A'. split; intro H.
  ++ simpl in H.
     destruct (set_mem string_eq_dec a A') eqn: Hsetmem.
     +++ apply set_mem_correct1 in Hsetmem.
         unfold sublist. intro x. 
         apply IHA in H.
         unfold sublist in H. specialize H with x.
         destruct H. split.
         ++++ intro. 
         simpl in H1. destruct H1; subst.
         assumption. apply H in H1. 
         apply (set_remove_1 string_eq_dec _ _ _ H1).
         ++++ simpl. destruct (string_eq_dec a x); subst.
         apply (count_occ_set_remove_In 
         string_eq_dec) in Hsetmem as H1. Lia.lia. 
         apply (count_occ_set_remove_neq string_eq_dec) 
         with (l:= A') in n. Lia.lia.
    +++ discriminate H. 
  ++ simpl. destruct (set_mem string_eq_dec a A') eqn: Hsetmem.
     +++ apply set_mem_correct1 in Hsetmem.
         rewrite IHA. unfold sublist. intro x. unfold sublist in H.
        specialize H with x. destruct H. split.
        ++++ intro H1. simpl in H. simpl in H0.
        destruct (string_eq_dec a x); subst.
        {
         rewrite (count_occ_In string_eq_dec) in H1.
         rewrite (count_occ_In string_eq_dec). 
         apply gt_S_n. 
         rewrite (count_occ_set_remove_In _ _ _ Hsetmem). Lia.lia.
        }
        {
         apply (count_occ_set_remove_neq string_eq_dec A') in n.
         rewrite (count_occ_In string_eq_dec). rewrite n. 
         rewrite (count_occ_In string_eq_dec) in H1. Lia.lia.
        }
        ++++ simpl in H0. 
        destruct (string_eq_dec a x); subst.
        apply (count_occ_set_remove_In string_eq_dec) in Hsetmem. 
        Lia.lia. apply (count_occ_set_remove_neq string_eq_dec A') in n.
        Lia.lia. 
     +++ unfold sublist in H. specialize H with a.
         destruct H. apply set_mem_complete1 in Hsetmem.
         rewrite (count_occ_not_In string_eq_dec) in Hsetmem. 
         rewrite Hsetmem in H0. simpl in H0. destruct (string_eq_dec a a).
         Lia.lia. contradiction. 
Qed.

Lemma sublist_bool_correct': forall A A' , (sublist_bool A A' = false)
                        <-> (~ sublist A A').
Proof. intros. rewrite <- not_true_iff_false. unfold not.
apply contrapositive_iff. symmetry. apply sublist_bool_correct. Qed.

Lemma equiv_sublist_bool: forall A B B' , 
     B =a= B' -> sublist_bool A B = sublist_bool A B'.
Proof. intros A B B' H. destruct (sublist_bool A B) eqn:Hsb;
[ rewrite sublist_bool_correct  in Hsb |
  rewrite sublist_bool_correct' in Hsb ];
rewrite (equiv_sublist _ H) in Hsb;
[ rewrite <- sublist_bool_correct  in Hsb |
  rewrite <- sublist_bool_correct' in Hsb ];
eauto.
Qed.

(** ------------equiv_bool correct ------------------------*)

Lemma is_disjoint_bool_correct A B: is_disjoint_bool A B = true <-> elems_inter A B = [].
unfold is_disjoint_bool. destruct (elems_inter A B). 
split; intro; reflexivity. split; intro H; discriminate H.
Qed.

(* -----------------------------------------------------
  | Relation-E inverse
  | e |= vq : A'^e' ->
  |   ~sat (e' /\ (~e)) (= e' -> e)
  | Type annotation e' is more specific than context e.
   -----------------------------------------------------
*)
Theorem context_type_rel : forall e S vq A' e',
       { e , S |= vq | (A', e') } -> 
           ~ sat (  e' /\(F) (~(F) (e)) ).
Proof. intros e S vq. generalize dependent e. induction vq. (* subst. *)
       - intros. inversion H; subst. (*assumption.*) rewrite not_sat_not_prop. 
         rewrite <- sat_taut_comp.
         intros. simpl in H0. apply andb_true_iff with (b2:=(E[[ e'0]] c)). assumption.
       - intros. inversion H; subst. apply IHvq in H5. assumption.
       - intros. inversion H; subst.
         rewrite not_sat_not_prop. rewrite <- sat_taut_comp.
         intros. simpl in H0. 
         apply andb_prop in H0. destruct H0. assumption.
       - intros. inversion H; subst. rewrite not_sat_not_prop. 
         unfold not_sat. intros.
         destruct (E[[ e1]] c) eqn:E1.
         + rewrite <- sat_taut_comp_inv_c. intros. simpl. 
         rewrite E1. simpl. 
         apply IHvq1 in H4.  rewrite not_sat_not_prop in H4. 
         rewrite <- sat_taut_comp in H4. specialize H4 with c.
         apply H4 in E1. simpl in E1. apply andb_prop in E1. 
         destruct E1. rewrite <- H1, H0. reflexivity.
         + rewrite <- sat_taut_comp_inv_c. intros. simpl.
         rewrite E1. simpl.
         apply IHvq2 in H8.  rewrite not_sat_not_prop in H8. 
         rewrite <- sat_taut_comp_inv in H8. specialize H8 with c.
         apply H8. simpl. rewrite H0. simpl. reflexivity.
       - intros. inversion H; subst.
         apply IHvq1 in H6. apply IHvq2 in H7. 
         rewrite not_sat_not_prop. rewrite <- sat_taut_comp.
         intros. simpl in H0.
         destruct (E[[ e1]] c) eqn:E1. 
         + rewrite not_sat_not_prop in H6. rewrite <- sat_taut_comp in H6.
         specialize H6 with c. auto. 
         + (*rewrite andb_false_l in H0. discriminate H0.*)
         rewrite not_sat_not_prop in H7. 
         rewrite <- sat_taut_comp in H7.
         specialize H7 with c. auto.
       - intros. inversion H; subst. apply IHvq1 in H6. assumption.
Qed. 


(* -----------------------------------------------------------
  | Variation Preservation : 
  |  e |= vq : A  ->
  |    forall c, Q[[vq]]c :: T[[A]]c 
  | where :  = vtype (type derivation of variational query) 
  |       :: = type' (type derivation of plain query)
  |       Q  = configVQuery (configuration of variational query)
  |       T  = configVQtype (configuration of variational type)
   ------------------------------------------------------------
*)

(*
Comment: we are proving variation preservation theorem 
for Variational database and 

*)

Lemma addannot_config_true Q e c: (E[[ e]] c) = true -> (QT[[ Q ^^ e]] c) = (QT[[ Q]] c).
intro H0.  simpl. rewrite H0. rewrite andb_true_r. unfold configaVelems. destruct Q.
  simpl. reflexivity. Qed.
  
Lemma type__configVRelS rn A' e' c: ||= rel (R[[ (rn, (A', e'))]] c) 
                                  = (if E[[ e']] c then A[[ A']] c else []).
unfold configVRelS. simpl. destruct (E[[ e']] c); reflexivity. Qed.

Lemma AE_QT Q c: (AE[[ Q]] c) = (QT[[ Q]] c). eauto. Qed.

Theorem variation_preservation_cond : forall e Q vc, 
       { e , Q |- vc } ->
       forall c, (E[[e]] c) = true ->
          ( (QT[[ Q]] c) ||- (C[[ vc]] c)) = true.
Proof. intros e Q vc H c He. 
induction H; destruct Q as (Aq, eq).
{ simpl "||-". reflexivity. }
(*all: destruct (E[[ eq]] c) eqn: Heq.*)
{ simpl. reflexivity. }
{ simpl. reflexivity. }
{ simpl "||-". apply IHvcondtype in He.
simpl in He. rewrite He. reflexivity. }
1, 2: simpl "||-"; apply IHvcondtype1 in He as He1;
apply IHvcondtype2 in He as He2;
simpl in He1, He2; rewrite He1, He2; reflexivity.
- simpl "||-". simpl in IHvcondtype1, IHvcondtype2.
destruct (E[[ e']] c) eqn: He'.
rewrite andb_true_r in IHvcondtype1. 
apply IHvcondtype1 in He as He1. eauto.
simpl in *. rewrite andb_true_r in IHvcondtype2.
apply IHvcondtype2 in He as He2. eauto.
Qed.

Theorem variation_preservation : forall e S vq A, 
       { e , S |= vq | A } ->
       forall c, E[[e]]c = true ->
           ||= (Q[[ vq]]c) =a= QT[[ A]]c.
Proof.
  intros e S vq A H c H0. 
   induction H as [e S HndpRS HndpAS 
                   rn A' HndpA' e' 
                   HInVR 
                   |
                   e S HndpRS HndpAS vq HndpvQ
                   e' A' HndpAA' Q HndpQ
                   Hq IHHq Hsbsmp
                   |
                   e e' S HndpRS HndpAS 
                   vq1 HndpvQ1 vq2 HndpvQ2
                   A1 HndpAA1 e1 A2 HndpAA2 e2 
                   Hq1 IHHq1 Hq2 IHHq2
                   | 
                   e S HndpRS HndpAS 
                   vq1 HndpvQ1 vq2 HndpvQ2
                   A1 HndpAA1 e1 A2 HndpAA2 e2 
                   Hq1 IHHq1 Hq2 IHHq2 HInter 
                   | 
                   e S HndpRS HndpAS 
                   vq1 HndpvQ1 vq2 HndpvQ2
                   A1 HndpAA1 e1 A2 HndpAA2 e2 op
                   Hq1 IHHq1 Hq2 IHHq2 HEquiv 
                   |
                   e S HndpRS HndpAS
                   vq HndpvQ A HndpAA e' vc 
                   Hq IHHq HCond
                   ].

 (** ----------------------------- Relation - E ----------------------------- *) 
  - 
  (* H0 : (E[[ e]] c) = true
     -----------------------------------------------
     ||= (Q[[ rel_v (rn, (A', e'))]] c) =a= (QT[[ (A', e /\(F) e')]] c)
  *)
  unfold configVQuery, configVQtype, configaVelems. (*"Q[[_]]c", "QT[[_]]c", "AE[[_]]c".*) simpl semE. 
  (* H0 : (E[[ e]] c) = true
     -----------------------------------------------
     ||= rel (R[[ (rn, (A', e'))]] c) =a=
                      (if (E[[ e]] c) && (E[[ e']] c) then A[[ A']] c else [])
  *)
  (* (E[[ e]] c) = true *)
  rewrite H0. rewrite andb_true_l. 
  (* Proved by definitions configVRelS and ||= rel (rn, A) = A*)
  rewrite type__configVRelS. reflexivity.

 (** ----------------------------- Project - E ----------------------------- *)
  - 
  (* Hq: {e, S |= vq | (A', e')} 
     Hsbsmp: subsump_vqtype (Q ^^ e) (A', e')
     -----------------------------------------
     ||= (Q[[ proj_v Q vq]] c) =a= (QT[[ Q ^^ e]] c)
  *)
  (*~ unfold ||=. AE = QT. Simplify IHHq with (E[[ e]] c) = true. ~*)
  simpl type_. rewrite AE_QT. unfold subsump_qtype_bool. apply IHHq in H0 as IHHq'. clear IHHq.
  (* Hq: {e, S |= vq | (A', e')} 
     Hsbsmp: subsump_vqtype (Q ^^ e) (A', e')
     IHHq' : ||= (Q[[ vq]] c) =a= (QT[[ (A', e')]] c)
     -----------------------------------------
     if sublist_bool (QT[[ Q]] c) (||= (Q[[ vq]] c)) then 
          QT[[ Q]] c  =a= (QT[[ Q ^^ e]] c)
  *)
  (* rewrite IHHq' in goal *)
  rewrite (equiv_sublist_bool _ IHHq'). 
  (* Hq: {e, S |= vq | (A', e')} 
     Hsbsmp: subsump_vqtype (Q ^^ e) (A', e')
     -----------------------------------------
     if sublist_bool (QT[[ Q]] c) (QT[[ (A', e')]] c) then 
          QT[[ Q]] c  =a= (QT[[ Q ^^ e]] c)
  *)
  (*~ By defintion, subsump_vqtype A B = sublist QT[[A]] QT[[B]] ~*)
  unfold subsump_vqtype in Hsbsmp. specialize Hsbsmp with c.
  (* Hq: {e, S |= vq | (A', e')} 
     Hsbsmp : sublist (QT[[ Q ^^ e]] c) (QT[[ (A', e')]] c)
     -----------------------------------------
     if sublist_bool (QT[[ Q]] c) (QT[[ (A', e')]] c) then 
         QT[[ Q]] c  =a= (QT[[ Q ^^ e]] c)
  *)
  (*~ (E[[ e]] c) = true -> (QT[[ Q ^^ e]] c) = (QT[[ Q]] c)  ~*)
  rewrite (addannot_config_true _ _ _ H0) in Hsbsmp. rewrite (addannot_config_true _ _ _ H0).
  (* Hq: {e, S |= vq | (A', e')} 
     Hsbsmp : sublist (QT[[ Q]] c) (QT[[ (A', e')]] c)
     -----------------------------------------
     if sublist_bool (QT[[ Q]] c) (QT[[ (A', e')]] c) then 
         QT[[ Q]] c  =a= (QT[[ Q]] c)
  *)
  (*~ Proved by sublist A B <-> sublist_bool A B = true ~*)
  rewrite <- sublist_bool_correct in Hsbsmp. rewrite Hsbsmp.
  reflexivity.

 (**  ------------------------------- Choice - E ------------------------------ *)
 - 
 (* Hq1 : {e /\(F) e', S |= vq1 | (A1, e1)}
    Hq2 : {e /\(F) ~(F) e', S |= vq2 | (A2, e2)}
    H0 : (E[[ e]] c) = true
    IHHq1 : (E[[ e /\(F) e']] c) = true -> ||= (Q[[ vq1]] c) =a= (QT[[ (A1, e1)]] c)
    IHHq2 : (E[[ e /\(F) ~(F) e']] c) = true -> ||= (Q[[ vq2]] c) =a= (QT[[ (A2, e2)]] c)
    ----------------------------------------------------------
    ||= (Q[[ chcQ e' vq1 vq2]] c) =a= (QT[[ vqtype_union_vq (A1, e1) (A2, e2)]] c)
 *)
 (*~ Hq1 Hq2: contex_typeannot_rel -> {e, _ |= _ | (_, e')} -> (~e -> ~e')  ~*)
    apply context_type_rel in Hq1. rewrite not_sat_not_prop, <- sat_taut_comp_inv in Hq1.
    apply context_type_rel in Hq2. rewrite not_sat_not_prop, <- sat_taut_comp_inv in Hq2. 
    specialize Hq1 with c. specialize Hq2 with c. 
 (*~ remove e from Hypotheses with (E[[ e]] c) = true ~*)
    simpl semE in *. rewrite H0 in *. rewrite andb_true_l in *. Search negb.
    rewrite negb_false_iff in Hq2. rewrite negb_true_iff in IHHq2. 
 (* Hq1 :  (E[[ e']] c) = false -> (E[[ e1]] c) = false
    Hq2 :  (E[[ e']] c) = true  -> (E[[ e2]] c) = false
    IHHq1 :(E[[ e']] c) = true  -> ||= (Q[[ vq1]] c) =a= (QT[[ (A1, e1)]] c)
    IHHq2 :(E[[ e']] c) = false -> ||= (Q[[ vq2]] c) =a= (QT[[ (A2, e2)]] c)
    ----------------------------------------------------------
    ||= (Q[[ chcQ e' vq1 vq2]] c) =a= (QT[[ vqtype_union_vq (A1, e1) (A2, e2)]] c)
 *)
 (*~ (Q[[ chcQ e' vq1 vq2]] c) -> (if E[[ e']] c then Q[[ vq1]] c else Q[[ vq2]] c) ~*)
    simpl configVQuery.
 (*~ (QT[[ vqtype_union_vq A B]] c) =a= elems_union (QT[[A]] c) (QT[[B]] c)~*)
    rewrite configVQType_dist_vqtype_union_vq; try assumption.
    repeat (rewrite configVQType_push_annot).
 (*~(E[[ e']] c) = true -> 
    (E[[ e2]] c) = false -> elems_union (QT[[ (A1, e1)]] c) (QT[[ (A2, e2)]] c) = (QT[[ (A1, e1)]] c) ~*)
    assert(Hq1': (E[[ e']] c) = true -> elems_union (QT[[ (A1, e1)]] c) (QT[[ (A2, e2)]] c) = (QT[[ (A1, e1)]] c)).
    intro. apply Hq2 in H. simpl. rewrite H. eauto.
 (*~(E[[ e']] c) = false ->  
    (E[[ e1]] c) = false -> elems_union (QT[[ (A1, e1)]] c) (QT[[ (A2, e2)]] c) = (QT[[ (A2, e2)]] c) ~*)
    assert(Hq2': (E[[ e']] c) = false -> elems_union (QT[[ (A1, e1)]] c) (QT[[ (A2, e2)]] c) =a= (QT[[ (A2, e2)]] c)).
    intro. apply Hq1 in H. simpl. rewrite H. rewrite elems_union_nil_l. reflexivity.
    destruct ( E[[ e2]] c); [ apply NoDupElem_NoDup_config | apply NoDup_nil]; auto.
 (* IHHq1 :(E[[ e']] c) = true  -> ||= (Q[[ vq1]] c) =a= (QT[[ (A1, e1)]] c)
    IHHq2 :(E[[ e']] c) = false -> ||= (Q[[ vq2]] c) =a= (QT[[ (A2, e2)]] c)
    Hq1' : (E[[ e']] c) = true ->
       elems_union (QT[[ (A1, e1)]] c) (QT[[ (A2, e2)]] c) = (QT[[ (A1, e1)]] c)
    Hq2' : (E[[ e']] c) = false ->
       elems_union (QT[[ (A1, e1)]] c) (QT[[ (A2, e2)]] c) =a= (QT[[ (A2, e2)]] c)
    ----------------------------------------------------------
    ||= (if E[[ e']] c then Q[[ vq1]] c else Q[[ vq2]] c) =a= elems_union (QT[[ (A1, e1)]] c) (QT[[ (A2, e2)]] c)
 *)
 
    destruct (E[[ e']] c) eqn: He'. 
 
 (* He'   :(E[[ e']] c) = true
    IHHq1 :||= (Q[[ vq1]] c) =a= (QT[[ (A1, e1)]] c)
    Hq1'  :elems_union (QT[[ (A1, e1)]] c) (QT[[ (A2, e2)]] c) = (QT[[ (A1, e1)]] c)
    ----------------------------------------------------------
    ||= (Q[[ vq1]] c) =a= elems_union (QT[[ (A1, e1)]] c) (QT[[ (A2, e2)]] c)
 *)
    rewrite Hq1'; try reflexivity. apply IHHq1; try reflexivity.
 (* He'   :(E[[ e']] c) = false
    IHHq2 : ||= (Q[[ vq2]] c) =a= (QT[[ (A2, e2)]] c)
    Hq2'  : elems_union (QT[[ (A1, e1)]] c) (QT[[ (A2, e2)]] c) =a= (QT[[ (A2, e2)]] c)
    ----------------------------------------------------------
    ||= (Q[[ vq1]] c) =a= elems_union (QT[[ (A1, e1)]] c) (QT[[ (A2, e2)]] c)
 *)
    rewrite Hq2'; try reflexivity. apply IHHq2; try reflexivity.
  

 (**  ------------------------------- Product - E ------------------------------ *)
  - 
 (* HInter : velems_inter A1 A2 =va= []
    H0 : (E[[ e]] c) = true
    IHHq1 : (E[[ e]] c) = true -> ||= (Q[[ vq1]] c) =a= (QT[[ (A1, e1)]] c)
    IHHq2 : (E[[ e]] c) = true -> ||= (Q[[ vq2]] c) =a= (QT[[ (A2, e2)]] c)
    ----------------------------------------------------------
    ||= (Q[[ prod_v vq1 vq2]] c) =a= (QT[[ vqtype_union_vq (A1, e1) (A2, e2)]] c)
 *)
 (*~ apply E[[ e]] c) = true in Inductive H ~*)
    apply IHHq2 in H0 as IHHq2'. apply IHHq1 in H0 as IHHq1'. 
    clear IHHq1. clear IHHq2.
 (*~ (QT[[ vqtype_union_vq A B]] c) =a= elems_union (QT[[A]] c) (QT[[B]] c)~*)
    rewrite configVQType_dist_vqtype_union_vq; try assumption.
    repeat (rewrite configVQType_push_annot).
 (*~ ||= (Q[[ prod_v vq1 vq2]] c) ||= prod (Q[[ vq1]] c) (Q[[ vq2]] c)~*)
    simpl configVQuery.
 (*
   ----------------------------------------------------
   ||= prod (Q[[ vq1]] c) (Q[[ vq2]] c) =a= elems_union (QT[[ (A1, e1)]] c) (QT[[ (A2, e2)]] c)
 *)
    simpl type_. 
 (* HInter : velems_inter A1 A2 =va= []
    ----------------------------------------------------
    if is_disjoint_bool (||= (Q[[ vq1]] c)) (||= (Q[[ vq2]] c))
     elems_union (||= (Q[[ vq1]] c)) (||= (Q[[ vq2]] c)) =a= elems_union (QT[[ (A1, e1)]] c) (QT[[ (A2, e2)]] c)
 *)

 (*~ velems_inter A1 A2 =va= [] -> elems_inter [[A1]]c [[A2]]c =a= [] ~*)
    unfold equiv_velems in HInter. unfold vqtype_inter_vq, equiv_vqtype in HInter. 
    specialize HInter with c. simpl in HInter.
    rewrite configVElemSet_dist_velems_inter in HInter; try assumption.
    assert (HInter': elems_inter (QT[[ (A1, e1)]] c) (QT[[ (A2, e2)]] c) =a= [] ).
    simpl. destruct (E[[ e1]] c); [ destruct (E[[ e2]] c); [ assumption |
    rewrite elems_inter_nil_r; reflexivity] | rewrite elems_inter_nil_l; reflexivity ].
 (* HInter' : elems_inter (QT[[ (A1, e1)]] c) (QT[[ (A2, e2)]] c) =a= []
    ----------------------------------------------------
    if is_disjoint_bool (||= (Q[[ vq1]] c)) (||= (Q[[ vq2]] c))
     elems_union (||= (Q[[ vq1]] c)) (||= (Q[[ vq2]] c)) =a= elems_union (QT[[ (A1, e1)]] c) (QT[[ (A2, e2)]] c)
 *)

 (*~ is_disjoint_bool A B = true -> elems_inter A B = [] ~*)
    rewrite (is_disjoint_bool_equiv) with (B := (QT[[(A1, e1)]]c)) (B':= (QT[[(A2, e2)]] c)); try assumption.
    apply nil_equiv_eq in HInter'. rewrite <- is_disjoint_bool_correct in HInter'. rewrite HInter'.
 (* IHHq1' : ||= (Q[[ vq1]] c) =a= (QT[[ (A1, e1)]] c)
    IHHq2' : ||= (Q[[ vq2]] c) =a= (QT[[ (A2, e2)]] c)
    ----------------------------------------------------
    elems_union (||= (Q[[ vq1]] c)) (||= (Q[[ vq2]] c)) =a= elems_union (QT[[ (A1, e1)]] c) (QT[[ (A2, e2)]] c)
 *)
 (*~ Proved by set_union_quiv ~*)
   rewrite (set_union_equiv) with (B := (QT[[(A1, e1)]]c)) (B':= (QT[[(A2, e2)]]c)); try (eauto; reflexivity).
 (*~ NoDup assumptions ~*)
    1, 2, 5, 6: try(apply (NoDup_equiv_elems IHHq1')); try(apply (NoDup_equiv_elems IHHq2')).

    1, 3, 5, 7   : simpl; destruct ( E[[ e1]] c).
    9, 10, 11, 12: simpl; destruct ( E[[ e2]] c).
    all: try(apply NoDupElem_NoDup_config; auto); try (apply NoDup_nil).

 (**  ------------------------------- Select - E ------------------------------ *)
 (**  ------------------------------- SetOp - E ------------------------------ *)
 - 
 (* HEquiv : (A1, e1) =T= (A2, e2)
    H0 : (E[[ e]] c) = true
    IHHq1 : (E[[ e]] c) = true -> ||= (Q[[ vq1]] c) =a= (QT[[ (A1, e1)]] c)
    IHHq2 : (E[[ e]] c) = true -> ||= (Q[[ vq2]] c) =a= (QT[[ (A2, e2)]] c)
    ----------------------------------------------------------
    ||= (Q[[ setU_v op vq1 vq2]] c) =a= (QT[[ (A1, e1)]] c)
 *)
 (*~ apply E[[ e]] c) = true in Inductive H ~*)
    apply IHHq2 in H0 as IHHq2'. apply IHHq1 in H0 as IHHq1'. 
    clear IHHq1. clear IHHq2.
 
 (*~ ||= (Q[[ setU_v vq1 vq2]] c) ||= prod (Q[[ vq1]] c) (Q[[ vq2]] c)~*)
    simpl configVQuery.
 (* IHHq1' : ||= (Q[[ vq1]] c) =a= (QT[[ (A1, e1)]] c)
    IHHq2' : ||= (Q[[ vq2]] c) =a= (QT[[ (A2, e2)]] c)
    ----------------------------------------------------
    ||= setU op (Q[[ vq1]] c) (Q[[ vq2]] c) =a= (QT[[ (A1, e1)]] c)
 *)
    simpl type_. 
 (* HEquiv : (A1, e1) =T= (A2, e2)
    ----------------------------------------------------
    if equiv_qtype_bool (||= (Q[[ vq1]] c)) (||= (Q[[ vq2]] c))
               then ||= (Q[[ vq1]] c) =a= (QT[[ (A1, e1)]] c)
 *)
 (*~  (A1, e1) =T= (A2, e2) -> (QT[[ (A1, e1)]] c) =a= (QT[[ (A2, e2)]] c) ~*)
  apply configVQtype_equiv with (c:=c) in HEquiv. rewrite <-IHHq1', <-IHHq2' in HEquiv.
 (*~ Proved by A =a= B -> equiv_qtype_bool A B = true ~*)
  rewrite <- equiv_qtype_bool_correct in HEquiv. rewrite HEquiv. assumption.

  - apply IHHq in H0 as Htype_. 
    simpl configVQuery.
    simpl type_. 
    
 (* HCond : {e, (A, e') |- vc}
    Htype_ : ||= (Q[[ vq]] c) =a= (QT[[ (A, e')]] c)
    ----------------------------------------------------
    (if (QT[[ (A, e')]] c) ||- (C[[ vc]] c) 
                then ||= (Q[[ vq]] c) else []) =a= (QT[[ (A, e')]] c)
  *)
  
  (* {e, (A, e') |- vc} -> (QT[[ (A, e')]] c) ||- (C[[ vc]] c) = true *)
  
  apply variation_preservation_cond with (c:=c) in HCond.
  
 (* HCond : (QT[[ (A, e')]] c) ||- (C[[ vc]] c) = true
    Htype_ : ||= (Q[[ vq]] c) =a= (QT[[ (A, e')]] c)
    ----------------------------------------------------
    (if (||= (Q[[ vq]] c)) ||- (C[[ vc]] c) 
                   then ||= (Q[[ vq]] c) else []) =a= (QT[[ (A, e')]] c)
  *) 
  
 (*~ v-condition (C[[ vc]] c) is well formed in all equivalent contexts:
      Htype_:      ||= (Q[[ vq]] c) =a= (QT[[ (A, e')]] c) -> 
      HCond_:  ||= (Q[[ vq]] c) ||- (C[[ vc]] c) = (QT[[ (A, e')]] c) ||- (C[[ vc]] c) ~*)
  
  apply condtype_equiv with (c:=(C[[ vc]] c)) in Htype_ as HCond_.   
  
 (* HCond : (QT[[ (A, e')]] c) ||- (C[[ vc]] c) = true
    Htype_ : ||= (Q[[ vq]] c) =a= (QT[[ (A, e')]] c)
    HCond_ : (||= (Q[[ vq]] c)) ||- (C[[ vc]] c) = (QT[[ (A, e')]] c) ||- (C[[ vc]] c)
    ----------------------------------------------------
    (if (||= (Q[[ vq]] c)) ||- (C[[ vc]] c) 
                          then ||= (Q[[ vq]] c) else []) =a= (QT[[ (A, e')]] c)
  *) 
  
  rewrite HCond_, HCond. assumption. auto.
Qed.


End VRA_varPrsrvtn_thm.


(** vcond supposed to be*)
(*Theorem variation_preservation_cond : forall e Q vc, 
       { e , Q |- vc } ->
       forall c, (E[[e]] c) = true ->
          ( (QT[[ Q]] c) ||- (C[[ vc]] c)) = true.
Proof. intros e Q vc H c He. 
induction H; destruct Q as (Aq, eq).
{ simpl "||-". reflexivity. }
(*all: destruct (E[[ eq]] c) eqn: Heq.*)
{ simpl. destruct (E[[ e']] c) eqn:He'. 
apply In_config_true with (c:=c) in H; try auto. 
rewrite configVElemSet_push_annot in H. simpl in H.
destruct (E[[ eq]] c) eqn: Heq.
simpl "||-". rewrite <- existsb_In_elem in H. 
rewrite H. reflexivity. eauto. eauto. }
{ simpl. destruct ((E[[ e1]] c) && (E[[ e2]] c)) eqn:He12. 
apply andb_prop in He12. destruct He12 as [He1 He2].
apply In_config_true with (c:=c) in H; try auto.
apply In_config_true with (c:=c) in H0; try auto.
rewrite configVElemSet_push_annot in H, H0. simpl in H, H0.
destruct (E[[ eq]] c) eqn: Heq.

simpl "||-". rewrite <- existsb_In_elem in H, H0. 
rewrite H, H0. reflexivity. eauto. eauto. }
{ simpl "||-". apply IHvcondtype in He.
simpl in He. rewrite He. reflexivity. }
1, 2: simpl "||-"; apply IHvcondtype1 in He as He1;
apply IHvcondtype2 in He as He2;
simpl in He1, He2; rewrite He1, He2; reflexivity.
- simpl "||-". simpl in IHvcondtype1, IHvcondtype2.
destruct (E[[ e']] c) eqn: He'.
rewrite andb_true_r in IHvcondtype1. 
apply IHvcondtype1 in He as He1. eauto.
simpl in *. rewrite andb_true_r in IHvcondtype2.
apply IHvcondtype2 in He as He2. eauto.
Qed.*)

(*Lemma subsump_listELEq: forall (A B A' B': elems), listElEq String.eqb A A' = true ->
              listElEq String.eqb B B' = true -> 
               subsump_qtype_bool A B = subsump_qtype_bool A' B'.
Proof. Admitted.


Lemma is_disjoint_bool_listELEq: forall (A B A' B': elems), listElEq String.eqb A A' = true ->
          listElEq String.eqb B B' = true -> 
             is_disjoint_bool A B = is_disjoint_bool A' B'.
Proof. Admitted.

Lemma elems_union_listELEq: forall (A B A' B': elems), listElEq String.eqb A A' = true ->
             listElEq String.eqb B B' = true -> 
                (elems_union A B) = (elems_union A' B').
             (*listElEq String.eqb (elems_union A B) (elems_union A' B') = true. -- requires transivity*)
Proof. Admitted.


Lemma equiv_qtype_bool_listELEq: forall (A B A' B': elems), listElEq String.eqb A A' = true ->
             listElEq String.eqb B B' = true -> 
             equiv_qtype_bool A B = equiv_qtype_bool A' B'.
Proof. Admitted. *)

(*high level proof explanantion*)
(*Theorem variation_preservation : forall e vq A, 
       vtype e vq A ->
       forall c, (E[[e]] c) = true ->
           (type' (configVQuery vq c)) =a= (configVQtype A c).
Proof.
  intros. induction H.
  (* Relation - E *) (*get rid of this*)
  - unfold configVQuery. unfold configVRelS. simpl. 
    rewrite not_sat_not_prop in H. rewrite <- sat_taut_comp in H. 
    unfold configVQtype. simpl. destruct (E[[e']] c) eqn: HsemE.
    + reflexivity.
    + reflexivity. 
  (* Relation - E *)
  - unfold configVQuery. unfold configVRelS. unfold configVQtype. simpl. 
    rewrite not_sat_not_prop in H. rewrite <- sat_taut_comp in H. 
    rewrite H0. apply H in H0. rewrite H0. reflexivity.
 (* Project - E *)
 - unfold subsump_vqtype, configVQtype in H1. simpl in H1.
   unfold configVQtype in IHvtype. simpl in IHvtype. 
   unfold configVQtype. simpl.  
   destruct (E[[ e']] c) eqn: He'.
     ++ 
        simpl. unfold subsump_qtype_bool. rewrite H0.
        specialize H1 with c. rewrite H0, He' in H1. 
        destruct (sublist_bool (configVElemSet A c) (type' (configVQuery vq c))) eqn:Hsubl.
        reflexivity.
        rewrite H1. rewrite H0. 
        reflexivity. 
        (*assumption.->*) apply ListElEq_refl_elems. 
        apply IHvtype in H0. assumption. (*<-*)
     ++ (*rewrite IHvtype1. ->*)
        rewrite (subsump_listELEq 
                  (configVElemSet A c) (type' (configVQuery vq c))
                  (configVElemSet A c) []).
        (*<-*)
        simpl. unfold subsump_qtype_bool. 
        specialize H1 with c. rewrite H0, He' in H1. 
        destruct (configVElemSet A c). rewrite H0.
        rewrite ListElEq_refl_elems. reflexivity. simpl in H1. discriminate H1.
        (*assumption.->*)apply ListElEq_refl_elems. 
        apply IHvtype in H0. assumption. (*<-*)

 (* Choice - E *)
 - unfold vqtype_union. simpl fst. simpl snd.
   simpl in IHvtype1. simpl in IHvtype2. rewrite H0 in IHvtype1, IHvtype2.
   rewrite configVQType_dist_velems_union.
   repeat (rewrite configVQType_push_annot).
   destruct (E[[ e']] c) eqn: E'.
   + simpl. rewrite E'. apply context_type_rel in H1.
     rewrite not_sat_not_prop in H1. 
     rewrite <- sat_taut_comp_inv in H1.
     specialize H1 with c. 
     simpl in H1. rewrite H0, E' in H1. simpl in H1. 
     rewrite H1.
     simpl. rewrite elems_union_nil_r. 
     simpl. rewrite orb_false_r. rewrite andb_diag.
     apply IHvtype1. reflexivity. reflexivity.
   + apply context_type_rel in H.
     rewrite not_sat_not_prop in H. 
     rewrite <- sat_taut_comp_inv in H.
     specialize H with c. 
     simpl in H. rewrite H0, E' in H. simpl in H. 
     unfold configVQtype at 1. 
     assert(Ihack2: forall e1 e2, (E[[  e1 /\(F) (e1 \/(F) e2)]] c) = (E[[ e1]] c)).
     { simpl. Search andb. intros. apply absorption_andb. }
     rewrite Ihack2. rewrite H. rewrite elems_union_nil_l.  
     unfold configVQuery. rewrite E'. fold configVQuery.
     destruct (configVQtype (A2, e2 /\(F) (e1 \/(F) e2)) c) eqn: D;
     unfold configVQtype in D; simpl in D; rewrite H in D;
     try (simpl in D); try (rewrite andb_diag in D);
     try (unfold configVQtype in IHvtype2); try (simpl in IHvtype2);
     try (rewrite D in IHvtype2);
     try (apply IHvtype2); repeat (reflexivity). reflexivity.
  (* Product - E *)
  - unfold vqtype_union. simpl fst. simpl snd.
    apply IHvtype2 in H0 as H02.
    apply IHvtype1 in H0 as H01.
    rewrite configVQType_dist_velems_union.
    repeat (rewrite configVQType_push_annot). 
    unfold configVQtype. simpl. rewrite absorption_andb. rewrite orb_comm. 
    rewrite absorption_andb. 
    (*rewrite H01. rewrite H02.->*)
     rewrite (elems_union_listELEq 
               (type' (configVQuery vq1 c)) (type' (configVQuery vq2 c)) 
               (configVQtype (A1, e1) c)    (configVQtype (A2, e2) c)).

     rewrite (is_disjoint_bool_listELEq 
               (type' (configVQuery vq1 c)) (type' (configVQuery vq2 c)) 
               (configVQtype (A1, e1) c)    (configVQtype (A2, e2) c)).
    (*<-*)
    destruct (is_disjoint_bool (configVQtype (A1, e1) c)
    (configVQtype (A2, e2) c)) eqn: Helems.
    + simpl. destruct (E[[ e1]] c) eqn: E1; rewrite ListElEq_refl_elems; reflexivity.
    + unfold is_disjoint_bool in Helems.
      simpl in H2. 
      rewrite <- configVQType_dist_velems_inter in Helems.
      unfold vqtype_inter in H2. simpl fst in H2. simpl snd in H2.
      rewrite H2 in Helems. simpl in Helems. 
      destruct ((E[[ e1]] c) || (E[[ e2]] c)). discriminate Helems.
      discriminate Helems.
    + assumption. + assumption. + assumption. + assumption.
 (* Select - E *)
 (* SetOp - E *)
 - simpl in IHvtype1. simpl in IHvtype2. simpl. 
   + simpl. (*rewrite IHvtype1. rewrite IHvtype2.->*)
     rewrite (equiv_qtype_bool_listELEq 
               (type' (configVQuery vq1 c)) (type' (configVQuery vq2 c)) 
               (if E[[ e1]] c then configVElemSet A1 c else [])    
               (if E[[ e2]] c then configVElemSet A2 c else [])).
     (*<-*)
     unfold configVQtype. simpl. 
     destruct H2. simpl in H2. simpl in H3. unfold equiv_velems in H2.
     unfold equivE in H3. rewrite <- H2. rewrite <- H3. destruct (E[[ e1]] c) eqn: E'.
     ++ rewrite (equiv_qtype_bool_refl (configVElemSet A1 c)). apply IHvtype1. apply H0.
     ++ simpl. apply IHvtype1. apply H0.
     ++ apply IHvtype1 in H0. assumption. ++ apply IHvtype2 in H0. assumption.
 
Qed.*)



