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
unfold equiv_atts in H. 
apply forall_dist_and in H. destruct H.
simpl count_occ in H0 at 1. symmetry in H0.
rewrite count_occ_inv_nil in H0. 
symmetry in H0.
apply nil_cons in H0. destruct H0.
- intros.  simpl. 
destruct (set_mem string_eq_dec a A') eqn: Hsetmem.
apply IHA. rewrite equiv_qtype_set_remove_cons. assumption.
apply (set_mem_correct1 string_eq_dec). assumption.
unfold equiv_qtype in H; unfold equiv_atts in H.
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



(** ------------equiv_bool correct ------------------------*)




(* -----------------------------------------------------
  | Relation-E inverse
  | e |- vq : A'^e' ->
  |   ~sat (e' /\ (~e)) (= e' -> e)
  | Type annotation e' is more specific than context e.
   -----------------------------------------------------
*)
Theorem context_type_rel : forall e S vq A' e',
       vtype e S vq (A', e') -> 
           ~ sat (  e' /\(F) (~(F) (e)) ).
Proof. intros e S vq. generalize dependent e. induction vq. (* subst. *)
       - intros. inversion H; subst. assumption. rewrite not_sat_not_prop. 
          rewrite <- sat_taut_comp.
          intros. assumption.
       - intros. inversion H; subst.
       - intros. inversion H; subst.
         rewrite not_sat_not_prop. rewrite <- sat_taut_comp.
         intros. assumption.
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

Theorem variation_preservation : forall e S vq A, 
       vtype e S vq A ->
       forall c, (E[[e]] c) = true ->
           (type_ (configVQuery vq c)) =a= (configVQtype A c).
Proof.
  intros. induction H.
  (* Relation - E *) (*get rid of this*)
  - unfold configVQuery. unfold configVRelS. simpl. 
    rewrite not_sat_not_prop in H1. rewrite <- sat_taut_comp in H1. 
    unfold configVQtype. simpl. destruct (E[[e']] c) eqn: HsemE.
    + reflexivity.
    + reflexivity. 
  (* Relation - E *)
  (* S |= r : A^e -> type' (Q[[ r(A)^e]]c) =a= Qt[[ A^e]]c  
    |             -> type' (R[[ r(A)^e]]c) =a= if E[[ e]]c = true then A[[ A]]c else []
    |             -> type' (r (if E[[ e]]c = true then A[[ A]]c else []))
    |                             =a= if E[[ e]]c = true then A[[ A]]c else []
    | destruct E[[ e]]c 
    | True =>     -> type' (r(A[[ A]]c) = A[[A]]c 
  *)
  - unfold configVQuery. unfold configVRelS. unfold configVQtype. simpl. 
    rewrite not_sat_not_prop in H1. rewrite <- sat_taut_comp in H1. 
    rewrite H0. apply H1 in H0. rewrite H0. reflexivity.
 (* Project - E *)
 - unfold subsump_vqtype, configVQtype in H1. simpl in H1.
   unfold configVQtype in IHvtype. simpl in IHvtype. 
   unfold configVQtype. simpl.  
   destruct (E[[ e']] c) eqn: He'.
     ++ simpl. unfold subsump_qtype_bool. rewrite H0.
        specialize H1 with c. rewrite H0, He' in H1. 
        destruct (sublist_bool (configVAttSet A c) (type' (configVQuery vq c))) eqn:Hsubl.
        reflexivity. 
        apply IHvtype in H0. apply not_true_iff_false in Hsubl.
        rewrite <- (contrapositive_iff _ _ (sublist_bool_correct _ _)) 
        in Hsubl.
        rewrite equiv_sublist with (B':=configVAttSet A' c) in Hsubl.
        contradiction. auto. 
     ++ (*rewrite IHvtype1. ->*)
        simpl. unfold subsump_qtype_bool. 
        specialize H1 with c. rewrite H0, He' in H1. 
        destruct (configVAttSet A c). rewrite H0. simpl. reflexivity.
        rewrite <- sublist_bool_correct in H1. simpl in H1.
        discriminate H1.
 (* Choice - E *)
 - unfold vqtype_union. simpl fst. simpl snd.
   simpl in IHvtype1. simpl in IHvtype2. rewrite H0 in IHvtype1, IHvtype2.
   rewrite configVQType_dist_vatts_union.
   repeat (rewrite configVQType_push_annot).
   all: try(apply (NoDupAtt_push_annot); eauto). 
   destruct (E[[ e']] c) eqn: E'.
   + simpl. rewrite E'. apply context_type_rel in H1.
     rewrite not_sat_not_prop in H1. 
     rewrite <- sat_taut_comp_inv in H1.
     specialize H1 with c. 
     simpl in H1. rewrite H0, E' in H1. simpl in H1. 
     rewrite H1.
     simpl. 
     simpl. rewrite orb_false_r. rewrite andb_diag.
     apply IHvtype1. reflexivity. reflexivity.
   + apply context_type_rel in H.
     rewrite not_sat_not_prop in H. 
     rewrite <- sat_taut_comp_inv in H.
     specialize H with c. 
     simpl in H. rewrite H0, E' in H. simpl in H. 
     unfold configVQtype at 1. 
     assert(Ihack2: forall e1 e2, (E[[  e1 /\(F) (e1 \/(F) e2)]] c) = (E[[ e1]] c)).
     { simpl. intros. apply absorption_andb. }
     rewrite Ihack2. rewrite H. rewrite atts_union_nil_l.  
     unfold configVQuery. rewrite E'. fold configVQuery. 
     destruct (configVQtype (A2, e2 /\(F) (e1 \/(F) e2)) c) eqn: D;
     unfold configVQtype in D; try (unfold configVQtype);
     simpl in D; rewrite H in D; try (simpl); try (rewrite H);
     try (simpl in D); try (simpl); try (rewrite andb_diag in D);try (rewrite andb_diag);
     try (unfold configVQtype in IHvtype2); try (simpl in  IHvtype2).
     try (rewrite D in IHvtype2); try (rewrite D);
     try (apply IHvtype2); try (reflexivity). all: try (reflexivity); eauto.
     apply NoDupAtt_NoDup_configVQ. eauto.
  (* Product - E *)
  - unfold vqtype_union. simpl fst. simpl snd.
    apply IHvtype2 in H0 as H02.
    apply IHvtype1 in H0 as H01.
    rewrite configVQType_dist_vatts_union.
    repeat (rewrite configVQType_push_annot). Check absorption_andb.
    unfold configVQtype. simpl. rewrite absorption_andb. rewrite orb_comm. 
    rewrite absorption_andb. 
    pose (NoDupAtt_NoDup_configVQ (A1, e1) c) as HA1VQ.
    simpl fst in HA1VQ. pose (NoDupAtt_NoDup_configVQ (A2, e2) c) as HA2VQ.
    simpl fst in HA2VQ.
   (*rewrite H01. rewrite H02.->*)
    rewrite (is_disjoint_bool_equiv) with 
    (B := (configVQtype (A1, e1) c)) 
    (B':= (configVQtype (A2, e2) c)).
    all: eauto; try(apply (NoDup_equiv_atts H01); eauto); 
                try(apply (NoDup_equiv_atts H02); eauto);
                try(apply (NoDupAtt_push_annot); eauto). 
    destruct (is_disjoint_bool (configVQtype (A1, e1) c)
    (configVQtype (A2, e2) c)) eqn: Hatts.
    + rewrite (set_union_equiv) with 
    (B := (configVQtype (A1, e1) c)) 
    (B':= (configVQtype (A2, e2) c)).
      simpl. reflexivity. 
      all: eauto; try(apply (NoDup_equiv_atts H01); eauto); 
           try(apply (NoDup_equiv_atts H02); eauto). 
    + unfold is_disjoint_bool in Hatts.
      (*rewrite (set_inter_equiv H01 H02) in Hatts.*)
      simpl in H2. 
      rewrite <- configVQType_dist_vatts_inter in Hatts.
      unfold vqtype_inter in H2. simpl fst in H2. simpl snd in H2.
      rewrite H2 in Hatts. simpl in Hatts. 
      destruct ((E[[ e1]] c) || (E[[ e2]] c)). discriminate Hatts.
      discriminate Hatts.
      all:assumption.
 (* Select - E *)
 (* SetOp - E *)
 - simpl in IHvtype1. simpl in IHvtype2. simpl. 
   + simpl. (*rewrite IHvtype1. rewrite IHvtype2.->*) 
     pose (NoDupAtt_NoDup_configVQ (A1, e1) c HA1) as HA1VQ. 
     pose (NoDupAtt_NoDup_configVQ (A2, e2) c HA2) as HA2VQ. 
     apply IHvtype1 in H0 as IHvtype1'. clear IHvtype1.
     apply IHvtype2 in H0 as IHvtype2'. clear IHvtype2.
     rewrite (equiv_qtype_bool_equiv) with 
     (B := (configVQtype (A1, e1) c)) 
     (B':= (configVQtype (A2, e2) c)).
     all: eauto;
     try (apply (NoDup_equiv_atts IHvtype1'); destruct (E[[ e1]] c); 
         [apply (NoDupAtt_NoDup_config c HA1) | apply NoDup_nil]);
     try (apply (NoDup_equiv_atts IHvtype2'); destruct (E[[ e2]] c); 
         [apply (NoDupAtt_NoDup_config c HA2) | apply NoDup_nil]).
     (*<-*)
     unfold configVQtype. simpl. 
     destruct H2. simpl in H2. simpl in H3. unfold equiv_vatts in H2.
     unfold equivE in H3. (*rewrite <- H2.*) rewrite <- H3. 
    
     destruct (E[[ e1]] c) eqn: E'.
     ++ rewrite (equiv_qtype_bool_equiv) with 
        (B := (configVAttSet A1 c)) 
        (B':= (configVAttSet A1 c)).
        rewrite (equiv_qtype_bool_refl (configVAttSet A1 c)). apply IHvtype1'. 
        all: try (apply (NoDupAtt_NoDup_config c HA1));
             try (apply (NoDupAtt_NoDup_config c HA2));
             try (symmetry; apply (H2 c)); try(reflexivity).
     ++ simpl. apply IHvtype1'. 
Qed.


End VRA_varPrsrvtn_thm.

(*Lemma subsump_listELEq: forall (A B A' B': atts), listElEq String.eqb A A' = true ->
              listElEq String.eqb B B' = true -> 
               subsump_qtype_bool A B = subsump_qtype_bool A' B'.
Proof. Admitted.


Lemma is_disjoint_bool_listELEq: forall (A B A' B': atts), listElEq String.eqb A A' = true ->
          listElEq String.eqb B B' = true -> 
             is_disjoint_bool A B = is_disjoint_bool A' B'.
Proof. Admitted.

Lemma atts_union_listELEq: forall (A B A' B': atts), listElEq String.eqb A A' = true ->
             listElEq String.eqb B B' = true -> 
                (atts_union A B) = (atts_union A' B').
             (*listElEq String.eqb (atts_union A B) (atts_union A' B') = true. -- requires transivity*)
Proof. Admitted.


Lemma equiv_qtype_bool_listELEq: forall (A B A' B': atts), listElEq String.eqb A A' = true ->
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
        destruct (sublist_bool (configVAttSet A c) (type' (configVQuery vq c))) eqn:Hsubl.
        reflexivity.
        rewrite H1. rewrite H0. 
        reflexivity. 
        (*assumption.->*) apply ListElEq_refl_atts. 
        apply IHvtype in H0. assumption. (*<-*)
     ++ (*rewrite IHvtype1. ->*)
        rewrite (subsump_listELEq 
                  (configVAttSet A c) (type' (configVQuery vq c))
                  (configVAttSet A c) []).
        (*<-*)
        simpl. unfold subsump_qtype_bool. 
        specialize H1 with c. rewrite H0, He' in H1. 
        destruct (configVAttSet A c). rewrite H0.
        rewrite ListElEq_refl_atts. reflexivity. simpl in H1. discriminate H1.
        (*assumption.->*)apply ListElEq_refl_atts. 
        apply IHvtype in H0. assumption. (*<-*)

 (* Choice - E *)
 - unfold vqtype_union. simpl fst. simpl snd.
   simpl in IHvtype1. simpl in IHvtype2. rewrite H0 in IHvtype1, IHvtype2.
   rewrite configVQType_dist_vatts_union.
   repeat (rewrite configVQType_push_annot).
   destruct (E[[ e']] c) eqn: E'.
   + simpl. rewrite E'. apply context_type_rel in H1.
     rewrite not_sat_not_prop in H1. 
     rewrite <- sat_taut_comp_inv in H1.
     specialize H1 with c. 
     simpl in H1. rewrite H0, E' in H1. simpl in H1. 
     rewrite H1.
     simpl. rewrite atts_union_nil_r. 
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
     rewrite Ihack2. rewrite H. rewrite atts_union_nil_l.  
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
    rewrite configVQType_dist_vatts_union.
    repeat (rewrite configVQType_push_annot). 
    unfold configVQtype. simpl. rewrite absorption_andb. rewrite orb_comm. 
    rewrite absorption_andb. 
    (*rewrite H01. rewrite H02.->*)
     rewrite (atts_union_listELEq 
               (type' (configVQuery vq1 c)) (type' (configVQuery vq2 c)) 
               (configVQtype (A1, e1) c)    (configVQtype (A2, e2) c)).

     rewrite (is_disjoint_bool_listELEq 
               (type' (configVQuery vq1 c)) (type' (configVQuery vq2 c)) 
               (configVQtype (A1, e1) c)    (configVQtype (A2, e2) c)).
    (*<-*)
    destruct (is_disjoint_bool (configVQtype (A1, e1) c)
    (configVQtype (A2, e2) c)) eqn: Hatts.
    + simpl. destruct (E[[ e1]] c) eqn: E1; rewrite ListElEq_refl_atts; reflexivity.
    + unfold is_disjoint_bool in Hatts.
      simpl in H2. 
      rewrite <- configVQType_dist_vatts_inter in Hatts.
      unfold vqtype_inter in H2. simpl fst in H2. simpl snd in H2.
      rewrite H2 in Hatts. simpl in Hatts. 
      destruct ((E[[ e1]] c) || (E[[ e2]] c)). discriminate Hatts.
      discriminate Hatts.
    + assumption. + assumption. + assumption. + assumption.
 (* Select - E *)
 (* SetOp - E *)
 - simpl in IHvtype1. simpl in IHvtype2. simpl. 
   + simpl. (*rewrite IHvtype1. rewrite IHvtype2.->*)
     rewrite (equiv_qtype_bool_listELEq 
               (type' (configVQuery vq1 c)) (type' (configVQuery vq2 c)) 
               (if E[[ e1]] c then configVAttSet A1 c else [])    
               (if E[[ e2]] c then configVAttSet A2 c else [])).
     (*<-*)
     unfold configVQtype. simpl. 
     destruct H2. simpl in H2. simpl in H3. unfold equiv_vatts in H2.
     unfold equivE in H3. rewrite <- H2. rewrite <- H3. destruct (E[[ e1]] c) eqn: E'.
     ++ rewrite (equiv_qtype_bool_refl (configVAttSet A1 c)). apply IHvtype1. apply H0.
     ++ simpl. apply IHvtype1. apply H0.
     ++ apply IHvtype1 in H0. assumption. ++ apply IHvtype2 in H0. assumption.
 
Qed.*)



