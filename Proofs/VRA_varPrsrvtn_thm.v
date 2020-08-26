(** Variational relational algebra lemmas *)
Set Warnings "-notation-overridden,-parsing".
Import Init.Datatypes.
Import Coq.Init.Nat.
Require Import Maps.
Require Export List.
Require Export Logic.
Import Coq.Lists.List.ListNotations.


Load VRA_encoding_lemmas.
Import VRA_encoding_lemmas.

Module VRA_varPrsrvtn_thm.

(** ------------------------------------------------------------
  Relating equiv_vatts to atts
---------------------------------------------------------------*)

Lemma equiv_vatts_to_atts: forall A A', A =va= A' ->
     forall c, ((configVAttSet A  c) =a= (configVAttSet A' c)).
Proof. Admitted.


(*---------------------------------------------------------------*)

(** ------------------------------------------------------------
  equiv_bool correct
---------------------------------------------------------------*)

Lemma equiv_qtype_bool_correct: forall A A' {Ha: NoDup A} {Ha': NoDup A'}, equiv_qtype_bool A A' = true
                        <-> equiv_qtype A A'.
Proof.  Admitted.

(** ------------equiv_bool correct ------------------------*)


Lemma equiv_sublist: forall A B B' {HB: NoDup B} {HB': NoDup B'}, 
     B =a= B' -> sublist_bool A B = sublist_bool A B'.
Proof. intros. Admitted.

(* 
   <- doesn't apply: NoDup A (= {(a, e1), (a, e2)}) can result in
   Dup configVAttSet A c = ({a a}) for c, e1 c = true && e2 c = true
*)
Lemma NoDup_configVAttSet: forall A, (forall c, NoDup (configVAttSet A c)) ->
      NoDup A.
Proof. Admitted.

Lemma configVAttSet_dist_vatts_union : forall A  A' c, configVAttSet (vatts_union A A') c =
      atts_union (configVAttSet A c) (configVAttSet A' c) .
Proof. Admitted.
  (*intros A A' c. generalize dependent A'.
  induction A as [|(a, e) As IHAs].
  - (* A = nil *)
    intro A'. simpl. reflexivity.
  - (* A = (a, e) :: As *)
    intro A'.
    (*unfold vatts_union. 
    rewrite ?union_dist_app. 
    unfold atts_union. 
    unfold vatts_union_c; fold vatts_union_c.*)
    destruct (findIfExists a A') as [e' | ] eqn: I.
    
    + (* findIfExists a A' = Some e' *)
      unfold vatts_union; fold vatts_union.
      rewrite I.
      destruct (E[[ e]] c) eqn:E;
      unfold configVAttSet; fold configVAttSet.
      ++ (* E[[ e]] c) = true *)
         unfold atts_union; fold atts_union.
         destruct (E[[ e']] c) eqn:E'.
         +++ (* E[[ e']] c) = true *)
             simpl semE. rewrite E, E'. simpl.
             rewrite two with (e:=e').
             rewrite four with (e:=e'). 
             rewrite IHAs. reflexivity.
             assumption. assumption. assumption. 
         +++ simpl semE. rewrite E, E'. simpl.
             rewrite one with (e:=e').
             rewrite (five a A' e' c).
             rewrite IHAs. reflexivity.
             assumption. assumption. assumption.
             assumption. 
      ++ unfold atts_union; fold atts_union.
         destruct (E[[ e']] c) eqn:E'.
         +++ (* E[[ e']] c) = true *)
             simpl semE. rewrite E, E'. simpl.
             rewrite (six a A' e' c).
             rewrite IHAs. (* unfold atts_union; fold atts_union. reflexivity.
             assumption. assumption. assumption.
             assumption. *) *)

(*intros A A' c. generalize dependent A'.
  induction A as [|(a, e) As IHAs].
  - (* A = nil *)
    intro A'. simpl. rewrite vatts_union_nil_l.
    rewrite atts_union_nil_l. reflexivity.
  - (* A = (a, e) :: As *)
    intro A'.
    unfold vatts_union. 
    rewrite ?union_dist_app. 
    unfold atts_union. 
    unfold vatts_union_c; fold vatts_union_c.
    destruct (findIfExists a A') as [e' | ] eqn: I;
    unfold configVAttSet; fold configVAttSet.
    + (* findIfExists a A' = Some e' *)
      destruct (E[[ e]] c) eqn:E.
      ++ (* E[[ e]] c) = true *)
         destruct (E[[ e']] c) eqn:E'.
         +++ (* E[[ e']] c) = true *)
         simpl semE. rewrite E, E'. simpl. 
         rewrite I. 
         rewrite two with (e:=e').
         rewrite three. rewrite four with (e:=e').
         rewrite five. rewrite <- ?app_comm_cons. simpl.
         unfold vatts_union in IHAs. 
         rewrite <- ?union_dist_app.
         unfold atts_union in IHAs. 
         +++ (* E[[ e']] c) = false *)
      ++ (* E[[ e]] c) = false *)
         +++ (* E[[ e']] c) = true *)
         +++ (* E[[ e']] c) = false *)
    + (* findIfExists a A' = None *)
      destruct (E[[ e]] c) eqn:E.
      ++ (* E[[ e]] c) = true *)
         destruct (E[[ e']] c) eqn:E'.
         +++ (* E[[ e']] c) = true *)
         
         +++ (* E[[ e']] c) = false *)

      ++ (* E[[ e]] c) = false *)

         +++ (* E[[ e']] c) = true *)
         +++ (* E[[ e']] c) = false *)
Admitted.*)

Lemma configVQType_dist_vatts_union : forall A A' e c, configVQtype (vatts_union A A', e) c
= atts_union (configVQtype (A, e) c) (configVQtype (A', e) c).
Proof. 

Admitted.

Lemma configVQType_dist_vatts_inter : forall A A' e e' c, 
configVQtype (vatts_inter (push_annot A e)
       (push_annot A' e'), e \/(F) e') c
= atts_inter (configVQtype (A, e) c) (configVQtype (A', e') c).
Proof. 
Admitted.


(* -----------------------------------------------------
  | Relation-E inverse
  | e |- vq : A'^e' ->
  |   ~sat (e' /\ (~e)) (= e' -> e)
  | Type annotation e' is more specific than context e.
   -----------------------------------------------------
*)
Theorem context_type_rel : forall e vq A' e',
       vtype e vq (A', e') -> 
           ~ sat (  e' /\(F) (~(F) (e)) ).
Proof. intros e vq. generalize dependent e. induction vq. (* subst. *)
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
         apply IHvq1 in H3.  rewrite not_sat_not_prop in H3. 
         rewrite <- sat_taut_comp in H3. specialize H3 with c.
         apply H3 in E1. simpl in E1. apply andb_prop in E1. 
         destruct E1. rewrite <- H1, H0. reflexivity.
         + rewrite <- sat_taut_comp_inv_c. intros. simpl.
         rewrite E1. simpl.
         apply IHvq2 in H7.  rewrite not_sat_not_prop in H7. 
         rewrite <- sat_taut_comp_inv in H7. specialize H7 with c.
         apply H7. simpl. rewrite H0. simpl. reflexivity.
       - intros. inversion H; subst.
       - intros. inversion H; subst.
         apply IHvq1 in H5. apply IHvq2 in H6. 
         rewrite not_sat_not_prop. rewrite <- sat_taut_comp.
         intros. simpl in H0.
         destruct (E[[ e1]] c) eqn:E1. 
         + rewrite not_sat_not_prop in H5. rewrite <- sat_taut_comp in H5.
         specialize H5 with c. auto. 
         + rewrite not_sat_not_prop in H6. 
         rewrite <- sat_taut_comp in H6.
         specialize H6 with c. auto.
       - intros. inversion H; subst. apply IHvq1 in H5. assumption.
Qed.
 


(* -----------------------------------------------------------
  | Variation Preservation : 
  |  e |- vq : A  ->
  |    forall c, Q[[vq]]c :: T[[A]]c 
  | where :  = vtype (type derivation of variational query) 
  |       :: = type' (type derivation of plain query)
  |       Q  = configVQuery (configuration of variational query)
  |       T  = configVQtype (configuration of variational type)
   ------------------------------------------------------------
*)

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
Theorem variation_preservation : forall e vq A, 
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
 
Qed.

End VRA_varPrsrvtn_thm.

