(** Variational relational algebra lemmas *)
Set Warnings "-notation-overridden,-parsing".
Import Init.Datatypes.
Import Coq.Init.Nat.
Require Import Maps.
Require Export List.
Require Export Logic.

Load VRA_RA_encoding.
Import VRA_RA_encoding.

Module VRA_varPrsrvtn_thm.

(** ------------------------------------------------------------
  Sorted Attribute Set implication lemmas
---------------------------------------------------------------*)
(* Less than first implies less than all  *)
Lemma fst_elm_lt_all_elm: forall (vt: vatt) (vs:vatts) (x : att), 
        (exists e, In (x, e) (tl (vt :: vs))) -> 
                     string_comp (fst vt) x = LTc.
Proof. 
       intros. generalize dependent x. 
       generalize dependent vt.
       induction vs as [| (v', ev') vs' IHvs]; destruct vt as (v, ev).
          + intros. simpl in H. destruct H as [e H]. contradiction.
          + intros x. 
            specialize IHvs with (vt:=(v', ev')) (x:=x). 
            (*destruct IHvs as [ex IHvs].*) simpl in IHvs. 
           assert ( I1: (LocallySortedVAtts ((v, ev) :: (v', ev') :: vs'))  /\ 
                               (NoDup ((v, ev) :: (v', ev') :: vs')) ). 
                  { apply assumption_vatts. }
           destruct I1 as [ I11 I12]. simpl. 
           (*exists ex.*)
           intros. destruct H as [ex H]. destruct H as [ H1| H2].
           ++ inversion H1; subst.  inversion I11; subst.  simpl in H4.
              assumption.
           ++ (*apply IHvs in H2.*) inversion I11; subst. simpl in H4.
              apply (string_comp_lt_trans v'). split.
              right. assumption. apply IHvs. exists ex. assumption.
Qed.

(* Less than n-th imples lesss than (n-end) [see A1] *)
Lemma lless_implies_gless :
   forall (a: vatt) (vs:vatts), (string_comp (fst a) (fst (hd a vs)) = EQc 
                              \/ string_comp (fst a) (fst (hd a vs)) = LTc ->
     (forall (x:att), (exists e, In (x, e) (tail vs)) -> 
       string_comp (fst a) x = LTc)).
Proof. intros. generalize dependent x. 
       destruct vs as [| (v', ev') vs']. 
       + intros.  destruct a as (a', e').
         simpl in H0. destruct H0 as [e0 H0]. contradiction.
       + intro x. simpl in H. 
         assert (I:  
        (exists e, In (x, e) (tl ((v', ev') :: vs'))) -> 
                     string_comp (fst (v', ev')) x = LTc ).
        { apply ( fst_elm_lt_all_elm (v', ev') vs' x). }
        simpl in I. intros. apply (string_comp_lt_trans v'). 
        split. assumption. apply I. destruct H0 as [ex H0].
        simpl in H0. exists ex. assumption.
Qed.


(*-------------------------------sortedlemmas-------------------------------------*)


Lemma config_filters_subset: forall vs c x xs, configVAttSet vs c = x :: xs 
 -> exists e, In (x, e) vs.
Proof. intros. induction vs as [| v vs]. 
       - simpl in H.  discriminate H. 
       - destruct v. simpl in H. destruct (E[[ f]] c) eqn: F.
         + inversion H. exists f. simpl. left. reflexivity.
         + simpl. apply IHvs in H. destruct H as [e H].
           exists e. right. assumption.
Qed. 

Lemma case1_req_global_lt_prop: forall (v v': vatt) (xs xs': vatts),
 (string_comp (fst v) (fst v')) = EQc \/ (string_comp (fst v) (fst v')) = LTc -> 
  (forall c, (E[[(snd v)]] c) = true  /\ (E[[(snd v')]] c) = false ->
   atts_union (configVAttSet (v :: xs) c) (configVAttSet (v' :: xs') c) 
     = (fst v) :: atts_union (configVAttSet xs c) (configVAttSet xs' c) ).
Proof. 
      intros v v' xs xs' H0 c H1.
      destruct v as (a, e). destruct v' as (a',e'). 
      simpl in H0. simpl in H1. simpl. 
      destruct H1 as [H1 H2]. 
      rewrite H1. rewrite H2. destruct (configVAttSet xs' c) eqn: Imp. 
        + simpl. rewrite atts_union_nil_r. reflexivity.
        + pose proof lless_implies_gless as H.
          specialize H with (vs:=((a',e')::xs')).
          simpl in H.
          specialize H with (a:=(a,e)). 
          simpl in H. 
          simpl. specialize H with a0. 
          simpl in H. rewrite H.
          reflexivity. assumption. 
          apply config_filters_subset in Imp. assumption.   
Qed.

Lemma case2_req_global_lt_prop: forall (v v': vatt) (xs xs': vatts),
 (string_comp (fst v) (fst v')) = EQc \/ (string_comp (fst v) (fst v')) = GTc -> 
  (forall c, (E[[(snd v)]] c) = false /\ (E[[(snd v')]] c) = true  ->
   atts_union (configVAttSet (v :: xs) c) (configVAttSet (v' :: xs') c) 
     = (fst v') :: atts_union (configVAttSet xs c) (configVAttSet xs' c) ).
Proof. 
      intros. rewrite atts_union_comm. 
      rewrite (atts_union_comm (configVAttSet xs c) (configVAttSet xs' c)). 
      apply case1_req_global_lt_prop.
      - destruct H. 
      + left. apply string_comp_eqc_symm. assumption. 
      + right. rewrite string_comp_lt_gt. assumption.
      - rewrite and_comm. assumption.
Qed.

Lemma case1_req_global_lt_prop_inter: forall (v v': vatt) (xs xs': vatts),
 (string_comp (fst v) (fst v')) = EQc  \/ (string_comp (fst v) (fst v')) = LTc -> 
  (forall c, (E[[(snd v)]] c) = true  /\ (E[[(snd v')]] c) = false ->
   atts_inter (configVAttSet (v :: xs) c) (configVAttSet (v' :: xs') c) 
     = atts_inter (configVAttSet xs c) (configVAttSet xs' c) ).
Proof. 
      (*intros v v' xs xs' H0 c H1.
      destruct v as (a, e). destruct v' as (a',e'). 
      simpl in H0. simpl in H1. simpl. 
      destruct H1 as [H1 H2]. 
      rewrite H1. rewrite H2. destruct (configVAttSet xs' c) eqn: Imp. 
        + simpl. rewrite atts_union_nil_r. reflexivity.
        + assert (H: globally_less). { unfold globally_less.
          apply lless_implies_gless. }
          unfold globally_less in H. specialize H with (vs:=((a',e')::xs')). 
          simpl in H.
          specialize H with (a:=(a,e)). 
          simpl in H. 
          simpl. specialize H with a0. 
          simpl in H. rewrite H.
          reflexivity. assumption. 
          apply config_filters_subset in Imp. assumption.   
Qed.*)
Admitted.

Lemma case2_req_global_lt_prop_inter: forall (v v': vatt) (xs xs': vatts),
 (string_comp (fst v) (fst v')) = EQc \/ (string_comp (fst v) (fst v')) = GTc -> 
  (forall c, (E[[(snd v)]] c) = false /\ (E[[(snd v')]] c) = true  ->
   atts_inter (configVAttSet (v :: xs) c) (configVAttSet (v' :: xs') c) 
     = atts_inter (configVAttSet xs c) (configVAttSet xs' c) ).
Proof. Admitted.

Lemma configVAttSet_dist_vatts_union : forall A  A' c, configVAttSet (vatts_union A A') c =
      atts_union (configVAttSet A c) (configVAttSet A' c) .
Proof. 
   intros A A' c. generalize dependent A'. induction A as [ | (a1, e1) ].
   - intro A'. rewrite vatts_union_nil_l. simpl. destruct (configVAttSet A' c).
     reflexivity. reflexivity.
   - intros. induction A' as [| (a2, e2)]. 
     + rewrite vatts_union_nil_r. rewrite atts_union_nil_r. 
       reflexivity. 
     + assert (I: forall a e A, configVAttSet ( (a, e) :: A ) c = 
       if semE e c then a :: (configVAttSet A c) else configVAttSet A c ).
       { intros. simpl. reflexivity. } (* rewrite I. rewrite I. *)
       destruct (E[[ e1]] c) eqn: E1. 
       ++ destruct (E[[ e2]] c) eqn: E2. 
          { rewrite I. rewrite I. rewrite E1. rewrite E2.
            destruct (string_comp a1 a2) eqn:SC.
            + simpl. rewrite SC. rewrite I. simpl. rewrite E1. simpl. 
              rewrite IHA. reflexivity.
            + simpl. rewrite SC. rewrite I. rewrite E1. 
              rewrite IHA. rewrite I. rewrite E2. reflexivity.
            + rewrite ackerman_resolve_vatts_union. 
                   rewrite ackerman_resolve_atts_union.
                   rewrite I. rewrite E2. rewrite IHA'.
                   rewrite I. rewrite E1. reflexivity.
                   assumption. simpl. assumption.
          }
          { destruct (string_comp a1 a2) eqn:SC.
            + rewrite case1_req_global_lt_prop. unfold vatts_union; fold vatts_union. 
              rewrite SC.  rewrite I. rewrite or_any_true. rewrite IHA.
              simpl. reflexivity.
              rewrite E1. reflexivity.
              simpl. left. assumption.
              simpl. split. assumption. assumption.
            + rewrite case1_req_global_lt_prop. simpl. rewrite SC. rewrite I. rewrite E1.
                rewrite IHA. rewrite I. rewrite E2. reflexivity.
                simpl. right. assumption.
                simpl. split. assumption. assumption.
            + rewrite ackerman_resolve_vatts_union. 
              rewrite I. rewrite E2. rewrite IHA'.
              rewrite I. rewrite E1.  rewrite I. rewrite E2. reflexivity.
              simpl. assumption.
          }
     ++ destruct (E[[ e2]] c) eqn: E2. 
          { destruct (string_comp a1 a2) eqn:SC.
            + rewrite case2_req_global_lt_prop. unfold vatts_union; fold vatts_union. 
              rewrite SC.  rewrite I. rewrite or_any_true. rewrite IHA.
              simpl. apply string_compEq_eq in SC. rewrite SC. reflexivity.
              rewrite E2. rewrite orb_comm. reflexivity.
              simpl. left. assumption.
              simpl. split. assumption. assumption.
            + simpl. rewrite SC. 
              rewrite E1. rewrite E2. rewrite I. rewrite E1. rewrite IHA. 
              rewrite I. rewrite E2. reflexivity.
            + rewrite case2_req_global_lt_prop. 
              rewrite ackerman_resolve_vatts_union. 
              rewrite I. rewrite E2.
              rewrite IHA'. rewrite I. rewrite E1. reflexivity.
              simpl. assumption.
              simpl. right. assumption. 
              simpl. split. assumption. assumption.
          }
          { rewrite I. rewrite I. rewrite E1. rewrite E2.
            destruct (string_comp a1 a2) eqn:SC.
            + simpl. rewrite SC. rewrite I. simpl. rewrite E1. rewrite E2. 
              simpl. apply IHA.
            + simpl. rewrite SC. rewrite I. rewrite E1. rewrite IHA. 
              rewrite I. rewrite E2. reflexivity.
            + rewrite ackerman_resolve_vatts_union. 
              rewrite I. rewrite E2. rewrite IHA'.
              rewrite I. rewrite E1. reflexivity.
             simpl. assumption.
          }
Qed.

Lemma configVQType_dist_vatts_union : forall A A' e c, configVQtype (vatts_union A A', e) c
= atts_union (configVQtype (A, e) c) (configVQtype (A', e) c).
Proof. 
 intros A A' e c. generalize dependent A'. induction A as [ | (a1, e1) ]. 
 - intro A'. destruct A' as [| (a2, e2)]. simpl. 
   + unfold configVQtype. simpl. destruct (E[[ e]] c) eqn: E.
     ++ reflexivity.
     ++ reflexivity. 
   + unfold configVQtype. simpl. destruct (E[[ e]] c) eqn: E.
     ++ rewrite atts_union_nil_l. reflexivity.
     ++ reflexivity. 
 - intro A'. destruct A' as [| (a2, e2)]. 
   + rewrite vatts_union_nil_r. 
     unfold configVQtype. simpl. destruct (E[[ e]] c) eqn: E. 
     rewrite atts_union_nil_r. reflexivity. reflexivity.
   + unfold configVQtype. unfold configVQtype in IHA. 
     destruct (E[[ e]] c) eqn: E. 
     ++ apply configVAttSet_dist_vatts_union. 
     ++ reflexivity.
Qed.


Lemma configVQType_dist_vatts_inter : forall A A' e e' c, 
configVQtype (vatts_inter (push_annot A e)
       (push_annot A' e'), e \/(F) e') c
= atts_inter (configVQtype (A, e) c) (configVQtype (A', e') c).
Proof. intros A A' e e' c. generalize dependent A'. induction A as [ | (a1, e1) ]. 
 - intro A'. destruct A' as [| (a2, e2)]. simpl. 
   + unfold configVQtype. simpl. destruct (E[[ e]] c) eqn: E;
       destruct (E[[ e']] c) eqn: E'; reflexivity. 
   + unfold configVQtype. simpl. destruct (E[[ e]] c) eqn: E;
      destruct (E[[ e']] c) eqn: E'; try (rewrite atts_inter_nil_l); reflexivity.
 - intro A'. induction A' as [| (a2, e2)]. 
   + rewrite push_annot_nil. rewrite vatts_inter_nil_r.
     repeat (rewrite configVQtype_nil). rewrite atts_inter_nil_r.
     reflexivity. 
   + unfold configVQtype. unfold configVQtype in IHA. unfold configVQtype in IHA'.
     assert (I: (E[[ e \/(F) e']] c) = (E[[ e]] c) || (E[[ e']] c)). { reflexivity. }
     destruct (E[[ e]] c) eqn: E; destruct (E[[ e']] c) eqn: E'; rewrite I.
     ++ rewrite orb_true_r. destruct (E[[ e1]] c) eqn: E1; destruct (E[[ e2]] c) eqn: E2.
        { destruct (string_comp a1 a2) eqn:SC.
           + simpl. rewrite SC. rewrite E1. rewrite E2. 
             unfold configVAttSet; fold configVAttSet. 
             remember (E[[ (e1 /\(F) e) /\(F) e2 /\(F) e']] c). 
             simpl in Heqb. rewrite E1, E2, E, E' in Heqb. simpl in Heqb.
             rewrite Heqb. simpl. rewrite SC.
             rewrite I in IHA. simpl in IHA. rewrite IHA. reflexivity.
           + assert (I2 : (configVAttSet ((a2, e2) :: A') c) = if E[[ e2]] c
                then a2 :: configVAttSet A' c else configVAttSet A' c). 
             {simpl. rewrite E2. reflexivity. }
             simpl. rewrite E1. rewrite E2. simpl. rewrite SC. 
             rewrite E2 in I2. rewrite <- I2.  
             rewrite <- IHA. rewrite I. simpl. reflexivity.
          + unfold push_annot; fold push_annot. 
            rewrite ackerman_resolve_vatts_inter.
            unfold configVAttSet; fold configVAttSet.
            rewrite E1. 
            unfold configVAttSet; fold configVAttSet.
            rewrite E2. 
            rewrite ackerman_resolve_atts_inter. 
            unfold configVAttSet in IHA'; fold configVAttSet in IHA'.
            rewrite E1 in IHA'. 
            rewrite <- IHA'. rewrite I. auto. auto. auto.
        }
        { destruct (string_comp a1 a2) eqn:SC.
           + rewrite case1_req_global_lt_prop_inter.
             simpl. rewrite SC. 
             unfold configVAttSet; fold configVAttSet.
             remember (E[[ (e1 /\(F) e) /\(F) e2 /\(F) e']] c). 
             simpl in Heqb. rewrite E1, E2, E, E' in Heqb. simpl in Heqb.
             rewrite Heqb. 
             rewrite I in IHA. rewrite <- IHA. simpl. reflexivity. auto. 
             auto.
           + rewrite case1_req_global_lt_prop_inter. 
             simpl. rewrite SC. rewrite fold_push_annot. rewrite I in IHA. simpl in IHA.
             rewrite IHA. simpl. rewrite E2. reflexivity.
             auto. auto. 
          + unfold push_annot; fold push_annot. 
            rewrite ackerman_resolve_vatts_inter.
            unfold configVAttSet; fold configVAttSet.
            rewrite E1. 
            unfold configVAttSet; fold configVAttSet.
            rewrite E2.
            rewrite fold_push_annot.
            unfold configVAttSet in IHA'; fold configVAttSet in IHA'.
            rewrite E1 in IHA'. 
            rewrite <- IHA'.
            rewrite I. auto. auto. 
        }
        { destruct (string_comp a1 a2) eqn:SC.
           + rewrite case2_req_global_lt_prop_inter.
             simpl. rewrite SC. 
             unfold configVAttSet; fold configVAttSet.
             remember (E[[ (e1 /\(F) e) /\(F) e2 /\(F) e']] c). 
             simpl in Heqb. rewrite E1, E2, E, E' in Heqb. simpl in Heqb.
             rewrite Heqb. 
             rewrite I in IHA. rewrite <- IHA. simpl. reflexivity. auto. 
             auto.
           + admit.
           + admit.
           (*+ rewrite case2_req_global_lt_prop_inter.
            unfold push_annot; fold push_annot. 
            rewrite ackerman_resolve_vatts_inter.
            rewrite fold_push_annot. rewrite I in IHA'. 
            rewrite IHA'.
             simpl. rewrite SC. rewrite fold_push_annot. rewrite I in IHA. simpl in IHA.
             rewrite IHA. simpl. rewrite E2. reflexivity.
             auto. auto. 
          + unfold push_annot; fold push_annot. 
            rewrite ackerman_resolve_vatts_inter.
            rewrite hack_control_simpl. rewrite E1. 
            rewrite hack_control_simpl. rewrite E2.
            rewrite fold_push_annot.
            rewrite hack_control_simpl in IHA'.
            rewrite E1 in IHA'. 
            rewrite <- IHA'.
            rewrite I. auto. auto. *)
        }
      
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

(*high level proof explanantion*)
Theorem variation_preservation : forall e vq A, 
       vtype e vq A ->
       forall c, (E[[e]] c) = true ->
           type' (configVQuery vq c) = configVQtype A c.
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
     ++ rewrite IHvtype. simpl. unfold subsump_qtype_bool. 
        specialize H1 with c. rewrite H0, He' in H1. rewrite H1. rewrite H0. 
        reflexivity. assumption.
     ++ rewrite IHvtype. simpl. unfold subsump_qtype_bool. 
        specialize H1 with c. rewrite H0, He' in H1. 
        destruct (configVAttSet A c). rewrite H0.
        reflexivity. simpl in H1. discriminate H1. assumption.
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
    rewrite H01. rewrite H02.
    destruct (is_disjoint_bool (configVQtype (A1, e1) c)
    (configVQtype (A2, e2) c)) eqn: Hatts.
    + simpl. destruct (E[[ e1]] c) eqn: E1; reflexivity.
    + unfold is_disjoint_bool in Hatts.
      simpl in H2. 
      rewrite <- configVQType_dist_vatts_inter in Hatts.
      unfold vqtype_inter in H2. simpl fst in H2. simpl snd in H2.
      rewrite H2 in Hatts. simpl in Hatts. 
      destruct ((E[[ e1]] c) || (E[[ e2]] c)). discriminate Hatts.
      discriminate Hatts.
 (* Select - E *)
 (* SetOp - E *)
 - simpl in IHvtype1. simpl in IHvtype2. simpl. 
   + simpl. rewrite IHvtype1. rewrite IHvtype2.
     unfold configVQtype. simpl. 
     destruct H2. simpl in H2. simpl in H3. unfold equiv_vatts in H2.
     unfold equivE in H3. rewrite H2. rewrite H3. destruct (E[[ e2]] c) eqn: E'.
     ++ rewrite (equiv_qtype_bool_refl (configVAttSet A2 c)). reflexivity.
     ++ simpl. reflexivity. 
     ++ assumption. ++ assumption.
 
Qed.

End VRA_varPrsrvtn_thm.

