(** Variational relational algebra lemmas *)
Set Warnings "-notation-overridden,-parsing".


Load SetOPLemmas.


Ltac intro_nodupattconfig_rewrite H:= 
apply (nodupatt_equiv) in H;
unfold equiv_vatts in H;
rewrite H; clear H.

Ltac In_to_Inunion HA a A A' eq_dec :=
pose (set_union_intro1 eq_dec a A A' HA) as Htemp;
apply (In_set_add eq_dec) in Htemp.

Ltac In_to_InunionA' HA' a A A' eq_dec:=
pose (set_union_intro2 eq_dec a A A' HA') as Htemp;
apply (In_set_add eq_dec) in Htemp.

Ltac notIn_to_notInunion HA HA' a A A' eq_dec:=
pose (conj HA HA') as Htemp;
rewrite (notIn_set_union eq_dec a A A') in Htemp;
try (apply notIn_set_add_equiv_vatts in Htemp);
try (apply notIn_set_add_equiv_atts in Htemp).

Ltac set_add_to_cons H1 H2 a' c A A':=
(* ~ InAtt a' A' -> ~ In a' [[A']]c -  H1*)
apply notInAtt_notIn_config with (c:=c) in H1 as H1';
(* ~ InAtt a' (removeAtt a' A) -> ~ In a' [[removeAtt a' A]]c - H2 *)
apply notInAtt_notIn_config with (c:=c) in H2 as H2';
(* combine H1 and H2 with and *)
pose (conj H1' H2') as Hsetadd_cons;
(* combine H1 and H2 with union: ~ In a' ([[A]]c U [[removeAtt a' A]]c) *)
rewrite (notIn_set_union string_eq_dec _ _ _) in Hsetadd_cons;
(* ~ In a A -> set_add a A = a:: A *)
apply notIn_set_add_equiv_atts in Hsetadd_cons;
clear H1'; clear H2'.

Ltac NoDupAttAA'_NoDupUconfigAA' HA HA' c :=
pose (NoDupAtt_NoDup_config c HA) as HAtemp;
pose (NoDupAtt_NoDup_config c HA') as HA'temp; 
pose (set_union_nodup string_eq_dec HAtemp HA'temp) as HNDpUcAA'.

Lemma set_remove_dist_set_union_atts: forall a A A' (HA: NoDup A) (HA': NoDup A'), 
set_remove string_eq_dec a (set_union string_eq_dec A A') =a= 
set_union string_eq_dec (set_remove string_eq_dec a A) 
(set_remove string_eq_dec a A').
Proof.
intros a A. generalize dependent A. induction A'. 
- intro. simpl. reflexivity. 
- intros. simpl set_union at 1. 
  inversion HA' as [|a' A'' HnInA' HNdpA']; subst. 
  destruct (in_dec string_eq_dec a0 A). 
  + rename i into HInA. 
    In_to_Inunion HInA a0 A A' string_eq_dec. 
    rewrite Htemp.  clear Htemp. simpl.
    destruct (string_eq_dec a a0) eqn:Haa0; subst.
    ++ apply (notIn_set_remove_eq string_eq_dec)
        in HnInA'. rewrite <- HnInA' at 2. apply (IHA' HA HNdpA').
    ++ simpl set_union. apply (set_remove_3 string_eq_dec) with (b:=a) 
       in HInA as HInrmvA. 
       In_to_Inunion HInrmvA a0 (set_remove string_eq_dec a A) 
       (set_remove string_eq_dec a A') string_eq_dec. 
       rewrite Htemp. apply (IHA'). 
       all:try (eauto).
  + rename n into HnInA.
    notIn_to_notInunion HnInA HnInA' a0 A A' string_eq_dec.
    apply set_remove_equiv with (a:=a) in Htemp. rewrite Htemp.
    clear Htemp. simpl.
    destruct (string_eq_dec a a0) eqn:Haa0; subst.
    ++ apply (notIn_set_remove_eq string_eq_dec) in HnInA as HnInrmA.
       rewrite HnInrmA. reflexivity.
    ++ simpl set_union. apply (contrapositive _ _ 
       (set_remove_1 string_eq_dec a0 a A)) in HnInA
       as HnInrmvA. apply (contrapositive _ _ 
       (set_remove_1 string_eq_dec a0 a A')) in HnInA'
       as HnInrmvA'.  
       notIn_to_notInunion HnInrmvA HnInrmvA' a0 
       (set_remove string_eq_dec a A) 
       (set_remove string_eq_dec a A') string_eq_dec. 
       rewrite Htemp.
       apply cons_equiv_atts. 
       apply (IHA'). all: assumption.
   ++ pose (set_union_nodup string_eq_dec HA HNdpA')
      as HNdpU. apply (set_add_nodup string_eq_dec a0) in HNdpU.
      assumption.
   ++ apply NoDup_cons. pose (conj HnInA HnInA') as HnInU.
      rewrite (notIn_set_union string_eq_dec a0 A A') in HnInU.
      assumption. pose (set_union_nodup string_eq_dec HA HNdpA')
      as HNdpU. assumption.
Qed.

(* -- removeAtt set_union -- *)
Lemma removeAtt_dist_set_union_vatts : forall a A A', 
removeAtt a (set_union vatt_eq_dec A A') =va= 
set_union vatt_eq_dec (removeAtt a A) (removeAtt a A').
Proof. intros a A. generalize dependent A. induction A'. 
- intro. simpl. reflexivity. 
- intros. simpl set_union at 1. 
  destruct a0 as (a0, e0). destruct (in_dec vatt_eq_dec (ae a0 e0) A'). 
-- rename i into HInA'. 
    In_to_InunionA' HInA' (ae a0 e0) A A' vatt_eq_dec. 
    rewrite Htemp.  clear Htemp. simpl.
    destruct (string_beq a a0) eqn:Haa0.
    ++ apply (IHA').
    ++ simpl set_union. apply In_removeAtt with (a:=a) in HInA'
       as HInrmvA'. 
       In_to_InunionA' HInrmvA' (ae a0 e0) (removeAtt a A) (removeAtt a A') vatt_eq_dec. 
       rewrite Htemp. apply (IHA'). rewrite <- stringBEF.eqb_neq.
       assumption.
-- rename n into HnInA'.
  destruct (in_dec vatt_eq_dec (ae a0 e0) A). 
  + rename i into HInA. 
    In_to_Inunion HInA (ae a0 e0) A A' vatt_eq_dec. 
    rewrite Htemp.  clear Htemp. simpl.
    destruct (string_beq a a0) eqn:Haa0.
    ++ apply (IHA').
    ++ simpl set_union. apply In_removeAtt with (a:=a) in HInA
       as HInrmvA. 
       In_to_Inunion HInrmvA (ae a0 e0) (removeAtt a A) (removeAtt a A') vatt_eq_dec. 
       rewrite Htemp. apply (IHA'). rewrite <- stringBEF.eqb_neq.
       assumption.
  + rename n into HnInA.
    notIn_to_notInunion HnInA HnInA' (ae a0 e0) A A' vatt_eq_dec.
    rewrite (removeAtt_equiv _ Htemp). clear Htemp.
    simpl.
    destruct (string_beq a a0) eqn:Haa0.
    ++ apply (IHA').
    ++ simpl set_union. apply notIn_notInremoveAtt with (a:=a) in HnInA
       as HnInrmvA. apply notIn_notInremoveAtt with (a:=a) in HnInA'
       as HnInrmvA'.  
       notIn_to_notInunion HnInrmvA HnInrmvA' (ae a0 e0) 
       (removeAtt a A) (removeAtt a A') vatt_eq_dec.
       rewrite Htemp.
       apply cons_equiv_vatts. 
       apply (IHA').
Qed.

Lemma configVAttSet_dist_vatts_union : forall A  A' c (HA: NoDupAtt A)
(HA': NoDupAtt A'), configVAttSet (vatts_union A A') c =a=
      atts_union (configVAttSet A c) (configVAttSet A' c) .
Proof. intros A A'. generalize dependent A. induction A' as [|a' A' IHA'].
- destruct A as [| a A]. 
  + intros. simpl. reflexivity.
  + intros. simpl configVAttSet at 3.
    rewrite vatts_union_nil_r. rewrite atts_union_nil_r.
    reflexivity. auto.
- intros A c Ha Ha'. destruct a' as (a', e').
  unfold vatts_union. unfold vatts_union in IHA'.
  pose (NoDupAtt_NoDup Ha') as Hndp.
  inversion Hndp as [|a'' e'' HnInA' HNDpA']; subst.
  simpl set_union. clear Hndp.
  (* modify context to get InAtt (set_union) *)
  destruct (in_dec vatt_eq_dec (ae a' e') A).
  + (* In (ae a' e') A *)
    (* rewrite existsb_In in HInAcase. *)
    rename i into HInA.
    In_to_Inunion HInA (ae a' e') A A' vatt_eq_dec.
    apply eq_equiv_vatts in Htemp.
    intro_nodupattconfig_rewrite Htemp.
    simpl. 
    destruct (E[[ e']] c) eqn:He'.
    ++ simpl atts_union. unfold atts_union.
       unfold atts_union in IHA'.
       (* In (ae a' e') A -> (* In a' [[A]]c *)*)
       pose (In_config_true a' e' A c HInA He') as HIc.
       apply (set_union_intro1 string_eq_dec) with (y:= (configVAttSet A' c)) in HIc.
       apply (In_set_add string_eq_dec) in HIc. 
       rewrite HIc. clear HIc.
       apply IHA'. auto. inversion Ha'. auto.
    ++ apply IHA'. auto. inversion Ha'. auto.
  + (* ~ In (ae a' e') A *)
    (*rewrite not_existsb_In in HInAcase. Locate combine.*)
    rename n into HnInA.
    notIn_to_notInunion HnInA HnInA' (ae a' e') A A' vatt_eq_dec.
    intro_nodupattconfig_rewrite Htemp.
    (* nodupatt_equation can be destructed in two case *)
    simpl_nodupatt.
    destruct (existsbAtt a' (set_union vatt_eq_dec A A')) eqn:HnInAttU.
    ++ existsbAtt_InAtt in HnInAttU. simpl. 
      (* invert to ~ InAtt a' A' *)
       inversion Ha' as [| a'' e'' A'' HnInAttA' HNdpAttA']; subst.
       destruct (E[[ e']] c) eqn:He'. 
       +++ 
           rewrite orb_true_l.
           simpl atts_union. 
           rewrite set_add_remove. 
           (*rewrite remove_dist_attsunion.*)
           apply NoDupAtt_NoDup_config with (c:=c) in Ha as HNdpCA.
           apply NoDupAtt_NoDup_config with (c:=c) in HNdpAttA' as HNdpCA'.
           rewrite (set_add_equiv _
           (set_remove_dist_set_union_atts _ HNdpCA HNdpCA')).
           repeat (rewrite set_remove_config).
           (* removeAtt a' A' = A' as ~ InAtt a' A' *)
           rewrite (notInAtt_removeAtt_eq A' a' HnInAttA').
           (* intro HInremA: ~ InAtt a' (removeAtt a' A) *)
           pose (notInAtt_removeAtt A a') as HInremA.
           (* convert set_add to cons in goal*)
             (* get set_add to cons relation (as H) in the current context *)
             set_add_to_cons HInremA HnInAttA' a' c A A'.
             (* rewrite (H) in goal *)
             rewrite Hsetadd_cons. 
           apply cons_equiv_atts. 
           (*rewrite removeAtt_dist_set_union_vatts;
           rewrite (notInAtt_removeAtt_eq A' a' HnInAttA').*)
           pose (nodupatt_equiv
           (removeAtt_dist_set_union_vatts a' A A')) as Hndprmv.
           unfold equiv_vatts in Hndprmv.
           rewrite Hndprmv.
           rewrite (notInAtt_removeAtt_eq A' a' HnInAttA').
           unfold atts_union in IHA'. apply IHA'.
           apply NoDupAtt_removeAtt. all: try (assumption). 
           NoDupAttAA'_NoDupUconfigAA' Ha HNdpAttA' c.
           unfold atts_union.
           apply HNDpUcAA'.
         
       +++ rewrite orb_false_l. 
           (* get InAtt a' A *)
           rewrite InAtt_set_union in HnInAttU.
           pose (or_not _ _ HnInAttU HnInAttA') as HInAttA.
           destruct (E[[ extract_e a' (set_union vatt_eq_dec A A')]]c) eqn: Hexta';
           (*  ~ InAtt a' A' -> 
                extract_e a' (A U A') = extract_e a' A  *)
           rewrite (extract_set_union _ _ Ha HNdpAttA') in Hexta';
           rewrite (notInAtt_extract _ _ HnInAttA') in Hexta';
           simpl in Hexta'; 
           rewrite orb_false_r in Hexta';
           (*  ~ InAtt a' A' ->  ~ In (a', e) A*)
           assert (HInA: InAtt a' A); auto;
           apply InAtt_In_exfexp in HInA;
           destruct HInA as [e HInA];
           (* extract_e a' A = e, given NoDupAtt A *)
           assert (Hexeqe: In (ae a' e) A); auto; 
           apply (In_extract _ _ Ha) in Hexeqe.

           { (* E[[ extract_e ...]]c = true *)
           (* In a A to In a [A] c for [[e]]c = true*)
           apply In_config_true with (c:=c) in HInA.
           (* In a [A]c -> In a [A]c U _ *)
           apply (set_union_intro1 string_eq_dec) with (y:= (configVAttSet A' c)) in HInA.
           unfold set_In in HInA.
           (* introduce set_add a (set_remove a ) in the RS*)
           unfold atts_union.
           NoDupAttAA'_NoDupUconfigAA' Ha HNdpAttA' c.
           
           rewrite <- (In_set_add_remove a' HNDpUcAA' HInA).
           (* *)
           
           (*rewrite remove_dist_attsunion.*)
            (*rewrite (set_add_equiv _
           (set_remove_dist_set_union_atts a' (configVAttSet A c) (configVAttSet A' c))).*)
           apply NoDupAtt_NoDup_config with (c:=c) in Ha as HNdpCA.
           apply NoDupAtt_NoDup_config with (c:=c) in HNdpAttA' as HNdpCA'.
           rewrite (set_add_equiv _
           (set_remove_dist_set_union_atts _ HNdpCA HNdpCA')).
          
           repeat (rewrite set_remove_config).
           repeat (rewrite set_remove_config).
           rewrite (notInAtt_removeAtt_eq A' a' HnInAttA').
           clear HInAttA.
           (* intro HInremA: ~ InAtt a' (removeAtt a' A) *)
           pose (notInAtt_removeAtt A a') as HInremA.
           (* convert set_add to cons in goal*)
            (* get set_add to cons relation (as H) in the current context *)
             set_add_to_cons HInremA HnInAttA' a' c A A'.
            (* rewrite (H) in goal *)
            rewrite Hsetadd_cons.
           apply cons_equiv_atts. 
           pose (nodupatt_equiv
           (removeAtt_dist_set_union_vatts a' A A')) as Hndprmv.
           unfold equiv_vatts in Hndprmv.
           rewrite Hndprmv.
           rewrite (notInAtt_removeAtt_eq A' a' HnInAttA').
           unfold atts_union in IHA'. apply IHA'.
           apply NoDupAtt_removeAtt. all: try(assumption).  
           rewrite Hexeqe in Hexta'. simpl in Hexta'.
           rewrite orb_false_r in Hexta'. assumption. 
           }

           { (* E[[ extract_e ...]]c = false *)
           (* In a A to ~In a [A] c for [[e]]c = false*)
           apply In_config_false with (c:=c) in HInA.
           pose (conj HInA (notInAtt_notIn_config a' A' c HnInAttA')) as HInU.
           rewrite (notIn_set_union string_eq_dec) in HInU.
           unfold atts_union.
           rewrite <- (notIn_set_remove_eq string_eq_dec _ _ HInU).
           apply NoDupAtt_NoDup_config with (c:=c) in Ha as HNdpCA.
           apply NoDupAtt_NoDup_config with (c:=c) in HNdpAttA' as HNdpCA'.
           rewrite (set_remove_dist_set_union_atts _ HNdpCA HNdpCA').
           repeat (rewrite set_remove_config).
           pose (nodupatt_equiv
           (removeAtt_dist_set_union_vatts a' A A')) as Hndprmv.
           unfold equiv_vatts in Hndprmv.
           rewrite Hndprmv.
           rewrite (notInAtt_removeAtt_eq A' a' HnInAttA').
           unfold atts_union in IHA'. 
           apply IHA'.
           apply NoDupAtt_removeAtt. 
           all: try(assumption).
           rewrite Hexeqe in Hexta'. simpl in Hexta'.
           rewrite orb_false_r in Hexta'. 
           assumption.
           }

   ++ not_existsbAtt_InAtt in HnInAttU. simpl.  
      rewrite InAtt_set_union in HnInAttU.
      apply Classical_Prop.not_or_and in HnInAttU.
      destruct HnInAttU.
      destruct (E[[ e']] c) eqn:He'.
      +++ simpl atts_union. unfold atts_union.
      set_add_to_cons H H0 a' c A A'.
      rewrite Hsetadd_cons. clear Hsetadd_cons.
      apply cons_equiv_atts. 
      unfold atts_union in IHA'. apply IHA'. 
      auto. inversion Ha'; subst. auto.
      +++ apply IHA'. 
      auto. inversion Ha'; subst. auto.
Qed.

Lemma configVQType_dist_vatts_union : forall A A' e c (HA: NoDupAtt A)
(HA': NoDupAtt A'), configVQtype (vatts_union A A', e) c
=a= atts_union (configVQtype (A, e) c) (configVQtype (A', e) c).
Proof. 
intros A A' e c. unfold configVQtype. destruct (E[[ e]] c) eqn: He.
apply configVAttSet_dist_vatts_union.
intros. simpl. reflexivity.
Qed.

Lemma configVAttSet_push_annot A e c:
configVAttSet (push_annot A e) c = configVQtype (A, e) c.
Proof. induction A. 
simpl. destruct ( E[[ e]] c); reflexivity.
unfold push_annot; fold push_annot.
destruct a. simpl configVQtype. 
simpl configVQtype in IHA.
simpl configVAttSet.
destruct (E[[ e]] c); destruct (E[[ f]] c); simpl;
try(eauto).
rewrite IHA. reflexivity.
Qed.

Lemma configVAttSet_dist_vatts_inter : forall A  A' c (HA: NoDupAtt A)
(HA': NoDupAtt A'), configVAttSet (vatts_inter A A') c =
      atts_inter (configVAttSet A c) (configVAttSet A' c).
Proof. intros. induction A.
- simpl. reflexivity.
- simpl.  destruct a. inversion HA; subst.
rewrite vatts_inter_equation. 
destruct (E[[ f]]c) eqn:Hf. { simpl atts_inter.
destruct (set_mem string_eq_dec a (configVAttSet A' c)) eqn: HaA'.
+ apply (set_mem_correct1 string_eq_dec) in HaA'. 
apply extract_true_In in HaA' as Hextract.
apply In_InAtt_config in HaA' as HInattaA'. 
rewrite <- existsbAtt_InAtt in HInattaA'. rewrite HInattaA'.
simpl configVAttSet. rewrite Hf, Hextract, IHA. simpl. 
reflexivity.  assumption.
+  apply (set_mem_complete1 string_eq_dec) in HaA'. 
rewrite <- extract_true_In in HaA'. rewrite not_true_iff_false in HaA'.
destruct (existsbAtt a A'). simpl configVAttSet. 
rewrite IHA, HaA'. rewrite andb_false_r. reflexivity.
assumption. apply(IHA H3). }
{ destruct (existsbAtt a A'). simpl configVAttSet. 
rewrite Hf, IHA. rewrite andb_false_l. reflexivity.
assumption. apply(IHA H3). }
Qed.

Lemma configVQType_dist_vatts_inter : forall A A' e e' c 
(HA: NoDupAtt A) (HA': NoDupAtt A'), 
configVQtype (vatts_inter (push_annot A e)
       (push_annot A' e'), e \/(F) e') c
= atts_inter (configVQtype (A, e) c) (configVQtype (A', e') c).
Proof. intros. unfold configVQtype. 
simpl. destruct (E[[ e]] c) eqn: He;
[rewrite orb_true_l | rewrite orb_false_l];
destruct (E[[ e']] c) eqn: He';
try(rewrite configVAttSet_dist_vatts_inter);
try(repeat(rewrite configVAttSet_push_annot));
simpl; simpl configVQtype; try(rewrite He, He');
try(eauto).  
Qed. 