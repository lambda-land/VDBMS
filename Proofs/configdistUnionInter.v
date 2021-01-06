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

Ltac NoDupAttAA'_NoDupAcUAc' HA HA' c :=
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

(*Lemma vatts_union_cases A b eb B : NoDupAtt (ae b eb::B) -> 
(  In (ae b eb) A -> vatts_union A (ae b eb::B) =va= vatts_union A B ) \/
(~ In (ae b eb) A -> 
   (  InAtt b A -> vatts_union A (ae b eb::B) =va= 
                   ( ae b (eb \/(F) (extract_e b A)) ::
                           vatts_union (removeAtt b A) B ) ) \/
   ( ~InAtt b A ->  )
).

*)

(* ---------- vatts_union case analysis lemmas -------------  *)

Lemma vatts_union_InA A b eb B : 
In (ae b eb) A -> vatts_union A (ae b eb::B) =va= vatts_union A B .

Proof.
intro HInA.
In_to_Inunion HInA (ae b eb) A B vatt_eq_dec.
apply eq_equiv_vatts in Htemp. 
apply nodupatt_equiv in Htemp. (* intro_nodupattconfig_rewrite Htemp. *)
auto.
Qed.

Lemma vatts_union_nInA_InAttA A b eb B {HndpAttA: NoDupAtt A}
{HndpAttbB: NoDupAtt (ae b eb::B)} : 
~ In (ae b eb) A /\ InAtt b A -> 
   vatts_union A (ae b eb::B) =va= ( ae b (eb \/(F) extract_e b (set_union vatt_eq_dec A B)) 
                                   :: vatts_union (removeAtt b A) B ).
Proof.
(* derive ~ In (ae b eb) B *)
apply NoDupAtt_NoDup in HndpAttbB as HndpbB.
inversion HndpbB as [|b' eb' HnInB HndpB]; subst.

intros H. destruct H as [HnInA HInAttA].

(* HInAttA: InAtt b A -> InAtt b (set_union _ A B) *)
assert(HInAttAUB: InAtt b (set_union vatt_eq_dec A B)).
rewrite InAtt_set_union. eauto.
 
notIn_to_notInunion HnInA HnInB (ae b eb) A B vatt_eq_dec.
apply nodupatt_equiv in Htemp. (* intro_nodupattconfig_rewrite Htemp. *)
rewrite Htemp. 

simpl_nodupatt.
InAtt_existsbAtt in HInAttAUB. rewrite HInAttAUB.
existsbAtt_InAtt in HInAttAUB. simpl.

(* derive ~InAtt b B *)
inversion HndpAttbB as [|b' eb' B' HnInAttB HndpAttB]; subst.
(*unfold equiv_vatts. simpl. intro c.*)

apply cons_equiv_vatts.
(* 
~ InAtt b B
----------------------------------------------------
nodupatt (removeAtt b (set_union vatt_eq_dec A B)) 
*)
pose (nodupatt_equiv
   (removeAtt_dist_set_union_vatts b A B)) as Hndprmv.

rewrite Hndprmv.
rewrite (notInAtt_removeAtt_eq B b HnInAttB).
(* 
~ InAtt b B
----------------------------------------------------
 nodupatt (set_union vatt_eq_dec (removeAtt b A) B)
*)
reflexivity.
Qed.

Lemma vatts_union_nInA_nInAttA A b eb B {HndpAttbB: NoDupAtt (ae b eb::B)} : 
~ In (ae b eb) A /\ ~ InAtt b A -> 
   vatts_union A (ae b eb::B) =va= 
                   ( ae b eb :: vatts_union A B ).
Proof.
(* derive ~ In (ae b eb) B *)
apply NoDupAtt_NoDup in HndpAttbB as HndpbB.
inversion HndpbB as [|b' eb' HnInB HndpB]; subst.

(* derive ~InAtt b B *)
inversion HndpAttbB as [|b' eb' B' HnInAttB HndpAttB]; subst.

intros H. destruct H as [HnInA HnInAttA].

(* HInAttA: InAtt b A -> InAtt b (set_union _ A B) *)
assert(HInAttAUB: ~InAtt b (set_union vatt_eq_dec A B)).
rewrite <- notInAtt_set_union. eauto.
 
notIn_to_notInunion HnInA HnInB (ae b eb) A B vatt_eq_dec.
apply nodupatt_equiv in Htemp. (* intro_nodupattconfig_rewrite Htemp. *)
rewrite Htemp. 

simpl_nodupatt.
InAtt_existsbAtt in HInAttAUB. rewrite not_true_iff_false in HInAttAUB.
rewrite HInAttAUB.
simpl.

apply cons_equiv_vatts. reflexivity.
Qed.

(* destruct (in_dec vatt_eq_dec (ae a' e') A) as [HInA | HnInA].
  + (* In (ae a' e') A *)
    apply vatts_union_InA with (B:=A') in HInA as Hequiv.

  + (* ~ In (ae a' e') A *)
     destruct (existsbAtt a' A) eqn:HexstAttA.
     ++ (* InAtt a' A *) existsbAtt_InAtt in HexstAttA. 
         rename HexstAttA into HInAttA.
         rewrite (vatts_union_nInA_InAttA) with (A:=A).

     ++ (* ~ InAtt a' A *)  not_existsbAtt_InAtt in HexstAttA. 
        rename HexstAttA into HnInAttA.
        rewrite (vatts_union_nInA_nInAttA) with (A:=A).
*)
(* ------------------------------case analysis -------------------------*)

Lemma vatts_union_nInAttA_nInAttB b A B eb c: 
~ InAtt b A -> ~ InAtt b B ->
(A[[ vatts_union A B]] c) =a= atts_union (A[[ A]] c) (A[[ B]] c) ->
(A[[ ae b eb :: vatts_union A B]] c) =a= 
                      atts_union (A[[ A]] c) (A[[ ae b eb :: B]] c).
Proof. intros HnInAttA HnInAttB H.
simpl. destruct (E[[ eb]] c) eqn:Heb.
+++ simpl atts_union. unfold atts_union.
    set_add_to_cons HnInAttA HnInAttB b c A B.
    rewrite Hsetadd_cons; clear Hsetadd_cons.
    apply cons_equiv_atts. 
    unfold atts_union in H. apply H; assumption.
+++ apply H; try assumption.
Qed.
  

Lemma In_set_union_removeAtt a' A A' c (HNdpAttA: NoDupAtt A)
(HNdpAttA': NoDupAtt A'):  In a' (A[[ A]] c) -> ~InAtt a' A' ->
       set_union string_eq_dec (A[[ A]] c)              (A[[ A']] c) =a= 
(a' :: set_union string_eq_dec (A[[ removeAtt a' A]] c) (A[[ A']] c)).
Proof. 
intros HInA HnInAttA'.
apply (set_union_intro1 string_eq_dec) with (y:= (configVAttSet A' c)) in HInA.
unfold set_In in HInA.
      
(* HNDpUcAA': NoDup (atts_union (A[[ A]] c) (A[[ A']] c)) *)   
NoDupAttAA'_NoDupAcUAc' HNdpAttA HNdpAttA' c.

(* set add a (set remove a A) =a= A *)
rewrite <- (In_set_add_remove a' HNDpUcAA' HInA).
       
(* NoDupAtt -> NoDup A[[ ]] c *)
apply NoDupAtt_NoDup_config with (c:=c) in HNdpAttA as HNdpCA.
apply NoDupAtt_NoDup_config with (c:=c) in HNdpAttA' as HNdpCA'.

(* set_remove a (set_union A B) =a= set_union (set_remove a A) (set_remove a B) *)
rewrite (set_add_equiv _
           (set_remove_dist_set_union_atts _ HNdpCA HNdpCA')); try assumption.

(*set_remove a A[[ A]] c =a= A[[set_remove a A ]] c *)
repeat (rewrite set_remove_config; try assumption).

(* ~InAtt a' A -> removeAtt a' A =a= A *)
rewrite (notInAtt_removeAtt_eq A' a' HnInAttA').
          
(* intro HInremA: ~ InAtt a' (removeAtt a' A) *)
pose (notInAtt_removeAtt A a') as HInremA.

(* ~ In a A -> set_add a A =a= a::A *)
set_add_to_cons HInremA HnInAttA' a' c A A'.
rewrite Hsetadd_cons.  

reflexivity.

Qed.

Lemma notInAtt_set_union_removeAtt a' A A' c (HNdpAttA: NoDupAtt A)
(HNdpAttA': NoDupAtt A'): 
~ In a' (A[[ A]] c) -> ~InAtt a' A' ->
set_union string_eq_dec (A[[ A]] c)              (A[[ A']] c) =a= 
set_union string_eq_dec (A[[ removeAtt a' A]] c) (A[[ A']] c).
Proof. 
intros HnInA HnInAttA'.
pose (conj HnInA (notInAtt_notIn_config a' A' c HnInAttA')) as HnInU.
rewrite (notIn_set_union string_eq_dec) in HnInU.
           
rewrite <- (notIn_set_remove_eq string_eq_dec _ _ HnInU).

apply NoDupAtt_NoDup_config with (c:=c) in HNdpAttA as HNdpCA.
apply NoDupAtt_NoDup_config with (c:=c) in HNdpAttA' as HNdpCA'.

rewrite (set_remove_dist_set_union_atts _ HNdpCA HNdpCA').
repeat (rewrite set_remove_config; try assumption).
           
rewrite (notInAtt_removeAtt_eq A' a' HnInAttA').

reflexivity.
Qed.

Lemma notInAttA'_set_union_cons_removeAtt a' A' A c (HNdpAttA: NoDupAtt A) (HNdpAttA': NoDupAtt A'):
 ~ InAtt a' A' -> 
       set_union string_eq_dec (A[[ A]] c)              (a' :: (A[[ A']] c)) =a= 
(a' :: set_union string_eq_dec (A[[ removeAtt a' A]] c)        (A[[ A']] c)) .
Proof.  intro HnInAttA'. 

(* derive Nodup NoDup (atts_union (A[[ A]] c) (A[[ A']] c)) *) 
NoDupAttAA'_NoDupAcUAc' HNdpAttA HNdpAttA' c.

simpl set_union.
rewrite set_add_remove; try assumption.
 
apply NoDupAtt_NoDup_config with (c:=c) in HNdpAttA as HNdpCA.
apply NoDupAtt_NoDup_config with (c:=c) in HNdpAttA' as HNdpCA'.

rewrite (set_add_equiv _
           (set_remove_dist_set_union_atts _ HNdpCA HNdpCA')).

repeat (rewrite set_remove_config; try assumption).
(* removeAtt a' A' = A' as ~ InAtt a' A' *)
rewrite (notInAtt_removeAtt_eq A' a' HnInAttA').
(* intro HInremA: ~ InAtt a' (removeAtt a' A) *)
pose (notInAtt_removeAtt A a') as HInremA.
         
set_add_to_cons HInremA HnInAttA' a' c A A'.
           
rewrite Hsetadd_cons. reflexivity.
Qed.

Hint Resolve NoDupAtt_removeAtt : core.

Lemma notInAttA'_extract_set_union:
  forall (a : att) [A A' : list vatt] (c : config),
  NoDupAtt A ->
  NoDupAtt A' ->
  ~ InAtt a A' ->
  (E[[ extract_e a (set_union vatt_eq_dec A A')]] c) =
  (E[[ extract_e a A]] c).
Proof. intros a A A' c HndpAttA HndpAttA' HnInAttA'. 
rewrite (extract_set_union _ _ HndpAttA HndpAttA').
rewrite (notInAtt_extract _ _ HnInAttA'). simpl.
rewrite orb_false_r. reflexivity. Qed.
       

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
  (*unfold vatts_union. unfold vatts_union in IHA'.*)
  pose (NoDupAtt_NoDup Ha') as Hndp.
  inversion Hndp as [|a'' e'' HnInA' HNDpA']; subst.
  clear Hndp.

  inversion Ha' as [| a'' e'' A'' HnInAttA' HNdpAttA']; subst.
  simpl set_union. 
  (* modify context to get InAtt (set_union) *)
  destruct (in_dec vatt_eq_dec (ae a' e') A) as [HInA | HnInA].
  + (* In (ae a' e') A *)
    apply vatts_union_InA with (B:=A') in HInA as Hequiv.
    unfold "=va=" in Hequiv. rewrite Hequiv.
    simpl. destruct (E[[ e']] c) eqn:He'.
    ++ simpl atts_union. unfold atts_union.
       unfold atts_union in IHA'.
       (* In (ae a' e') A -> (* In a' A[[A]]c *)*)
       pose (In_config_true a' e' A c HInA He') as HIc.
       apply (set_union_intro1 string_eq_dec) with (y:= (A[[ A']]c)) in HIc.
       apply (In_set_add string_eq_dec) in HIc. rewrite HIc. clear HIc.
       apply IHA'; eauto. 
    ++ apply IHA'; eauto.
  + (* ~ In (ae a' e') A *)
     destruct (existsbAtt a' A) eqn:HexstAttA.
     ++ (* InAtt a' A *) 
         existsbAtt_InAtt in HexstAttA. rename HexstAttA into HInAttA.
         apply (vatts_union_nInA_InAttA) with (A:=A) in Ha' as Hequiv;
         try( split; assumption); try assumption.
         unfold "=va=" in Hequiv. rewrite Hequiv.
         simpl. destruct (E[[ e']] c) eqn:He'. 
         +++ (* (E[[ e']] c) = true *) rewrite orb_true_l.
             rewrite (notInAttA'_set_union_cons_removeAtt _ c Ha HNdpAttA' HnInAttA').

             apply cons_equiv_atts. apply IHA'; eauto.
         
         +++ (* (E[[ e']] c) = false *) rewrite orb_false_l. 
             (* ~ InAtt a' A'-> E[[ extract_e a' (set_union vatt_eq_dec A A')]]c = 
                                E[[ extract_e a' A]]c *)
             rewrite notInAttA'_extract_set_union; try assumption.
             apply InAtt_extract in HInAttA as HInAexe; try assumption.
             destruct HInAexe as [e [HInA Hexeqe] ].

             destruct (E[[ extract_e a' A]] c) eqn: Hexta'.

             { (* E[[ extract_e a' A]]c = true *)

              (* E[[ extract_e a' A]]c = true -> E[[e]]c = true *)
              rewrite Hexeqe in Hexta'. simpl in Hexta'.
              rewrite orb_false_r in Hexta'.

              (* E[[e]]c = true /\ In (ae a e) A -> In a A[[A]]c *)
              apply In_config_true with (c:=c) in HInA; try assumption.
              
              (* atts_union (A[[ A]] c) (A[[ A']] c) -> 
                    (a' :: atts_union (A[[ removeAtt a' A]] c) (A[[ A']] c)) *)
              rewrite (In_set_union_removeAtt _ c Ha HNdpAttA' HInA HnInAttA').

              apply cons_equiv_atts. apply IHA'; eauto.
             }

             { (* E[[ extract_e a' A]]c = false *)
          
              (* E[[ extract_e a' A]]c = false -> E[[e]]c = false *)
              rewrite Hexeqe in Hexta'. simpl in Hexta'.
              rewrite orb_false_r in Hexta'.

              (*  E[[e]]c = false /\ In (ae a e) A -> ~ In a A[[[A]]c*)
              apply In_config_false with (c:=c) in HInA; try assumption.
              rewrite (notInAtt_set_union_removeAtt _ c Ha HNdpAttA' HInA HnInAttA').
              
              apply IHA'; eauto.
             }

     ++ (* ~ InAtt a' A *)  not_existsbAtt_InAtt in HexstAttA. 
        rename HexstAttA into HnInAttA.
        apply (vatts_union_nInA_nInAttA) with (A:=A) in Ha' as Hequiv;
        try(split; assumption).
        unfold "=va=" in Hequiv. rewrite Hequiv.
        apply vatts_union_nInAttA_nInAttB; eauto.

Qed.


Lemma configVQType_dist_vqtype_union_vq : forall Q Q' c (HA: NoDupAtt (fst Q))
(HA': NoDupAtt (fst Q')), configVQtype (vqtype_union_vq Q Q') c
=a= atts_union (configVQtype Q c) (configVQtype Q' c).
Proof. 
intros Q Q' c HQ HQ'. destruct Q as (A, e). destruct Q' as (A', e').
unfold vqtype_union_vq, configVQtype, configaVatts. simpl fst. simpl snd. 
simpl. 
destruct (E[[ e]] c) eqn: He; simpl; [|
destruct (E[[ e']] c) eqn: He'; simpl; [ | (* [] =a= [] *)simpl; reflexivity] ]; 

rewrite configVAttSet_dist_vatts_union; 
try (apply NoDupAtt_push_annot; auto); simpl;
repeat(rewrite configVAttSet_push_annot); simpl;
rewrite He; [|rewrite He']; reflexivity. 

Qed.

(*Lemma configVQType_dist_vatts_union : forall A A' e c (HA: NoDupAtt A)
(HA': NoDupAtt A'), configVQtype (vatts_union A A', e) c
=a= atts_union (configVQtype (A, e) c) (configVQtype (A', e) c).
Proof. 
intros A A' e c. unfold configVQtype, configaVatts.
destruct (E[[ e]] c) eqn: He.
apply configVAttSet_dist_vatts_union.
intros. simpl. reflexivity.
Qed.*)



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

Lemma vatts_inter_equiv A A' B B' (HA: NoDupAtt A) (HA': NoDupAtt A')
(HB: NoDupAtt B) (HB': NoDupAtt B'): A =va= A' ->
B =va= B' ->
vatts_inter A B =va= vatts_inter A' B'. 
Proof. intros H1 H2.
unfold equiv_vatts in H1.
unfold equiv_vatts in H2.
unfold equiv_vatts. intro c.
repeat(rewrite configVAttSet_dist_vatts_inter).
apply set_inter_equiv. all: try(assumption);
try (apply (NoDupAtt_NoDup_config); assumption).
apply H1. apply H2. Qed.


Lemma vqtype_inter_vq_equiv A A' B B' (HA: NoDupAtt (fst A)) 
(HA': NoDupAtt (fst A'))
(HB: NoDupAtt (fst B)) (HB': NoDupAtt (fst B')): A =T= A' ->
B =T= B' ->
vqtype_inter_vq A B =T= vqtype_inter_vq A' B'. 
Proof. intros HAt HBt.  
unfold equiv_vqtype in HAt. 
unfold equiv_vqtype in HBt. 
unfold equiv_vqtype. intro c. specialize HAt with c.
specialize HBt with c. destruct A as (A, ea).
destruct B as (B, eb). destruct A' as (A', ea').
destruct B' as (B', eb'). unfold vqtype_inter_vq.
simpl. simpl in *. 
destruct (E[[ea]]c); destruct (E[[ea']]c);
destruct (E[[eb]]c); destruct (E[[eb']]c);
simpl; repeat(rewrite configVAttSet_dist_vatts_inter);
try(assumption); try reflexivity;
[ apply set_inter_equiv
| rewrite set_inter_equiv with (B:=(A[[ A]] c)) (B':=[])
| rewrite set_inter_equiv with (B:=(A[[ A']] c)) (B':=[])
| rewrite set_inter_equiv with (B:=[]) (B':=(A[[ B]] c))
| rewrite set_inter_equiv with (B:=[]) (B':=[])
| rewrite set_inter_equiv with (B:=[]) (B':=(A[[ B']] c))
| rewrite set_inter_equiv with (B:=[]) (B':=[])];

try reflexivity; try(assumption);
try (apply (NoDupAtt_NoDup_config); assumption);
try (apply NoDup_nil).

rewrite atts_inter_nil_r. reflexivity.
rewrite atts_inter_nil_r. reflexivity.
all: symmetry; assumption.

(*intros HAt HBt. unfold equiv_vqtype in HAt. destruct HAt.
unfold equiv_vqtype in HBt. destruct HBt. 
unfold equiv_vqtype.
simpl. split. apply vatts_inter_equiv. all :(try assumption).
unfold equivE. intro. simpl. rewrite H0, H2. reflexivity.*) Qed.

Lemma configVAttSet_vatts_inter_nil_l A B c (HA: NoDupAtt A) (HB: NoDupAtt B): (A[[ A]] c) =a= [] ->
(A[[vatts_inter A B]] c) =a= []. 
Proof. intro H. 
rewrite configVAttSet_dist_vatts_inter.
apply atts_inter_nil_l_equiv.
1, 2: apply (NoDupAtt_NoDup_config); assumption. 
all: eauto.
Qed.

Lemma configVAttSet_vatts_inter_nil_r A B c (HA: NoDupAtt A) (HB: NoDupAtt B): (A[[ B]] c) =a= [] ->
(A[[vatts_inter A B]] c) =a= []. 
Proof. intro H. 
rewrite configVAttSet_dist_vatts_inter.
apply atts_inter_nil_r_equiv.
1, 2: apply (NoDupAtt_NoDup_config); assumption. 
all: eauto.
Qed.


Lemma vatts_union_equiv A A' B B' (HA: NoDupAtt A) (HA': NoDupAtt A')
(HB: NoDupAtt B) (HB': NoDupAtt B'): A =va= A' ->
B =va= B' ->
vatts_union A B =va= vatts_union A' B'. 
Proof. intros H1 H2.
unfold equiv_vatts in H1.
unfold equiv_vatts in H2.
unfold equiv_vatts. intro c.
repeat(rewrite configVAttSet_dist_vatts_union).
apply set_union_equiv. all: try(assumption);
try (apply (NoDupAtt_NoDup_config); assumption).
apply H1. apply H2. Qed.

Lemma vqtype_union_vq_equiv A A' B B' (HA: NoDupAtt (fst A)) 
(HA': NoDupAtt (fst A'))
(HB: NoDupAtt (fst B)) (HB': NoDupAtt (fst B')): A =T= A' ->
B =T= B' ->
vqtype_union_vq A B =T= vqtype_union_vq A' B'. 
Proof. intros HAt HBt. 
unfold equiv_vqtype in HAt. 
unfold equiv_vqtype in HBt. 
unfold equiv_vqtype. intro c. specialize HAt with c.
specialize HBt with c. destruct A as (A, ea).
destruct B as (B, eb). destruct A' as (A', ea').
destruct B' as (B', eb'). simpl in *.
unfold vqtype_union_vq. 
simpl. destruct (E[[ea]]c) eqn:Hea; destruct (E[[ea']]c) eqn:Hea';
destruct (E[[eb]]c) eqn:Heb; destruct (E[[eb']]c) eqn:Heb';
simpl; try (
repeat(rewrite configVAttSet_dist_vatts_union);
try (apply NoDupAtt_push_annot; assumption); simpl;
repeat (rewrite configVAttSet_push_annot); simpl;
try (rewrite Hea); try (rewrite Hea'); try (rewrite Heb);
try (rewrite Heb');
try (apply set_union_equiv; try (apply NoDupAtt_NoDup_config;
assumption); try (apply NoDup_nil);
try assumption) ; try reflexivity); 

[ rewrite set_union_equiv with (B:=[]) (B':=[])
| rewrite atts_union_nil_r 
| rewrite set_union_equiv with (B:=[]) (B':=[])
| rewrite atts_union_nil_r
| rewrite atts_union_nil_l
| rewrite atts_union_nil_l ]; 
try assumption;
try (symmetry; assumption);
try (apply NoDup_nil);try (apply NoDupAtt_NoDup_config;
assumption). 
all: simpl; reflexivity.

(*intros HAt HBt. 
unfold equiv_vqtype in HAt. destruct HAt.
unfold equiv_vqtype in HBt. destruct HBt. 
unfold equiv_vqtype, vqtype_union_vq.
simpl. split. apply vatts_union_equiv;
try (apply NoDupAtt_push_annot; assumption);
unfold equiv_vatts; intro c;
repeat (rewrite configVAttSet_push_annot); 
apply configVQtype_equiv; unfold equiv_vqtype;
eauto. unfold equivE; simpl; intro. rewrite H0, H2.
reflexivity.*) Qed.

Lemma In_push_annot_In a e e' A {HndpAttA : NoDupAtt A} : 
In (ae a (e /\(F) e')) (A < e') <-> In (ae a e) A.
Proof. split;
    intro HInA;
    induction A as [|(aI, eI) A IHA]; simpl in HInA. 
    1, 3: destruct HInA.
    1, 2: destruct HInA as [HeqA | HInA].
    1, 3: inversion HeqA; subst; simpl; left; eauto.
    1, 2: inversion HndpAttA; subst; simpl; right; eauto.
Qed.    

Lemma removeAtt_push_annot a2 A1 e: removeAtt a2 (A1 < e) =va= ((removeAtt a2 A1) < e).
Proof. induction A1. simpl. reflexivity.
destruct a. simpl. destruct (string_beq a2 a) eqn:Ha2a.
apply IHA1; auto. unfold "=va=". intro c. simpl. 
destruct ((E[[ f]] c) && (E[[ e]] c)); [apply cons_equiv_atts|];
apply IHA1. Qed.

Lemma extract_e_push_annot a A e c: 
(E[[ extract_e a (A < e)]] c) = (E[[ extract_e a A /\(F) e]] c).
Proof. induction A as [|(a', e')]. eauto. 
simpl. destruct (string_eq_dec a a'); subst. Search extract_e.
  + repeat(rewrite simpl_extract_eq). simpl. rewrite IHA. simpl.
    rewrite andb_orb_distrib_l. reflexivity.
  + repeat(rewrite (simpl_extract_neq _ _ n)). apply IHA.
Qed. 

Hint Constructors NoDupAtt:core.

Lemma vatts_union_push_annot A1 A2 e {HndpAttA1:NoDupAtt A1} {HndpAttA2:NoDupAtt A2}: 
vatts_union  (A1 < e) (A2 < e) =va= ((vatts_union A1 A2) < e).
Proof. generalize dependent A1.

induction A2 as [| (a2, e2) A2 IHA2]; intros. simpl. 
unfold "=va=". intro c. simpl. repeat(rewrite vatts_union_nil_r;
try assumption; try eauto). 
reflexivity.

(* Case A2 := [ae a2 e2 :: A2] *)
simpl push_annot. 
inversion HndpAttA2 as [| a2' e2' A2' HnInAttA2 HndpAttA2']; subst.
destruct (in_dec vatt_eq_dec (ae a2 (e2 /\(F) e)) (A1 < e)) as [HInA1 | HnInA1].
  + (* In (ae a2 e2) A1 *)
    rewrite vatts_union_InA with (B:=(A2 < e)); try auto.
    rewrite IHA2; try auto. apply push_annot_equiv.
    rewrite vatts_union_InA with (B:=A2); try auto.
    reflexivity. Search push_annot.

    apply In_push_annot_In with (e':=e); eauto.

  + (* ~ In (ae a2 e2) A1 *)
     destruct (existsbAtt a2 (A1 < e)) eqn:HexstAttA1;
     remember (vatts_union A1 (ae a2 e2 :: A2)) as vattsunion;
         assert (Hrewrite: vattsunion =va= (vatts_union A1 (ae a2 e2 :: A2))) by 
          (rewrite Heqvattsunion; reflexivity).
     ++ (* InAtt a2 A1 *) 
         existsbAtt_InAtt in HexstAttA1. rename HexstAttA1 into HInAttA1.
         rewrite (vatts_union_nInA_InAttA); try auto.
         generalize removeAtt_push_annot; intros H.
         specialize H with a2 A1 e.
         generalize vatts_union_equiv; intros H0.
         specialize H0 with (removeAtt a2 (A1 < e)) (removeAtt a2 A1 < e) (A2 < e) (A2 < e).
         apply H0 in H; try (apply NoDupAtt_push_annot; auto); try reflexivity. clear H0.
         rewrite (cons_equiv_vatts) with (l2:=vatts_union (removeAtt a2 A1 < e) (A2 < e)); try assumption.
         rewrite (cons_equiv_vatts) with (l2:=vatts_union (removeAtt a2 A1) A2 < e); try (apply IHA2; eauto).
         clear H.

         
         rewrite (vatts_union_nInA_InAttA) in Hrewrite; try auto. 
         apply push_annot_equiv with (e:=e) in Hrewrite. rewrite Hrewrite. clear Hrewrite.
         
         apply notInAtt_push_annot with (e:=e) in HnInAttA2 as HnInAttA2_psh.
         unfold "=va=". intro c. simpl. repeat (rewrite notInAttA'_extract_set_union; try auto).
         
         rewrite extract_e_push_annot. simpl.
         rewrite andb_orb_distrib_l. reflexivity.

         split. rewrite <- In_push_annot_In; try auto. apply HnInA1. 
         apply Classical_Prop.NNPP.
         
         apply (contrapositive_iff _ _ (notInAtt_push_annot a2 A1 e)). apply PNNP. assumption.

         eauto. apply NoDupAtt_cons; [apply notInAtt_push_annot|]; eauto. 
         
     ++ (* ~ InAtt a2 A1 *)  not_existsbAtt_InAtt in HexstAttA1. 
        rename HexstAttA1 into HnInAttA1.
        rewrite (vatts_union_nInA_nInAttA); try auto. 

        rewrite (vatts_union_nInA_nInAttA) in Hrewrite; try auto. 
        apply push_annot_equiv with (e:=e) in Hrewrite. rewrite Hrewrite. clear Hrewrite.
        
        rewrite (cons_equiv_vatts) with (l2:= (vatts_union A1 A2 < e)); try (apply IHA2; eauto).
        unfold "=va=". intro c. simpl. reflexivity.

        split. rewrite <- In_push_annot_In; try auto. apply HnInA1. Search push_annot.
        rewrite notInAtt_push_annot. apply HnInAttA1.

        apply NoDupAtt_cons; [apply notInAtt_push_annot|]; eauto.
        

Qed.


Lemma push_annot_andf_equiv A e e': (A < (e /\(F) e')) =va= ((A < e) < e').
Proof. unfold "=va=". intro c. Search push_annot.
repeat (rewrite configVAttSet_push_annot).
simpl.  rewrite configVAttSet_push_annot. simpl.
destruct (E[[ e]] c); destruct (E[[ e']] c);
simpl; reflexivity. Qed.




