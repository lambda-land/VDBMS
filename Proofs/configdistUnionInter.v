(** Variational relational algebra lemmas *)
Set Warnings "-notation-overridden,-parsing".

Load SetOPLemmas.


Ltac intro_nodupelemconfig_rewrite H:= 
apply (nodupelem_equiv) in H;
unfold equiv_velems in H;
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
try (apply notIn_set_add_equiv_velems in Htemp);
try (apply notIn_set_add_equiv_elems in Htemp).

Ltac set_add_to_cons H1 H2 a' c A A':=
(* ~ InElem a' A' -> ~ In a' [[A']]c -  H1*)
apply notInElem_notIn_config with (c:=c) in H1 as H1';
(* ~ InElem a' (removeElem a' A) -> ~ In a' [[removeElem a' A]]c - H2 *)
apply notInElem_notIn_config with (c:=c) in H2 as H2';
(* combine H1 and H2 with and *)
pose (conj H1' H2') as Hsetadd_cons;
(* combine H1 and H2 with union: ~ In a' ([[A]]c U [[removeElem a' A]]c) *)
rewrite (notIn_set_union string_eq_dec _ _ _) in Hsetadd_cons;
(* ~ In a A -> set_add a A = a:: A *)
apply notIn_set_add_equiv_elems in Hsetadd_cons;
clear H1'; clear H2'.

Ltac NoDupElemAA'_NoDupAcUAc' HA HA' c :=
pose (NoDupElem_NoDup_config c HA) as HAtemp;
pose (NoDupElem_NoDup_config c HA') as HA'temp; 
pose (set_union_nodup string_eq_dec HAtemp HA'temp) as HNDpUcAA'.

Lemma set_remove_dist_set_union_elems: forall a A A' (HA: NoDup A) (HA': NoDup A'), 
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
       apply cons_equiv_elems. 
       apply (IHA'). all: assumption.
   ++ pose (set_union_nodup string_eq_dec HA HNdpA')
      as HNdpU. apply (set_add_nodup string_eq_dec a0) in HNdpU.
      assumption.
   ++ apply NoDup_cons. pose (conj HnInA HnInA') as HnInU.
      rewrite (notIn_set_union string_eq_dec a0 A A') in HnInU.
      assumption. pose (set_union_nodup string_eq_dec HA HNdpA')
      as HNdpU. assumption.
Qed.

(* -- removeElem set_union -- *)
Lemma removeElem_dist_set_union_velems : forall a A A', 
removeElem a (set_union velem_eq_dec A A') =va= 
set_union velem_eq_dec (removeElem a A) (removeElem a A').
Proof. intros a A. generalize dependent A. induction A'. 
- intro. simpl. reflexivity. 
- intros. simpl set_union at 1. 
  destruct a0 as (a0, e0). destruct (in_dec velem_eq_dec (ae a0 e0) A'). 
-- rename i into HInA'. 
    In_to_InunionA' HInA' (ae a0 e0) A A' velem_eq_dec. 
    rewrite Htemp.  clear Htemp. simpl.
    destruct (string_beq a a0) eqn:Haa0.
    ++ apply (IHA').
    ++ simpl set_union. apply In_removeElem with (a:=a) in HInA'
       as HInrmvA'. 
       In_to_InunionA' HInrmvA' (ae a0 e0) (removeElem a A) (removeElem a A') velem_eq_dec. 
       rewrite Htemp. apply (IHA'). rewrite <- stringBEF.eqb_neq.
       assumption.
-- rename n into HnInA'.
  destruct (in_dec velem_eq_dec (ae a0 e0) A). 
  + rename i into HInA. 
    In_to_Inunion HInA (ae a0 e0) A A' velem_eq_dec. 
    rewrite Htemp.  clear Htemp. simpl.
    destruct (string_beq a a0) eqn:Haa0.
    ++ apply (IHA').
    ++ simpl set_union. apply In_removeElem with (a:=a) in HInA
       as HInrmvA. 
       In_to_Inunion HInrmvA (ae a0 e0) (removeElem a A) (removeElem a A') velem_eq_dec. 
       rewrite Htemp. apply (IHA'). rewrite <- stringBEF.eqb_neq.
       assumption.
  + rename n into HnInA.
    notIn_to_notInunion HnInA HnInA' (ae a0 e0) A A' velem_eq_dec.
    rewrite (removeElem_equiv _ Htemp). clear Htemp.
    simpl.
    destruct (string_beq a a0) eqn:Haa0.
    ++ apply (IHA').
    ++ simpl set_union. apply notIn_notInremoveElem with (a:=a) in HnInA
       as HnInrmvA. apply notIn_notInremoveElem with (a:=a) in HnInA'
       as HnInrmvA'.  
       notIn_to_notInunion HnInrmvA HnInrmvA' (ae a0 e0) 
       (removeElem a A) (removeElem a A') velem_eq_dec.
       rewrite Htemp.
       apply cons_equiv_velems. 
       apply (IHA').
Qed.

(*Lemma velems_union_cases A b eb B : NoDupElem (ae b eb::B) -> 
(  In (ae b eb) A -> velems_union A (ae b eb::B) =va= velems_union A B ) \/
(~ In (ae b eb) A -> 
   (  InElem b A -> velems_union A (ae b eb::B) =va= 
                   ( ae b (eb \/(F) (extract_e b A)) ::
                           velems_union (removeElem b A) B ) ) \/
   ( ~InElem b A ->  )
).

*)

(* ---------- velems_union case analysis lemmas -------------  *)

Lemma velems_union_InA A b eb B : 
In (ae b eb) A -> velems_union A (ae b eb::B) =va= velems_union A B .

Proof.
intro HInA.
In_to_Inunion HInA (ae b eb) A B velem_eq_dec.
apply eq_equiv_velems in Htemp. 
apply nodupelem_equiv in Htemp. (* intro_nodupelemconfig_rewrite Htemp. *)
auto.
Qed.

Lemma velems_union_nInA_InElemA A b eb B {HndpElemA: NoDupElem A}
{HndpElembB: NoDupElem (ae b eb::B)} : 
~ In (ae b eb) A /\ InElem b A -> 
   velems_union A (ae b eb::B) =va= ( ae b (eb \/(F) extract_e b (set_union velem_eq_dec A B)) 
                                   :: velems_union (removeElem b A) B ).
Proof.
(* derive ~ In (ae b eb) B *)
apply NoDupElem_NoDup in HndpElembB as HndpbB.
inversion HndpbB as [|b' eb' HnInB HndpB]; subst.

intros H. destruct H as [HnInA HInElemA].

(* HInElemA: InElem b A -> InElem b (set_union _ A B) *)
assert(HInElemAUB: InElem b (set_union velem_eq_dec A B)).
rewrite InElem_set_union. eauto.
 
notIn_to_notInunion HnInA HnInB (ae b eb) A B velem_eq_dec.
apply nodupelem_equiv in Htemp. (* intro_nodupelemconfig_rewrite Htemp. *)
rewrite Htemp. 

simpl_nodupelem.
InElem_existsbElem in HInElemAUB. rewrite HInElemAUB.
existsbElem_InElem in HInElemAUB. simpl.

(* derive ~InElem b B *)
inversion HndpElembB as [|b' eb' B' HnInElemB HndpElemB]; subst.
(*unfold equiv_velems. simpl. intro c.*)

apply cons_equiv_velems.
(* 
~ InElem b B
----------------------------------------------------
nodupelem (removeElem b (set_union velem_eq_dec A B)) 
*)
pose (nodupelem_equiv
   (removeElem_dist_set_union_velems b A B)) as Hndprmv.

rewrite Hndprmv.
rewrite (notInElem_removeElem_eq B b HnInElemB).
(* 
~ InElem b B
----------------------------------------------------
 nodupelem (set_union velem_eq_dec (removeElem b A) B)
*)
reflexivity.
Qed.

Lemma velems_union_nInA_nInElemA A b eb B {HndpElembB: NoDupElem (ae b eb::B)} : 
~ In (ae b eb) A /\ ~ InElem b A -> 
   velems_union A (ae b eb::B) =va= 
                   ( ae b eb :: velems_union A B ).
Proof.
(* derive ~ In (ae b eb) B *)
apply NoDupElem_NoDup in HndpElembB as HndpbB.
inversion HndpbB as [|b' eb' HnInB HndpB]; subst.

(* derive ~InElem b B *)
inversion HndpElembB as [|b' eb' B' HnInElemB HndpElemB]; subst.

intros H. destruct H as [HnInA HnInElemA].

(* HInElemA: InElem b A -> InElem b (set_union _ A B) *)
assert(HInElemAUB: ~InElem b (set_union velem_eq_dec A B)).
rewrite <- notInElem_set_union. eauto.
 
notIn_to_notInunion HnInA HnInB (ae b eb) A B velem_eq_dec.
apply nodupelem_equiv in Htemp. (* intro_nodupelemconfig_rewrite Htemp. *)
rewrite Htemp. 

simpl_nodupelem.
InElem_existsbElem in HInElemAUB. rewrite not_true_iff_false in HInElemAUB.
rewrite HInElemAUB.
simpl.

apply cons_equiv_velems. reflexivity.
Qed.

(* destruct (in_dec velem_eq_dec (ae a' e') A) as [HInA | HnInA].
  + (* In (ae a' e') A *)
    apply velems_union_InA with (B:=A') in HInA as Hequiv.

  + (* ~ In (ae a' e') A *)
     destruct (existsbElem a' A) eqn:HexstElemA.
     ++ (* InElem a' A *) existsbElem_InElem in HexstElemA. 
         rename HexstElemA into HInElemA.
         rewrite (velems_union_nInA_InElemA) with (A:=A).

     ++ (* ~ InElem a' A *)  not_existsbElem_InElem in HexstElemA. 
        rename HexstElemA into HnInElemA.
        rewrite (velems_union_nInA_nInElemA) with (A:=A).
*)
(* ------------------------------case analysis -------------------------*)

Lemma velems_union_nInElemA_nInElemB b A B eb c: 
~ InElem b A -> ~ InElem b B ->
(A[[ velems_union A B]] c) =a= elems_union (A[[ A]] c) (A[[ B]] c) ->
(A[[ ae b eb :: velems_union A B]] c) =a= 
                      elems_union (A[[ A]] c) (A[[ ae b eb :: B]] c).
Proof. intros HnInElemA HnInElemB H.
simpl. destruct (E[[ eb]] c) eqn:Heb.
+++ simpl elems_union. unfold elems_union.
    set_add_to_cons HnInElemA HnInElemB b c A B.
    rewrite Hsetadd_cons; clear Hsetadd_cons.
    apply cons_equiv_elems. 
    unfold elems_union in H. apply H; assumption.
+++ apply H; try assumption.
Qed.
  

Lemma In_set_union_removeElem a' A A' c (HNdpElemA: NoDupElem A)
(HNdpElemA': NoDupElem A'):  In a' (A[[ A]] c) -> ~InElem a' A' ->
       set_union string_eq_dec (A[[ A]] c)              (A[[ A']] c) =a= 
(a' :: set_union string_eq_dec (A[[ removeElem a' A]] c) (A[[ A']] c)).
Proof. 
intros HInA HnInElemA'.
apply (set_union_intro1 string_eq_dec) with (y:= (configVElemSet A' c)) in HInA.
unfold set_In in HInA.
      
(* HNDpUcAA': NoDup (elems_union (A[[ A]] c) (A[[ A']] c)) *)   
NoDupElemAA'_NoDupAcUAc' HNdpElemA HNdpElemA' c.

(* set add a (set remove a A) =a= A *)
rewrite <- (In_set_add_remove a' HNDpUcAA' HInA).
       
(* NoDupElem -> NoDup A[[ ]] c *)
apply NoDupElem_NoDup_config with (c:=c) in HNdpElemA as HNdpCA.
apply NoDupElem_NoDup_config with (c:=c) in HNdpElemA' as HNdpCA'.

(* set_remove a (set_union A B) =a= set_union (set_remove a A) (set_remove a B) *)
rewrite (set_add_equiv _
           (set_remove_dist_set_union_elems _ HNdpCA HNdpCA')); try assumption.

(*set_remove a A[[ A]] c =a= A[[set_remove a A ]] c *)
repeat (rewrite set_remove_config; try assumption).

(* ~InElem a' A -> removeElem a' A =a= A *)
rewrite (notInElem_removeElem_eq A' a' HnInElemA').
          
(* intro HInremA: ~ InElem a' (removeElem a' A) *)
pose (notInElem_removeElem A a') as HInremA.

(* ~ In a A -> set_add a A =a= a::A *)
set_add_to_cons HInremA HnInElemA' a' c A A'.
rewrite Hsetadd_cons.  

reflexivity.

Qed.

Lemma notInElem_set_union_removeElem a' A A' c (HNdpElemA: NoDupElem A)
(HNdpElemA': NoDupElem A'): 
~ In a' (A[[ A]] c) -> ~InElem a' A' ->
set_union string_eq_dec (A[[ A]] c)              (A[[ A']] c) =a= 
set_union string_eq_dec (A[[ removeElem a' A]] c) (A[[ A']] c).
Proof. 
intros HnInA HnInElemA'.
pose (conj HnInA (notInElem_notIn_config a' A' c HnInElemA')) as HnInU.
rewrite (notIn_set_union string_eq_dec) in HnInU.
           
rewrite <- (notIn_set_remove_eq string_eq_dec _ _ HnInU).

apply NoDupElem_NoDup_config with (c:=c) in HNdpElemA as HNdpCA.
apply NoDupElem_NoDup_config with (c:=c) in HNdpElemA' as HNdpCA'.

rewrite (set_remove_dist_set_union_elems _ HNdpCA HNdpCA').
repeat (rewrite set_remove_config; try assumption).
           
rewrite (notInElem_removeElem_eq A' a' HnInElemA').

reflexivity.
Qed.

Lemma notInElemA'_set_union_cons_removeElem a' A' A c (HNdpElemA: NoDupElem A) (HNdpElemA': NoDupElem A'):
 ~ InElem a' A' -> 
       set_union string_eq_dec (A[[ A]] c)              (a' :: (A[[ A']] c)) =a= 
(a' :: set_union string_eq_dec (A[[ removeElem a' A]] c)        (A[[ A']] c)) .
Proof.  intro HnInElemA'. 

(* derive Nodup NoDup (elems_union (A[[ A]] c) (A[[ A']] c)) *) 
NoDupElemAA'_NoDupAcUAc' HNdpElemA HNdpElemA' c.

simpl set_union.
rewrite set_add_remove; try assumption.
 
apply NoDupElem_NoDup_config with (c:=c) in HNdpElemA as HNdpCA.
apply NoDupElem_NoDup_config with (c:=c) in HNdpElemA' as HNdpCA'.

rewrite (set_add_equiv _
           (set_remove_dist_set_union_elems _ HNdpCA HNdpCA')).

repeat (rewrite set_remove_config; try assumption).
(* removeElem a' A' = A' as ~ InElem a' A' *)
rewrite (notInElem_removeElem_eq A' a' HnInElemA').
(* intro HInremA: ~ InElem a' (removeElem a' A) *)
pose (notInElem_removeElem A a') as HInremA.
         
set_add_to_cons HInremA HnInElemA' a' c A A'.
           
rewrite Hsetadd_cons. reflexivity.
Qed.

Hint Resolve NoDupElem_removeElem : core.

Lemma notInElemA'_extract_set_union:
  forall (a : elem) [A A' : list velem] (c : config),
  NoDupElem A ->
  NoDupElem A' ->
  ~ InElem a A' ->
  (E[[ extract_e a (set_union velem_eq_dec A A')]] c) =
  (E[[ extract_e a A]] c).
Proof. intros a A A' c HndpElemA HndpElemA' HnInElemA'. 
rewrite (extract_set_union _ _ HndpElemA HndpElemA').
rewrite (notInElem_extract _ _ HnInElemA'). simpl.
rewrite orb_false_r. reflexivity. Qed.
       

Theorem velems_union_is_variation_preserving : forall A  A' c (HA: NoDupElem A)
(HA': NoDupElem A'), 
    A[[ velems_union A A']]c =a= elems_union (A[[ A]] c) (A[[ A']] c).
Proof. intros A A'. generalize dependent A. induction A' as [|a' A' IHA'].
- (* case A' = [] *)
  (*
     -----------------------------------------------
     A[[ velems_union A []]] c =a= elems_union (A[[ A]] c) []
  *)
  destruct A as [| a A]; intros. 
  + (* case A = []       *) simpl. reflexivity.
  + (* case A = (a :: A) *) simpl (A[[ _]] _) at 3.
    (* forall X, velems_union X [] =va= [] /\ forall x, elems_union x [] =a= [] *)
    rewrite velems_union_nil_r, elems_union_nil_r. 
    reflexivity. assumption.
    
- (* case A' = (a :: A') *)
  intros A c Ha Ha'. destruct a' as (a', e').
  (* IHA' : A[[ velems_union A A']] c =a= elems_union (A[[ A]] c) (A[[ A']] c)
     Ha'  : NoDupElem (ae a' e' :: A')
     .........
     -----------------------------------------------
     A[[ velems_union A (ae a' e' :: A')]] c =a= elems_union (A[[ A]] c) (A[[ ae a' e' :: A']] c)
  *)
  
  (* inversion NoDupElem (ae a' e' :: A') -> ~ InElem a' A' *)
  inversion Ha' as [| a'' e'' A'' HnInElemA' HNdpElemA']; subst.
  simpl set_union. 
  
  (* introduce ~ In (ae a' e') A' from NoDupElem_NoDup lemma *)
  pose (NoDupElem_NoDup Ha') as Hndp.
  inversion Hndp as [|a'' e'' HnInA' HNDpA']; subst. clear Hndp.
  
  (* IHA' : A[[ velems_union A A']] c =a= elems_union (A[[ A]] c) (A[[ A']] c)
     HnInA' : ~ In (ae a' e') A'
     HnInElemA' : ~ InElem a' A'
     .......
     -----------------------------------------------
     A[[ velems_union A (ae a' e' :: A')]] c =a= elems_union (A[[ A]] c) (A[[ ae a' e' :: A']] c)
  *)
  (** Prove by cases of In (ae a' e') A  *)
  destruct (in_dec velem_eq_dec (ae a' e') A) as [HInA | HnInA].
  + (* case In (ae a' e') A *)
    
    (* IHA' : A[[ velems_union A A']] c =a= elems_union (A[[ A]] c) (A[[ A']] c)
       HnInA' : ~ In (ae a' e') A'
       HnInElemA' : ~ InElem a' A'
       HInA : In (ae a' e') A  (* case analysis *)
       ........
       -----------------------------------------------
       A[[ velems_union A (ae a' e' :: A')]] c =a= elems_union (A[[ A]] c) (A[[ ae a' e' :: A']] c)
    *)
    
    (* HInA : In (ae a' e') A -> velems_union A (ae a' e' :: A') =va= velems_union A A' *)
    apply velems_union_InA with (B:=A') in HInA as Hequiv. 
    unfold "=va=" in Hequiv. rewrite Hequiv.
    (* .......
       -----------------------------------------------
       A[[ velems_union A A']] c =a= elems_union (A[[ A]] c) (A[[ ae a' e' :: A']] c)
    *)
    simpl. 
    (* .......
       -----------------------------------------------
       A[[ velems_union A A']] c =a= elems_union (A[[ A]] c) 
                                  (if E[[ e']] c then a' :: A[[ A']] c else A[[ A']] c)
    *)
    destruct (E[[ e']] c) eqn:He'.
    ++ (* case  (E[[ e']] c) = true *)
       (* HInA : In (ae a' e') A
          .......
          -----------------------------------------------
          A[[ velems_union A A']] c =a= elems_union (A[[ A]] c) (a' :: A[[ A']] c)
       *)
       simpl elems_union. unfold elems_union.
       unfold elems_union in IHA'.
       (* HInA : In (ae a' e') A
          .......
          -----------------------------------------------
          A[[ velems_union A A']] c =a= set_add string_eq_dec a' (elems_union (A[[ A]] c) (A[[ A']] c))
       *)
       (* HInA  : In (ae a' e') A -> HInA_c: In a' (A[[A]]c) *)
       pose (In_config_true a' e' A c HInA He') as HInA_c.
       (* HInA_c: In a' (A[[A]]c) -> In a' (elems_union (A[[ A]] c) (A[[ A']] c) *)
       apply (set_union_intro1 string_eq_dec) with (y:= (A[[ A']]c)) in HInA_c.
       (* HInA_c -> set_add string_eq_dec a' (elems_union (A[[ A]] c) (A[[ A']] c)) =
                                              elems_union (A[[ A]] c) (A[[ A']] c)  *)
       apply (In_set_add string_eq_dec) in HInA_c. rewrite HInA_c. clear HInA_c.
       
       (* IHA' : A[[ velems_union A A']] c =a= elems_union (A[[ A]] c) (A[[ A']] c)
          .......
          -----------------------------------------------
          A[[ velems_union A A']] c =a= elems_union (A[[ A]] c) (A[[ A']] c)
       *)
       apply IHA'; eauto.
        
    ++ (* case  (E[[ e']] c) = false *)
       apply IHA'; eauto.
       
  + (* case ~ In (ae a' e') A *)
  
     (* IHA' : A[[ velems_union A A']] c =a= elems_union (A[[ A]] c) (A[[ A']] c)
        HnInA' : ~ In (ae a' e') A'
        HnInElemA' : ~ InElem a' A'
        .......
        -----------------------------------------------
        A[[ velems_union A (ae a' e' :: A')]] c =a= elems_union (A[[ A]] c) (A[[ ae a' e' :: A']] c)
     *)
     (** Proof by cases of existsbElem a' A *)
     destruct (existsbElem a' A) eqn:HexstElemA.
     ++ (* case existsbElem a' A = true -> InElem a' A *) 
         existsbElem_InElem in HexstElemA. rename HexstElemA into HInElemA.
         (* HnInA : ~ In (ae a' e') A
            HInElemA : InElem a' A
            ........
            -----------------------------------------------
            A[[ velems_union A (ae a' e' :: A')]] c =a= elems_union (A[[ A]] c) (A[[ ae a' e' :: A']] c)
         *)
         (* From velems_union Defn, HnInA /\ HInElemA -> 
             velems_union A (ae a' e' :: A') =va= ae a' (e' \/(F) extract_e a' (velems_union A A')) 
                                                   :: velems_union (removeElem a' A) A' *)
         apply (velems_union_nInA_InElemA) with (A:=A) in Ha' as Hequiv;
         try( split; assumption); try assumption.
         unfold "=va=" in Hequiv. rewrite Hequiv.
         (* ........
            -----------------------------------------------
            A[[ ae a' (e' \/(F) extract_e a' (set_union velem_eq_dec A A')) 
                                   :: velems_union (removeElem a' A) A']] c 
            =a= elems_union (A[[ A]] c) (A[[ ae a' e' :: A']] c)
         *)
         simpl. 
         (* ........
            -----------------------------------------------
           (if (E[[ e']] c) || (E[[ extract_e a' (set_union velem_eq_dec A A')]] c)
             then a' :: A[[ velems_union (removeElem a' A) A']] c
              else A[[ velems_union (removeElem a' A) A']] c) =a= elems_union 
                 (A[[ A]] c)
                    (if E[[ e']] c then a' :: A[[ A']] c else A[[ A']] c)
         *)
         (** Prove by cases (E[[ e']] c) *)
         destruct (E[[ e']] c) eqn:He'. 
         +++ (* (E[[ e']] c) = true *) 
             
             rewrite orb_true_l.
             (* HnInElemA' : ~ InElem a' A'
                .........
                -----------------------------------------------
                a' :: A[[ velems_union (removeElem a' A) A']] c 
                       =a= elems_union (A[[ A]] c) (a' :: A[[ A']] c)
             *)
             (* HnInElemA' : ~ InElem a' A' -> elems_union (A[[ A]] c) (a' :: A[[ A']] c)
                    =a= a' :: elems_union (A[[ removeElem a' A]] c) (A[[ A']] c) *)
             rewrite (notInElemA'_set_union_cons_removeElem _ c Ha HNdpElemA' HnInElemA').
             apply cons_equiv_elems. 
             
             (* IHA': A[[ velems_union A A']] c =a= elems_union (A[[ A]] c) (A[[ A']] c)
                ..........
                -----------------------------------------------
                a' :: A[[ velems_union (removeElem a' A) A']] c 
                       =a= a' :: elems_union (A[[ removeElem a' A]] c) (A[[ A']] c)
             *)
             apply IHA'; eauto.
         
         +++ (* (E[[ e']] c) = false *) 
             rewrite orb_false_l.
             
             (* HnInElemA' : ~ InElem a' A'
                .........
                -----------------------------------------------
                (if E[[ extract_e a' (set_union velem_eq_dec A A')]] c
                  then a' :: A[[ velems_union (removeElem a' A) A']] c
                   else A[[ velems_union (removeElem a' A) A']] c) =a= elems_union (A[[ A]] c) (A[[ A']] c)
             *) 
             
             (* ~ InElem a' A'-> E[[ extract_e a' (set_union velem_eq_dec A A')]]c = 
                                E[[ extract_e a' A]]c *)
             rewrite notInElemA'_extract_set_union; try assumption.
             apply InElem_extract in HInElemA as HInAexe; try assumption.
             destruct HInAexe as [e [HInA Hexeqe] ].
             
             (* .........
                -----------------------------------------------
                (if E[[ extract_e a' A]] c
                  then a' :: A[[ velems_union (removeElem a' A) A']] c
                   else A[[ velems_union (removeElem a' A) A']] c) =a= elems_union (A[[ A]] c) (A[[ A']] c)
             *) 
             
             (** Prove by cases (E[[ extract_e a' A]] c) *)
             destruct (E[[ extract_e a' A]] c) eqn: Hexta'.

             ++++ (* E[[ extract_e a' A]]c = true *)

                  (* E[[ extract_e a' A]]c = true -> E[[e]]c = true *)
                  rewrite Hexeqe in Hexta'. simpl in Hexta'.
                  rewrite orb_false_r in Hexta'.

                  (* E[[e]]c = true /\ In (ae a e) A -> In a A[[A]]c *)
                   apply In_config_true with (c:=c) in HInA; try assumption.
              
                  (* In a A[[A]]c -> elems_union (A[[ A]] c) (A[[ A']] c) =a= 
                                    (a' :: elems_union (A[[ removeElem a' A]] c) (A[[ A']] c)) *)
                   rewrite (In_set_union_removeElem _ c Ha HNdpElemA' HInA HnInElemA').
                   apply cons_equiv_elems. 
                   
                   apply IHA'; eauto.

             ++++ (* E[[ extract_e a' A]]c = false *)
          
                  (* E[[ extract_e a' A]]c = false -> E[[e]]c = false *)
                  rewrite Hexeqe in Hexta'. simpl in Hexta'.
                  rewrite orb_false_r in Hexta'.
                  
                  (*  E[[e]]c = false /\ In (ae a e) A -> ~ In a A[[[A]]c *)
                  apply In_config_false with (c:=c) in HInA; try assumption.
                  
                  (* ~ In a A[[A]]c -> elems_union (A[[ A]] c) (A[[ A']] c) =a= 
                                       elems_union (A[[ removeElem a' A]] c) (A[[ A']] c) *)
                  rewrite (notInElem_set_union_removeElem _ c Ha HNdpElemA' HInA HnInElemA').
              
                  apply IHA'; eauto.

     ++ (* case existsbElem a' A = false -> ~ InElem a' A *)  
        not_existsbElem_InElem in HexstElemA. 
        rename HexstElemA into HnInElemA.
        
        (*  HnInA    : ~ In (ae a' e') A
            HnInElemA : ~ InElem a' A
            ........
            -----------------------------------------------
            A[[ velems_union A (ae a' e' :: A')]] c =a= elems_union (A[[ A]] c) (A[[ ae a' e' :: A']] c)
        *)
        (* HnInA /\ HnInElemA ->
              velems_union A (ae a' e' :: A') =va= ae a' e' :: velems_union A A' *)
        apply (velems_union_nInA_nInElemA) with (A:=A) in Ha' as Hequiv;
        try(split; assumption).
        unfold "=va=" in Hequiv. rewrite Hequiv.
        (*  HnInElemA' : ~ InElem a' A'
            HnInElemA  : ~ InElem a' A
            ..............
            -----------------------------------------------
            A[[ ae a' e' :: velems_union A A']] c =a= elems_union (A[[ A]] c) (A[[ ae a' e' :: A']] c)
        *)
        (* Goal -> HnInElemA' /\ HnInElemA /\ IHA'  *)
        apply velems_union_nInElemA_nInElemB; eauto.

Qed.

Lemma configVElemSet_dist_velems_union : forall A  A' c (HA: NoDupElem A)
(HA': NoDupElem A'), configVElemSet (velems_union A A') c =a=
      elems_union (configVElemSet A c) (configVElemSet A' c) .
Proof. apply velems_union_is_variation_preserving. Qed.


Lemma configVQType_dist_vqtype_union_vq : forall Q Q' c (HA: NoDupElem (fst Q))
(HA': NoDupElem (fst Q')), configVQtype (vqtype_union_vq Q Q') c
=a= elems_union (configVQtype Q c) (configVQtype Q' c).
Proof. 
intros Q Q' c HQ HQ'. destruct Q as (A, e). destruct Q' as (A', e').
unfold vqtype_union_vq, configVQtype, configaVelems. simpl fst. simpl snd. 
simpl. 
destruct (E[[ e]] c) eqn: He; simpl; [|
destruct (E[[ e']] c) eqn: He'; simpl; [ | (* [] =a= [] *)simpl; reflexivity] ]; 

rewrite configVElemSet_dist_velems_union; 
try (apply NoDupElem_push_annot; auto); simpl;
repeat(rewrite configVElemSet_push_annot); simpl;
rewrite He; [|rewrite He']; reflexivity. 

Qed.

(*Lemma configVQType_dist_velems_union : forall A A' e c (HA: NoDupElem A)
(HA': NoDupElem A'), configVQtype (velems_union A A', e) c
=a= elems_union (configVQtype (A, e) c) (configVQtype (A', e) c).
Proof. 
intros A A' e c. unfold configVQtype, configaVelems.
destruct (E[[ e]] c) eqn: He.
apply configVElemSet_dist_velems_union.
intros. simpl. reflexivity.
Qed.*)

Theorem velems_intersection_is_variation_preserving : forall A  A' c (HA: NoDupElem A)
(HA': NoDupElem A'), A[[ velems_inter A A']] c =
      elems_inter (A[[ A]] c) (A[[ A']] c).
Proof. intros. induction A as [|a A IHA].
- (* case A = [] *) simpl. reflexivity.
- (* case A = (a::A) *) 
   simpl.  destruct a as (a, e). 
   (* get (~ InElemA a A) from NoDupElem (ae a e :: A) *)
   inversion HA as [| a'' e'' A'' HnInElemA HNdpElemA]; subst.
   (* rewrite velems_inter equation*)
   rewrite velems_inter_equation. 
   (** Proof by cases of (E[[ e]]c) *)
   destruct (E[[ e]]c) eqn:He.
   { (* case He: (E[[e]]c) = true *)
      simpl elems_inter.
     (** Proof by cases of (set_mem _ a (A[[ A']] c)) *)
     destruct (set_mem string_eq_dec a (A[[ A']] c)) eqn: Hset_memaA'.
    + (* case (set_mem _ a (A[[ A']] c) = true *)
      (* set_mem _ a (A[[ A']] c) = true -> In a (A[[ A']] c) *)
      apply (set_mem_correct1 string_eq_dec) in Hset_memaA'.
      (* In a (A[[ A']] c) -> Hextract: E[[ extract_e a A']] c = true *) 
      apply extract_true_In in Hset_memaA' as Hextract.
      (* In a (A[[ A']] c) -> HInelemaA': InElem a A' *) 
      apply In_InElem_config in Hset_memaA' as HInelemaA'. 
      (* InElem a A' -> existsbElem a A' = true *)
      rewrite <- existsbElem_InElem in HInelemaA'. rewrite HInelemaA'.
      (* simpl A[[_]]c. rewrite He Hextract IHA *)
      simpl configVElemSet. rewrite He, Hextract, IHA. simpl. 
      reflexivity.  assumption.
    + (* case (set_mem _ a (A[[ A']] c) <> true *)
      (* set_mem _ a (A[[ A']] c) <> true -> ~ In a (A[[ A']] c) *)
      apply (set_mem_complete1 string_eq_dec) in Hset_memaA'. 
      (* ~ In a (A[[ A']] c) -> Hextract: E[[ extract_e a A']] c = false *) 
      rewrite <- extract_true_In in Hset_memaA'.
      (* rewrite <> true <-> = false in Hset_memaA' *) 
      rewrite not_true_iff_false in Hset_memaA'.
      (** Proof by cases of existsbElem a A' *)
      destruct (existsbElem a A'). 
      ++ (* existsbElem a A' = true *)
         (* simpl A[[_]]c. rewrite IHA Hset_memaA' *)
         simpl configVElemSet. rewrite IHA, Hset_memaA'. 
         rewrite andb_false_r. reflexivity. assumption. 
      ++ (* existsbElem a A' = false *) apply(IHA HNdpElemA). 
   }
   { (* case He: (E[[e]]c) = true *)
     (** Proof by cases of existsbElem a A' *)
     destruct (existsbElem a A'). 
     + (* existsbElem a A' = true *)
       (* simpl A[[_]]c. rewrite He IHA *)
       simpl configVElemSet. rewrite He, IHA. 
       rewrite andb_false_l. reflexivity. assumption. 
     + (* existsbElem a A' = false *) apply(IHA HNdpElemA). 
   }
Qed.

Lemma configVElemSet_dist_velems_inter : forall A  A' c (HA: NoDupElem A)
(HA': NoDupElem A'), configVElemSet (velems_inter A A') c =
      elems_inter (configVElemSet A c) (configVElemSet A' c).
Proof. apply velems_intersection_is_variation_preserving. Qed.

Lemma configVQType_dist_velems_inter : forall A A' e e' c 
(HA: NoDupElem A) (HA': NoDupElem A'), 
configVQtype (velems_inter (push_annot A e)
       (push_annot A' e'), e \/(F) e') c
= elems_inter (configVQtype (A, e) c) (configVQtype (A', e') c).
Proof. intros. unfold configVQtype. 
simpl. destruct (E[[ e]] c) eqn: He;
[rewrite orb_true_l | rewrite orb_false_l];
destruct (E[[ e']] c) eqn: He';
try(rewrite configVElemSet_dist_velems_inter);
try(repeat(rewrite configVElemSet_push_annot));
simpl; simpl configVQtype; try(rewrite He, He');
try(eauto).  
Qed. 

Lemma velems_inter_equiv A A' B B' (HA: NoDupElem A) (HA': NoDupElem A')
(HB: NoDupElem B) (HB': NoDupElem B'): A =va= A' ->
B =va= B' ->
velems_inter A B =va= velems_inter A' B'. 
Proof. intros H1 H2.
unfold equiv_velems in H1.
unfold equiv_velems in H2.
unfold equiv_velems. intro c.
repeat(rewrite configVElemSet_dist_velems_inter).
apply set_inter_equiv. all: try(assumption);
try (apply (NoDupElem_NoDup_config); assumption).
apply H1. apply H2. Qed.


Lemma vqtype_inter_vq_equiv A A' B B' (HA: NoDupElem (fst A)) 
(HA': NoDupElem (fst A'))
(HB: NoDupElem (fst B)) (HB': NoDupElem (fst B')): A =T= A' ->
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
simpl; repeat(rewrite configVElemSet_dist_velems_inter);
try(assumption); try reflexivity;
[ apply set_inter_equiv
| rewrite set_inter_equiv with (B:=(A[[ A]] c)) (B':=[])
| rewrite set_inter_equiv with (B:=(A[[ A']] c)) (B':=[])
| rewrite set_inter_equiv with (B:=[]) (B':=(A[[ B]] c))
| rewrite set_inter_equiv with (B:=[]) (B':=[])
| rewrite set_inter_equiv with (B:=[]) (B':=(A[[ B']] c))
| rewrite set_inter_equiv with (B:=[]) (B':=[])];

try reflexivity; try(assumption);
try (apply (NoDupElem_NoDup_config); assumption);
try (apply NoDup_nil).

rewrite elems_inter_nil_r. reflexivity.
rewrite elems_inter_nil_r. reflexivity.
all: symmetry; assumption.

(*intros HAt HBt. unfold equiv_vqtype in HAt. destruct HAt.
unfold equiv_vqtype in HBt. destruct HBt. 
unfold equiv_vqtype.
simpl. split. apply velems_inter_equiv. all :(try assumption).
unfold equivE. intro. simpl. rewrite H0, H2. reflexivity.*) Qed.

Lemma configVElemSet_velems_inter_nil_l A B c (HA: NoDupElem A) (HB: NoDupElem B): (A[[ A]] c) =a= [] ->
(A[[velems_inter A B]] c) =a= []. 
Proof. intro H. 
rewrite configVElemSet_dist_velems_inter.
apply elems_inter_nil_l_equiv.
1, 2: apply (NoDupElem_NoDup_config); assumption. 
all: eauto.
Qed.

Lemma configVElemSet_velems_inter_nil_r A B c (HA: NoDupElem A) (HB: NoDupElem B): (A[[ B]] c) =a= [] ->
(A[[velems_inter A B]] c) =a= []. 
Proof. intro H. 
rewrite configVElemSet_dist_velems_inter.
apply elems_inter_nil_r_equiv.
1, 2: apply (NoDupElem_NoDup_config); assumption. 
all: eauto.
Qed.


Lemma velems_union_equiv A A' B B' (HA: NoDupElem A) (HA': NoDupElem A')
(HB: NoDupElem B) (HB': NoDupElem B'): A =va= A' ->
B =va= B' ->
velems_union A B =va= velems_union A' B'. 
Proof. intros H1 H2.
unfold equiv_velems in H1.
unfold equiv_velems in H2.
unfold equiv_velems. intro c.
repeat(rewrite configVElemSet_dist_velems_union).
apply set_union_equiv. all: try(assumption);
try (apply (NoDupElem_NoDup_config); assumption).
apply H1. apply H2. Qed.

Lemma vqtype_union_vq_equiv A A' B B' (HA: NoDupElem (fst A)) 
(HA': NoDupElem (fst A'))
(HB: NoDupElem (fst B)) (HB': NoDupElem (fst B')): A =T= A' ->
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
repeat(rewrite configVElemSet_dist_velems_union);
try (apply NoDupElem_push_annot; assumption); simpl;
repeat (rewrite configVElemSet_push_annot); simpl;
try (rewrite Hea); try (rewrite Hea'); try (rewrite Heb);
try (rewrite Heb');
try (apply set_union_equiv; try (apply NoDupElem_NoDup_config;
assumption); try (apply NoDup_nil);
try assumption) ; try reflexivity); 

[ rewrite set_union_equiv with (B:=[]) (B':=[])
| rewrite elems_union_nil_r 
| rewrite set_union_equiv with (B:=[]) (B':=[])
| rewrite elems_union_nil_r
| rewrite elems_union_nil_l
| rewrite elems_union_nil_l ]; 
try assumption;
try (symmetry; assumption);
try (apply NoDup_nil);try (apply NoDupElem_NoDup_config;
assumption). 
all: simpl; reflexivity.

(*intros HAt HBt. 
unfold equiv_vqtype in HAt. destruct HAt.
unfold equiv_vqtype in HBt. destruct HBt. 
unfold equiv_vqtype, vqtype_union_vq.
simpl. split. apply velems_union_equiv;
try (apply NoDupElem_push_annot; assumption);
unfold equiv_velems; intro c;
repeat (rewrite configVElemSet_push_annot); 
apply configVQtype_equiv; unfold equiv_vqtype;
eauto. unfold equivE; simpl; intro. rewrite H0, H2.
reflexivity.*) Qed.

Lemma In_push_annot_In a e e' A {HndpElemA : NoDupElem A} : 
In (ae a (e /\(F) e')) (A < e') <-> In (ae a e) A.
Proof. split;
    intro HInA;
    induction A as [|(aI, eI) A IHA]; simpl in HInA. 
    1, 3: destruct HInA.
    1, 2: destruct HInA as [HeqA | HInA].
    1, 3: inversion HeqA; subst; simpl; left; eauto.
    1, 2: inversion HndpElemA; subst; simpl; right; eauto.
Qed.    

Lemma removeElem_push_annot a2 A1 e: removeElem a2 (A1 < e) =va= ((removeElem a2 A1) < e).
Proof. induction A1. simpl. reflexivity.
destruct a as (a,f). simpl. destruct (string_beq a2 a) eqn:Ha2a.
apply IHA1; auto. unfold "=va=". intro c. simpl. 
destruct ((E[[ f]] c) && (E[[ e]] c)); [apply cons_equiv_elems|];
apply IHA1. Qed.

Lemma extract_e_push_annot a A e c: 
(E[[ extract_e a (A < e)]] c) = (E[[ extract_e a A /\(F) e]] c).
Proof. induction A as [|(a', e')]. eauto. 
simpl. destruct (string_eq_dec a a'); subst. Search extract_e.
  + repeat(rewrite simpl_extract_eq). simpl. rewrite IHA. simpl.
    rewrite andb_orb_distrib_l. reflexivity.
  + repeat(rewrite (simpl_extract_neq _ _ n)). apply IHA.
Qed. 

Hint Constructors NoDupElem:core.

Lemma velems_union_push_annot A1 A2 e {HndpElemA1:NoDupElem A1} {HndpElemA2:NoDupElem A2}: 
velems_union  (A1 < e) (A2 < e) =va= ((velems_union A1 A2) < e).
Proof. generalize dependent A1.

induction A2 as [| (a2, e2) A2 IHA2]; intros. simpl. 
unfold "=va=". intro c. simpl. repeat(rewrite velems_union_nil_r;
try assumption; try eauto). 
reflexivity.

(* Case A2 := [ae a2 e2 :: A2] *)
simpl push_annot. 
inversion HndpElemA2 as [| a2' e2' A2' HnInElemA2 HndpElemA2']; subst.
destruct (in_dec velem_eq_dec (ae a2 (e2 /\(F) e)) (A1 < e)) as [HInA1 | HnInA1].
  + (* In (ae a2 e2) A1 *)
    rewrite velems_union_InA with (B:=(A2 < e)); try auto.
    rewrite IHA2; try auto. apply push_annot_equiv.
    rewrite velems_union_InA with (B:=A2); try auto.
    reflexivity. Search push_annot.

    apply In_push_annot_In with (e':=e); eauto.

  + (* ~ In (ae a2 e2) A1 *)
     destruct (existsbElem a2 (A1 < e)) eqn:HexstElemA1;
     remember (velems_union A1 (ae a2 e2 :: A2)) as velemsunion;
         assert (Hrewrite: velemsunion =va= (velems_union A1 (ae a2 e2 :: A2))) by 
          (rewrite Heqvelemsunion; reflexivity).
     ++ (* InElem a2 A1 *) 
         existsbElem_InElem in HexstElemA1. rename HexstElemA1 into HInElemA1.
         rewrite (velems_union_nInA_InElemA); try auto.
         generalize removeElem_push_annot; intros H.
         specialize H with a2 A1 e.
         generalize velems_union_equiv; intros H0.
         specialize H0 with (removeElem a2 (A1 < e)) (removeElem a2 A1 < e) (A2 < e) (A2 < e).
         apply H0 in H; try (apply NoDupElem_push_annot; auto); try reflexivity. clear H0.
         rewrite (cons_equiv_velems) with (l2:=velems_union (removeElem a2 A1 < e) (A2 < e)); try assumption.
         rewrite (cons_equiv_velems) with (l2:=velems_union (removeElem a2 A1) A2 < e); try (apply IHA2; eauto).
         clear H.

         
         rewrite (velems_union_nInA_InElemA) in Hrewrite; try auto. 
         apply push_annot_equiv with (e:=e) in Hrewrite. rewrite Hrewrite. clear Hrewrite.
         
         apply notInElem_push_annot with (e:=e) in HnInElemA2 as HnInElemA2_psh.
         unfold "=va=". intro c. simpl. repeat (rewrite notInElemA'_extract_set_union; try auto).
         
         rewrite extract_e_push_annot. simpl.
         rewrite andb_orb_distrib_l. reflexivity.

         split. rewrite <- In_push_annot_In; try auto. apply HnInA1. 
         apply Classical_Prop.NNPP.
         
         apply (contrapositive_iff _ _ (notInElem_push_annot a2 A1 e)). apply PNNP. assumption.

         eauto. apply NoDupElem_cons; [apply notInElem_push_annot|]; eauto. 
         
     ++ (* ~ InElem a2 A1 *)  not_existsbElem_InElem in HexstElemA1. 
        rename HexstElemA1 into HnInElemA1.
        rewrite (velems_union_nInA_nInElemA); try auto. 

        rewrite (velems_union_nInA_nInElemA) in Hrewrite; try auto. 
        apply push_annot_equiv with (e:=e) in Hrewrite. rewrite Hrewrite. clear Hrewrite.
        
        rewrite (cons_equiv_velems) with (l2:= (velems_union A1 A2 < e)); try (apply IHA2; eauto).
        unfold "=va=". intro c. simpl. reflexivity.

        split. rewrite <- In_push_annot_In; try auto. apply HnInA1. Search push_annot.
        rewrite notInElem_push_annot. apply HnInElemA1.

        apply NoDupElem_cons; [apply notInElem_push_annot|]; eauto.
        

Qed.


Lemma push_annot_andf_equiv A e e': (A < (e /\(F) e')) =va= ((A < e) < e').
Proof. unfold "=va=". intro c. Search push_annot.
repeat (rewrite configVElemSet_push_annot).
simpl.  rewrite configVElemSet_push_annot. simpl.
destruct (E[[ e]] c); destruct (E[[ e']] c);
simpl; reflexivity. Qed.




