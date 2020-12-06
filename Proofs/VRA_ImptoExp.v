(** Variational relational algebra lemmas *)
Set Warnings "-notation-overridden,-parsing".

Load configdistUnionInter.

(* Few points to remember:
   1. when destructing (vTypeImp S q = (A, _) ),
      get (NoDupAtt A) by applying NoDupAtt_vtypeImpNOTC'. 
*)

(* ------------------------------------------------------------
  | Explicitly Annotating Quaries
   ------------------------------------------------------------
*)

(* Helper function for Imp to Exp conversion : ImptoExp
   Get type of Implicit vquery without Type Checking; type is always explicitely annotated 
     -> Type validity checking is not required for convedrsion - just not performed here
     -> If vquery type checks then this function provides that valid vtype not vice versa 
        as it doesn't perform the validity checking ; Lemma vtypeImpNOTC_correct
     | Justification for not type checking
     |    if Implicit vquery to be converted doesn't type check 
     |        equivalent explicit vquery will not type check as well 
     |    conversion function should produce the equivalent explicit query 
     |        even for not type valid implicit vquery
*)



Fixpoint vtypeImpNOTC (e:fexp) (vs: vschema) (vq:vquery) : vqtype :=
 match vq with 
 (*| (rel_v (rn, (A_, e_'))) =>  let vr := (findVR rn vs) in
           match e with
          | litB true => (getvs vr, getf vr)
          | _         => (getvs vr, (e /\(F) getf vr))
          end*)
 | (rel_v (rn, (A_, e_'))) =>  let vr := (findVR rn vs) in
           (getvs vr, (e /\(F) getf vr))
 | (proj_v Q vq)     => 
      let (A', e') := vtypeImpNOTC e vs vq in 
        (vqtype_inter_vq Q (A', e'))
 | (chcQ e' vq1 vq2) => 
      let  (A1, e1) := vtypeImpNOTC (e /\(F) e') vs vq1  in
       let (A2, e2) := vtypeImpNOTC (e /\(F) (~(F) e')) vs vq2 in
        (vqtype_union_vq (A1, e1) (A2, e2))
 | (prod_v vq1 vq2) =>
      let (A1, e1)  := vtypeImpNOTC e  vs vq1 in
       let (A2, e2) := vtypeImpNOTC e  vs vq2 in
        (vqtype_union_vq (A1, e1) (A2, e2))
 | (setU_v op vq1 vq2) =>
       let (A1, e1)  := vtypeImpNOTC e vs vq1 in
        let (A2, e2)  := vtypeImpNOTC e vs vq2 in
         (A1, e1)
 end. 



(* Convert implicit vquery to explicit vquery w.r.t vSchema *)
Fixpoint ImptoExp (vq: vquery) (vs:vschema) : (vquery) :=
 match vq with 
 | (rel_v (rn, (A_, e_'))) => let (A, e) := vtypeImpNOTC (litB true) vs vq in 
                               (proj_v (A, e) vq)
 (* projected attribute list is not annotated - Design Decision in vdbms *)
 | (proj_v Q vq)           => let vq_s := (ImptoExp vq vs) in
                               let (A', e') := vtypeImpNOTC (litB true) vs vq_s in 
                                let QinterQ' := vqtype_inter_vq Q (A', e') in
                                 proj_v QinterQ' vq_s 

 | (chcQ e' vq1 vq2)   => chcQ e' (ImptoExp vq1 vs) (ImptoExp vq2 vs)
      
 | (prod_v vq1 vq2)    => prod_v (ImptoExp vq1 vs) (ImptoExp vq2 vs)
     
 | (setU_v op vq1 vq2) => setU_v op (ImptoExp vq1 vs) (ImptoExp vq2 vs)
      
 end. 

Notation "[ vq ] vs" := (ImptoExp vq vs) (at level 90, left associativity).

(* ------------------------------------------------------------
  | Correctness vtypeImpNOTC : 
       if vq has a valid type (from vtypeImp), 
          vtypeImpNOTC gives that same type
   ------------------------------------------------------------
*)

Lemma InRn_In:
forall rn vrs, InRn rn vrs <-> exists A e, In (rn, (A, e)) vrs.
Proof. intros. split. 
- intro H. induction vrs. 
+ simpl in H. destruct H.
+ destruct a as (rn', (A', e')). 
simpl in H. destruct H.
++ rewrite H. exists A'. exists e'.
simpl. eauto.
++ apply IHvrs in H. destruct H as [A H].
destruct H as [e H]. exists A. exists e.
simpl. eauto.
- intro H. destruct H as [A H].
destruct H as [e H]. induction vrs. 
+ simpl in H. destruct H.
+ destruct a as (rn', (A', e')). 
simpl in H. destruct H; try(inversion H; subst);
simpl; eauto.
Qed.



Lemma In_getVRAe rn A e vrs {HRn: NoDupRn vrs}: 
       In (rn, (A, e)) vrs -> getVRAe rn vrs = (rn, (A, e)).
Proof. intro H. induction vrs.
- simpl in H. destruct H.
- destruct a as (rn', (A', e')). 
simpl in H. destruct H.
+ simpl. inversion H; subst. 
rewrite stringBEF.eqb_refl. reflexivity.
+ simpl. inversion HRn; subst.
destruct (stringDecF.eqb rn' rn) eqn: Hrnrn'.
++ rewrite stringDecF.eqb_eq in Hrnrn'.
rewrite InRn_In in H2.
rewrite <- dist_not_exists in H2.
specialize H2 with A.
rewrite <- dist_not_exists in H2.
specialize H2 with e. 
rewrite Hrnrn' in H2. contradiction.
++ eauto. 
Qed.

Lemma getVRAe_In rn a As e vrs {HRn: NoDupRn vrs}: 
       getVRAe rn vrs = (rn, (cons a As, e)) ->  In (rn, (cons a As, e)) vrs.
Proof. 
intro H. induction vrs.
- simpl in H. inversion H.
- simpl. unfold getVRAe in H; fold getVRAe in H.
destruct a0 as (rn_, (A0, e0)).
destruct (stringDecF.eqb rn_ rn) eqn:Heq.
left. assumption.
right. apply IHvrs. inversion HRn; subst.
all: assumption.
Qed.



Lemma InVR_findVR rn A e S {HRn: NoDupRn (fst S)}: 
       InVR (rn, (A, e)) S -> findVR rn S = (rn, (A, e)).
Proof. intro H. inversion H; subst.
unfold findVR. simpl. destruct H0.
apply In_getVRAe in H0 .
unfold getr in H0.
simpl in H0. rewrite H0.
unfold getf in H1. 
simpl in H1.
unfold getr, getvs, getf.
simpl. rewrite H1. reflexivity.
assumption. Qed.

Lemma getVRAe_getr rn S: getr (getVRAe rn S) = rn.
Proof. unfold getr. induction S. simpl. reflexivity.
destruct a as (r, (A, e)). simpl.
destruct (stringDecF.eqb r rn) eqn:Heq. simpl. 
rewrite stringDecF.eqb_eq in Heq. all: assumption.
Qed.

Lemma findVR_fst rn S: fst (findVR rn S) = rn.
Proof. unfold findVR. simpl. apply getVRAe_getr. Qed.

Lemma findVR_InVR rn a As e S {HRn: NoDupRn (fst S)}: 
       findVR rn S = (rn, (a :: As, e)) -> InVR (rn, (a :: As, e)) S.
Proof. intro H. 
unfold findVR in H; fold findVR in H.
unfold InVR. 
unfold getr, getvs, getf. 
simpl. remember (getf (getVRAe rn (fst S))).
exists f. split. apply getVRAe_In.
assumption.
apply injective_projections.
simpl. 
inversion H. rewrite H1. unfold getr in H1.
assumption. inversion H. rewrite H2.
simpl. apply injective_projections.
simpl. unfold getvs in H2. assumption.
simpl. unfold getf in H3. rewrite Heqf.
unfold getf. rewrite <- H1 at 2. reflexivity.
inversion H. rewrite Heqf. rewrite H1. reflexivity.
Qed.

 

(* Correctness of vtypeImp_ function *)
 
Lemma vtypeImpNOTC_correct : forall e vs vq vt {HRn: NoDupRn (fst vs)}, 
  vtypeImp e vs vq vt -> (vtypeImpNOTC e vs vq) = vt.
Proof. 

intros. induction H;
  try(simpl vtypeImpNOTC);
  try(rewrite IHvtypeImp); 
  try(rewrite (IHvtypeImp1 HRn); rewrite (IHvtypeImp2 HRn)); 
  try(reflexivity); try(assumption);try(assumption). 
- apply InVR_findVR in H.
rewrite H. unfold getvs. unfold getf.
simpl. reflexivity. assumption. 
(*- Search NoDupAtt. apply nodupatt_fixed_point in HA.
unfold vqtype_inter_vq. simpl.
assert (Hn: vatts_inter (nodupatt (fst Q)) A' = (vatts_inter (fst Q) A')).
{ rewrite HA. reflexivity. }
apply injective_projections. simpl.
fold vatts_inter. assumption. simpl. reflexivity.*)
Qed.

(* NoDupAtt prop preservation vtypeImpNOTC *)



Lemma NoDupAtt_vatts_inter A B: 
   NoDupAtt A -> NoDupAtt (vatts_inter A B).
Proof. intro H.
induction A. rewrite vatts_inter_nil_l.
auto. simpl in H. rewrite vatts_inter_equation.
destruct a as (a0, e). inversion H; subst.
destruct (existsbAtt a0 B) eqn: Hex.

apply NoDupAtt_cons. apply notInAtt_vatts_inter. 
all: auto.
Qed.

Lemma NoDupAtt_vtypeImpNOTC : forall e vs vq {HRn: NoDupRn (fst vs)}
{HndpS: NODupAttRs vs} {HndpQ: NoDupAttvQ vq}, 
  NoDupAtt (fst (vtypeImpNOTC e vs vq)).
Proof. 

intros. generalize dependent e. induction vq.
- simpl. destruct v as (rn, (A, e')).
destruct (findVR rn vs) eqn:Hf.
simpl. destruct p as (Ap, ep).
destruct Ap. unfold getvs. simpl.
intro. apply NoDupAtt_nil.
apply (findVR_InVR) with (rn:=r0) (a:=v)
(As:= Ap) (e:=ep) in HRn as HIn.
apply HndpS in HIn. 
intro. apply HIn. pose (findVR_fst rn vs) as Hf'.
rewrite Hf in Hf'. simpl in Hf'. rewrite Hf' at 1.
assumption.
- intro. destruct (vtypeImpNOTC e vs vq) eqn:Hvq.
simpl. rewrite Hvq. unfold vqtype_inter_vq.
simpl. inversion HndpQ; subst. apply NoDupAtt_vatts_inter.
assumption.
- simpl. intro. inversion HndpQ; subst.
apply IHvq1 with (e:= (e /\(F) f)) in H1.
apply IHvq2 with (e:= (e /\(F) ~(F)f)) in H3.
destruct (vtypeImpNOTC (e /\(F) f) vs vq1) as (A1, e1).
destruct (vtypeImpNOTC (e /\(F) ~(F) f) vs vq2) as (A2, e2).
simpl. unfold vatts_union. apply NoDupAtt_nodupatt.
- intro. simpl. 
destruct (vtypeImpNOTC e vs vq1) as (A1, e1).
destruct (vtypeImpNOTC e vs vq2) as (A2, e2).
unfold vqtype_union_vq. simpl. 
unfold vatts_union. apply NoDupAtt_nodupatt.
- intro. simpl. inversion HndpQ; subst.
apply IHvq1 with (e:=e) in H1.
destruct (vtypeImpNOTC e vs vq1) as (A1, e1).
destruct (vtypeImpNOTC e vs vq2) as (A2, e2).
unfold vqtype_union_vq. assumption.
Qed.

Lemma NoDupAtt_vtypeImpNOTC' : forall e vs vq Aq eq {HRn: NoDupRn (fst vs)}
{HndpS: NODupAttRs vs} {HndpQ: NoDupAttvQ vq}, 
  vtypeImpNOTC e vs vq = (Aq, eq) ->
  NoDupAtt (Aq).
Proof. intros. assert ( Hfst: fst (vtypeImpNOTC e vs vq) = Aq).
rewrite H. simpl. reflexivity. 
rewrite <- Hfst. apply NoDupAtt_vtypeImpNOTC.
all: try(assumption). Qed.

Lemma NoDupAttvQ_ImptoExp q S {HRs: NoDupRn (fst S)} {HS: NODupAttRs S}: 
          NoDupAttvQ q -> NoDupAttvQ ([q]S).
Proof. intros. induction H.
+ simpl. destruct (vtypeImpNOTC (litB true) S ([vq] S)) as (A', e').
apply NoDupAttvQ_proj_v. unfold vqtype_inter_vq. simpl.
apply NoDupAtt_vatts_inter; assumption. assumption.
+ simpl. 
apply NoDupAttvQ_proj_v. 
destruct (findVR rn S) eqn:HInVR. pose (findVR_fst rn S) as Hrn.
rewrite HInVR in Hrn. simpl in Hrn. rewrite Hrn in HInVR.
rewrite Hrn. unfold getvs, getf.
simpl. destruct p. destruct v. simpl. apply NoDupAtt_nil.
apply (findVR_InVR) in HInVR; try assumption. unfold NODupAttRs in HS.
specialize HS with (rn, (v :: v0, f)). apply HS in HInVR. 
unfold getvs in HInVR. simpl in HInVR. simpl. assumption.
apply NoDupAttvQ_rel_v. 
+ simpl. apply NoDupAttvQ_chcQ; assumption.
+ simpl. apply NoDupAttvQ_prod_v; assumption.
+ simpl. apply NoDupAttvQ_setU_v; assumption.
Qed.

Ltac simpl_equivE := unfold equivE; simpl; intro; try(eauto).

(* ------------------------------------------------------------
  | Properties Imp Exp relationship 
   ------------------------------------------------------------
*)




Lemma contex_equiv_NOTC' e1 e2 S q {HRn: NoDupRn (fst S)}
{HndpS: NODupAttRs S} {HndpQ: NoDupAttvQ q}:
   e1 =e= e2 -> 
     fst(vtypeImpNOTC e1 S q) = fst(vtypeImpNOTC e2 S q) /\
     snd(vtypeImpNOTC e1 S q) =e= snd(vtypeImpNOTC e2 S q).  
Proof. 
generalize dependent e2. 
generalize dependent e1. induction q; 
intros e1 e2 He12.

{ destruct v as (rn, (Av, ev)). simpl.
destruct (findVR rn S) eqn:Hf.
unfold getvs, getf, equiv_vqtype.
simpl. split. reflexivity. 
unfold equivE. simpl.  intro.
rewrite He12. reflexivity.
}

{ simpl. inversion HndpQ; subst.
apply IHq with (e1:=e1) (e2:=e2) in H2 as IHq'.
destruct (vtypeImpNOTC e1 S q) as (Aq1, eq1) eqn:He1.
destruct (vtypeImpNOTC e2 S q) as (Aq2, eq2) eqn:He2.
destruct IHq' as [IHqA IHqe]. 
simpl in IHqA. simpl in IHqe. 
unfold vqtype_inter_vq, equiv_vqtype.
simpl. split. 

rewrite IHqA. reflexivity.

(*apply NoDupAtt_vtypeImpNOTC' in He1 as HnAq1.
apply NoDupAtt_vtypeImpNOTC' in He2 as HnAq2.
apply vatts_inter_equiv.
all : try(assumption); try(reflexivity).*)

unfold equivE. intro. simpl. rewrite IHqe.
reflexivity. 

assumption.
}

{ simpl. inversion HndpQ; subst.
apply IHq1 with (e1:=(e1 /\(F) f)) (e2:=(e2 /\(F) f)) in H1 as IHq1'.
apply IHq2 with (e1:=(e1 /\(F) ~(F) f)) (e2:=(e2 /\(F) ~(F) f)) in H3 as IHq2'.

destruct (vtypeImpNOTC (e1 /\(F) f) S q1) as (Aq1f, eq1f) eqn:He1f.
destruct (vtypeImpNOTC (e2 /\(F) f) S q1) as (Aq2f, eq2f) eqn:He2f.
destruct (vtypeImpNOTC (e1 /\(F) ~(F) f) S q2) as (Aq1nf, eq1nf) eqn:He1nf.
destruct (vtypeImpNOTC (e2 /\(F) ~(F) f) S q2 ) as (Aq2nf, eq2nf) eqn:He2nf.


apply NoDupAtt_vtypeImpNOTC' in He1f as HnAq1f.
apply NoDupAtt_vtypeImpNOTC' in He2f as HnAq2f.
apply NoDupAtt_vtypeImpNOTC' in He1nf as HnAq1nf.
apply NoDupAtt_vtypeImpNOTC' in He2nf as HnAq2nf. 

simpl in IHq1', IHq2'. destruct IHq1' as [IHq1'A IHq1'e].
destruct IHq2' as [IHq2'A IHq2'e].

unfold vqtype_union_vq. simpl. split. 
rewrite IHq1'A, IHq2'A. reflexivity.

simpl_equivE. rewrite IHq1'e, IHq2'e. reflexivity.
 
all: (try simpl; try eauto).

all: try(simpl_equivE; rewrite He12; reflexivity).
}

{ simpl. inversion HndpQ; subst.

apply (IHq1 H1) with (e1:=e1) (e2:=e2) in He12 as IHq1'.
apply (IHq2 H2) with (e1:=e1) (e2:=e2) in He12 as IHq2'.

destruct (vtypeImpNOTC e1 S q1) as (Aq11, eq11) eqn:He1q1.
destruct (vtypeImpNOTC e2 S q1) as (Aq21, eq21) eqn:He2q1.
destruct (vtypeImpNOTC e1 S q2) as (Aq12, eq12) eqn:He1q2.
destruct (vtypeImpNOTC e2 S q2) as (Aq22, eq22) eqn:He2q2.

unfold equiv_vqtype in IHq1'; 
simpl in IHq1'; destruct IHq1' as [HAq1 Heq1].

unfold equiv_vqtype in IHq2'; 
simpl in IHq2'; destruct IHq2' as [HAq2 Heq2].

unfold vqtype_union_vq, equiv_vqtype.
simpl. split. 

apply NoDupAtt_vtypeImpNOTC' in He1q1 as HnAq11; try (assumption).
apply NoDupAtt_vtypeImpNOTC' in He2q1 as HnAq21; try (assumption).
apply NoDupAtt_vtypeImpNOTC' in He1q2 as HnAq12; try (assumption).
apply NoDupAtt_vtypeImpNOTC' in He2q2 as HnAq22; try (assumption).

rewrite HAq1, HAq2. reflexivity.

(*apply vatts_union_equiv; try (assumption).*)

simpl_equivE. rewrite Heq1, Heq2.
reflexivity.
}

{ 

simpl. inversion HndpQ; subst.

apply (IHq1 H1) with (e1:=e1) (e2:=e2) in He12 as IHq1'.

destruct (vtypeImpNOTC e1 S q1) as (Aq11, eq11) eqn:He1q1.
destruct (vtypeImpNOTC e2 S q1) as (Aq21, eq21) eqn:He2q1.
destruct (vtypeImpNOTC e1 S q2) as (Aq12, eq12) eqn:He1q2.
destruct (vtypeImpNOTC e2 S q2) as (Aq22, eq22) eqn:He2q2.

auto.

(* unfold equiv_vqtype in IHq1'; 
simpl in IHq1'; destruct IHq1' as [HAq1 Heq1].

unfold vqtype_union_vq, equiv_vqtype.
simpl. split. 

all: assumption.*)

}

Qed.

Lemma contex_equiv_NOTC e1 e2 S q {HRn: NoDupRn (fst S)}
{HndpS: NODupAttRs S} {HndpQ: NoDupAttvQ q}:
   e1 =e= e2 -> 
    vtypeImpNOTC e1 S q =T= vtypeImpNOTC e2 S q. 
Proof. intro He1e2. 
apply contex_equiv_NOTC' with (S:=S) (q:=q) in He1e2; try assumption.
unfold equiv_vqtype. destruct He1e2 as [Hfst Hsnd].
apply eq_equiv_vatts in Hfst. split; assumption. Qed.


Lemma contex_intro_NOTC' e S q {HRn: NoDupRn (fst S)}
{HndpS: NODupAttRs S} {HndpQ: NoDupAttvQ q} Aq eq eq' e': 

vtypeImpNOTC e S q = (Aq, eq) ->
eq' =e= (eq /\(F) e') ->
( fst (vtypeImpNOTC (e /\(F) e') S q) = Aq /\
  snd (vtypeImpNOTC (e /\(F) e') S q) =e= eq').
Proof. 
generalize dependent e.
generalize dependent Aq.
generalize dependent eq. 
generalize dependent eq'.
generalize dependent e'.
induction q. 

{ intros. simpl in H. 
destruct v as (rn, (A_, e_)). simpl. 
destruct (findVR rn S) as (rn_, (Ar, er)).
unfold getvs, getf, equiv_vqtype in H. simpl in H.
inversion H; subst.
(* destruct H as [HAr Her]. *)
unfold getvs, getf. simpl.
split; eauto.

simpl_equivE. rewrite H0.
simpl. (*rewrite <- Her. simpl. 
Search andb.*) rewrite <- andb_assoc.
rewrite andb_comm with (b1:=(E[[ e']] c)).
rewrite andb_assoc. reflexivity.
} 

{ intros. simpl in H. inversion HndpQ; subst.
destruct a as (Ap, ep).

destruct (vtypeImpNOTC e S q) as (Aq_, eq) eqn: Hefq.

apply NoDupAtt_vtypeImpNOTC' in Hefq as HnAq; try (assumption).
(*apply eq_equiv_vqtype in Hefq.*)

(*assert(Hefq': fst (vtypeImpNOTC e S q) = Aq_ /\
snd (vtypeImpNOTC e S q) =e= eq).
rewrite Hefq. simpl. split; eauto. apply equivE_refl.*)

eapply (IHq H4) with (e':= e')(eq':= (eq /\(F) e')) in Hefq; try (reflexivity).

simpl.

destruct Hefq as [Hefqfst Hefqsnd].

(* context now has the (prod/setU) q1 q2 value but in equivalence *)
destruct (vtypeImpNOTC (e /\(F) e') S q) as (Aq', eq_') eqn:Hefe'q.

simpl in Hefqfst. rewrite Hefqfst. rewrite Hefqfst in *. 

unfold vqtype_inter_vq, equiv_vqtype in H;
simpl in H. inversion H; subst.

unfold vqtype_inter_vq, equiv_vqtype;
simpl. 

split. auto.

(*unfold equiv_vqtype in Hefq; 
simpl in Hefq; destruct Hefq as [HAq Heq].

split.

rewrite <- HAq_. apply vatts_inter_equiv.
all: apply NoDupAtt_vtypeImpNOTC' in Hefe'q as HnAq';
try(assumption); try(reflexivity).*)

rewrite H0. simpl_equivE. simpl in Hefqsnd.
rewrite Hefqsnd. simpl.
rewrite <- andb_assoc. reflexivity.
}

{ (* Choice rule case: *)

intros. simpl in H. inversion HndpQ; subst.

destruct (vtypeImpNOTC (e /\(F) f) S q1) as (Aq1, eq1) eqn: Hefq1.
destruct (vtypeImpNOTC (e /\(F) ~(F)f) S q2) as (Aq2, eq2) eqn: Hefq2.

apply NoDupAtt_vtypeImpNOTC' in Hefq1 as HnAq1; try (assumption).
apply NoDupAtt_vtypeImpNOTC' in Hefq2 as HnAq2; try (assumption).

(*destruct (vtypeImpNOTC ((e /\(F) e') /\(F) f) S q1) as (Aq1', eq1')     eqn:Hefe'q1.
  destruct (vtypeImpNOTC ((e /\(F) e') /\(F) ~(F)f) S q2) as (Aq2', eq2') eqn:Hefe'q2.*)
(*apply eq_equiv_vqtype in Hefq1. apply eq_equiv_vqtype in Hefq2.*)

eapply IHq1 with (e':= e')(eq':= (eq1 /\(F) e')) in Hefq1; try(assumption); try(reflexivity).
eapply IHq2 with (e':= e')(eq':= (eq2 /\(F) e')) in Hefq2; try(assumption); try(reflexivity).

(* context re-ordering assumption *)
assert (Hr: (((e /\(F) f) /\(F) e') =e= ((e /\(F) e') /\(F) f))/\
(((e /\(F) ~(F) f) /\(F) e') =e= ((e /\(F) e') /\(F) ~(F) f))).
{ (* Proof of assertion *)
split. all: try (simpl_equivE; rewrite <- andb_assoc;
rewrite andb_comm with (b2:=(E[[ e']] c));
rewrite andb_assoc; reflexivity). } 
destruct Hr as [Hr1 Hr2].

eapply (contex_equiv_NOTC') with (q:= q1) (S:=S)  in Hr1; try(assumption).
eapply (contex_equiv_NOTC') with (q:= q2) (S:=S)  in Hr2; try(assumption).
(* eapply (contex_equiv_NOTC) with (A:=Aq2) (q:= q2)
(S:=S) (f1:= (eq2 /\(F) e')) (f2:= (eq2 /\(F) e')) in Hr2.*)

(*apply (contex_equiv_NOTC) with (e1:= (e /\(F) e'))
(f1:= (eq1 /\(F) e' \/(F) eq2 /\(F) e')).*)

(*simpl. rewrite Hr1 in Hefq1. 
rewrite Hr2 in Hefq2. *)

simpl. 
destruct Hr1 as [Hr1fst Hr1snd].
destruct Hr2 as [Hr2fst Hr2snd].
destruct Hefq1 as [Hefq1fst Hefq1snd].
destruct Hefq2 as [Hefq2fst Hefq2snd].
rewrite Hr1fst in Hefq1fst.
rewrite Hr2fst in Hefq2fst.
rewrite Hr1snd in Hefq1snd.
rewrite Hr2snd in Hefq2snd.

(* context now has the choice rule q1 q2 value but in equivalence *)
destruct (vtypeImpNOTC ((e /\(F) e') /\(F) f) S q1) as (Aq1', eq1') eqn:Hefe'q1.
destruct (vtypeImpNOTC ((e /\(F) e') /\(F) ~(F)f) S q2) as (Aq2', eq2') eqn:Hefe'q2.

simpl in Hefq1fst, Hefq1snd, Hefq2fst, Hefq2snd.
rewrite Hefq1fst, Hefq2fst.

unfold vqtype_union_vq in H.
simpl in H. inversion H; subst.

unfold vqtype_union_vq. 
simpl.  

split. reflexivity.
rewrite H0. simpl_equivE. rewrite Hefq1snd, Hefq2snd.
simpl. symmetry. apply andb_orb_distrib_l. 

(*unfold equiv_vqtype in Hefq1. 
simpl in Hefq1. destruct Hefq1 as [H1Aq H1eq].

unfold equiv_vqtype in Hefq2. 
simpl in Hefq2. destruct Hefq2 as [H2Aq H2eq].
split.

rewrite <- HAq.  
apply NoDupAtt_vtypeImpNOTC' in Hefe'q1 as HnAq1'; try(assumption); try(reflexivity).
apply NoDupAtt_vtypeImpNOTC' in Hefe'q2 as HnAq2'; try(assumption); try(reflexivity).

apply vatts_union_equiv; try(assumption); try(reflexivity).

rewrite H0. simpl_equivE.
rewrite <- Heq0. simpl.
rewrite H1eq, H2eq. simpl. 
symmetry. apply andb_orb_distrib_l. *)

}


all: intros; simpl in H; inversion HndpQ; subst;

destruct (vtypeImpNOTC e S q1) as (Aq1, eq1) eqn: Hefq1;
destruct (vtypeImpNOTC e S q2) as (Aq2, eq2) eqn: Hefq2;

apply NoDupAtt_vtypeImpNOTC' in Hefq1 as HnAq1; try (assumption);
apply NoDupAtt_vtypeImpNOTC' in Hefq2 as HnAq2; try (assumption);

(*apply eq_equiv_vqtype in Hefq1; apply eq_equiv_vqtype in Hefq2;*)

eapply IHq1 with (e':= e')(eq':= (eq1 /\(F) e')) in Hefq1; try(assumption); try(reflexivity);
eapply IHq2 with (e':= e')(eq':= (eq2 /\(F) e')) in Hefq2; try(assumption); try(reflexivity);

simpl;

(* context now has the (prod/setU) q1 q2 value but in equivalence *)
destruct (vtypeImpNOTC (e /\(F) e') S q1) as (Aq1', eq1') eqn:Hefe'q1;
destruct (vtypeImpNOTC (e /\(F) e') S q2) as (Aq2', eq2') eqn:Hefe'q2;

simpl;

destruct Hefq1 as [Hefq1fst Hefq1snd];
destruct Hefq2 as [Hefq2fst Hefq2snd];
simpl in Hefq1fst, Hefq1snd, Hefq2fst, Hefq2snd;

unfold vqtype_union_vq in H;
simpl in H; inversion H; subst;

(*rewrite Hefq1fst, Hefq2fst. *)
split; [reflexivity|]. 

try(rewrite H0; simpl_equivE;
rewrite Hefq1snd, Hefq2snd; simpl; 
symmetry; apply andb_orb_distrib_l).

try(rewrite H0, Hefq1snd; apply equivE_refl). 

(*unfold vqtype_union_vq, equiv_vqtype in H;
simpl in H; destruct H as [HAq Heq0];

unfold vqtype_union_vq, equiv_vqtype;
simpl;

unfold equiv_vqtype in Hefq1; 
simpl in Hefq1; destruct Hefq1 as [H1Aq H1eq];

unfold equiv_vqtype in Hefq2; 
simpl in Hefq2; destruct Hefq2 as [H2Aq H2eq];

split; [

(* prod *)
try (rewrite <- HAq;
apply NoDupAtt_vtypeImpNOTC' in Hefe'q1 as HnAq1'; try(assumption); try(reflexivity);
apply NoDupAtt_vtypeImpNOTC' in Hefe'q2 as HnAq2'; try(assumption); try(reflexivity);
apply vatts_union_equiv; try(assumption); try(reflexivity));

(* setU *)
try(apply transitivity with (y:=Aq1); assumption)

| 

(* prod *)
try(rewrite H0; simpl_equivE;
rewrite <- Heq0; simpl;
rewrite H1eq, H2eq; simpl; 
symmetry; apply andb_orb_distrib_l);

(* setU *)
try(rewrite H0; simpl_equivE;
rewrite <- Heq0; simpl; apply H1eq)

].*)


Qed.

Lemma contex_intro_NOTC e S q {HRn: NoDupRn (fst S)}
{HndpS: NODupAttRs S} {HndpQ: NoDupAttvQ q} Aq eq eq' e': 

vtypeImpNOTC e S q =T= (Aq, eq) ->
eq' =e= (eq /\(F) e') ->
vtypeImpNOTC (e /\(F) e') S q =T= (Aq, eq').
Proof. 
destruct (vtypeImpNOTC e S q) as (Aq'', eq'') eqn: Hq.
apply contex_intro_NOTC' with (eq':=eq'' /\(F) e') (e':=e') in Hq; try assumption;
try reflexivity.

intros HT He. unfold equiv_vqtype in HT.
destruct Hq as [Hqfst Hqsnd].
destruct HT as [HTfst HTsnd].
simpl in HTfst, HTsnd.  

unfold equiv_vqtype . split.
simpl. rewrite <- Hqfst in HTfst. auto.
simpl. rewrite Hqsnd, He. simpl_equivE. rewrite HTsnd.
auto. 

Qed.



 
Lemma vatts_inter_simpl A B:
vatts_inter (vatts_inter A B) B =va= vatts_inter A B. 
Proof. induction A.
- repeat (rewrite vatts_inter_nil_l).
reflexivity.
- destruct B.
simpl. repeat (rewrite vatts_inter_nil_r).
reflexivity. destruct a as (a', e').
destruct (existsbAtt a' (v :: B)) eqn:Ha'.
rewrite vatts_inter_equation. 
destruct (vatts_inter (ae a' e' :: A) (v :: B)) eqn:Ha'AvB.
reflexivity.
destruct v0 as (a0, e0).
rewrite vatts_inter_equation in Ha'AvB. 
rewrite Ha' in Ha'AvB. 
inversion Ha'AvB; subst.
rewrite Ha'. simpl. unfold equiv_vatts.
intro c. simpl. 
destruct ((E[[ e']] c) && (E[[ extract_e a0 (v :: B)]] c) &&
  (E[[ extract_e a0 (v :: B)]] c)) eqn:Hes;
rewrite <- andb_assoc in Hes; rewrite andb_diag in Hes;
rewrite Hes; try( apply cons_equiv_atts);
unfold equiv_vatts in IHA; auto.

assert (Hsimp: vatts_inter (ae a' e' :: A) (v :: B) = vatts_inter A (v :: B)).
{ rewrite vatts_inter_equation. rewrite Ha'. reflexivity. }

rewrite Hsimp. apply IHA.
Qed.


(*nodupatt_equiv: forall [A A' : vatts], A =va= A' -> nodupatt A =va= nodupatt A'
*)


Lemma ImpQ_ImpType_Equiv_ExpQ_ImpType e S q A A': 
  { e , S |-  q   | A }  -> 
  { e , S |- [q]S | A' } -> 
   A =T= A'.

Proof.  
generalize dependent A'.
generalize dependent A.
generalize dependent e.
induction q; destruct A as (A, ea); 
destruct A' as (A', ea');
intros HImp HExp.

{ 
inversion HImp; subst.
simpl ImptoExp in HExp.
apply InVR_findVR in H3
as HInFind.
rewrite HInFind in HExp.
unfold getvs in HExp. unfold getf in HExp.
simpl in HExp.
inversion HExp; subst.
inversion H5; subst.
apply InVR_findVR in H2
as HInFind'.
rewrite HInFind in HInFind'.
inversion HInFind'; subst. 
unfold equiv_qtype. split.
+ simpl. rewrite vatts_inter_pres. reflexivity.
assumption. 
+ simpl. simpl_equivE.
symmetry. rewrite <- andb_comm.
rewrite <- andb_assoc. rewrite andb_diag.
reflexivity. + assumption. + assumption.
}

{ 

destruct a as (Ap, ep).
inversion HImp; subst.
rename A'0 into Aq.
rename e' into eq.

simpl in HExp. simpl in HndpQ.
destruct (vtypeImpNOTC (litB true) S ([q] S))
as (Aqs, eqs) eqn:Hvtntc. 
inversion HExp; subst.
apply NoDupAtt_vtypeImpNOTC' in Hvtntc as HndpattAqs; try assumption.
specialize IHq with (e:=e) (A:=(Aq, eq)) (A':=(A'0, e')).
apply (IHq H4) in H5 as Hequ.
unfold equiv_vqtype.
unfold equiv_vqtype in Hequ;
simpl in Hequ; destruct Hequ; apply vtypeImpNOTC_correct in H5
as Hqsine; try assumption. simpl. apply eq_equiv_vqtype in Hvtntc.
apply eq_equiv_vqtype in Hqsine.
apply (contex_intro_NOTC (litB true))
with (e':=e) (eq':= (eqs /\(F) e) ) in Hvtntc; try assumption; try reflexivity.
assert(Hee': (litB true /\(F) e) =e= e ).
{ unfold equivE. simpl. reflexivity. }
apply (contex_equiv_NOTC) with (S:=S) (q:=[q] S) in Hee'; try assumption.
rewrite Hvtntc in Hee'. rewrite <- Hee' in Hqsine. 
inversion Hqsine; subst. simpl in H1, H2.
split.  
+ symmetry. rewrite vatts_inter_equiv with 
(A':=(vatts_inter Ap A'0)) (B':=A'0).
rewrite vatts_inter_simpl.
all: try(assumption); try(reflexivity). 
1, 3: apply vatts_inter_equiv; try(symmetry; assumption); 
try assumption; try reflexivity. 
1: apply NoDupAtt_vatts_inter; assumption.
(*all: try(apply NoDupAtt_vatts_inter); try(apply vatts_inter_equiv); 
try(symmetry; assumption); try(assumption);
try(reflexivity). *)
+ simpl. rewrite <- H2 in H0. simpl_equivE.
unfold equivE in H0. simpl in H0.
rewrite H0. rewrite <- H2. simpl. rewrite andb_assoc.
rewrite andb_assoc. rewrite <- andb_diag with (b:=(E[[ eqs]] c)) at 1.
rewrite andb_assoc. reflexivity.
}

all: try(inversion HImp as
[ | | e0 f0 S0 HnS HnAS 
      q10 HnQ1 q20 HnQ2
      A1 HnA1 e1 A2 HnA2 e2 
      Hq1 Hq2
    | e0 S0 HnS HnAS 
      q10 HnQ1 q20 HnQ2
      A1 HnA1 e1 A2 HnA2 e2
      Hq1 Hq2
    | ]; subst;
simpl in HExp; inversion HExp as
[ | | e0 f0 S0 HnSs HnASs 
      q10 HnQ1s q20 HnQ2s
      A1s HnA1s e1s A2s HnA2s e2s 
      Hq1s Hq2s
    | e0 S0 HnSs HnASs
      q10 HnQ1s q20 HnQ2s
      A1s HnA1s e1s A2s HnA2s e2s
      Hq1s Hq2s
    | ]; subst;
apply IHq1 with (A':=(A1s, e1s)) in Hq1;
apply IHq2 with (A':=(A2s, e2s)) in Hq2;
try (assumption);
unfold equiv_vqtype in Hq1;
unfold equiv_vqtype in Hq2;
simpl in Hq1; simpl in Hq2;
destruct Hq1 as [Hq1A Hq1e];
destruct Hq2 as [Hq2A Hq2e];
unfold equiv_vqtype; simpl;
split; try (apply vatts_union_equiv;
try (assumption));
unfold equivE; intro ;
simpl; rewrite Hq1e, Hq2e;
reflexivity).

{ inversion HImp; subst.
simpl in HExp. inversion HExp; subst.
apply IHq1 with (A':=(A', ea')) in H5.
assumption. assumption. }

Qed.


Lemma ExpQ_ImpType_Equiv_ExpQ_ExpType e S q A A': 
  { e , S |- [q]S | A }  -> 
  { e , S |= [q]S | A' } -> 
   A =T= A'.
Proof. 
generalize dependent A'.
generalize dependent A.
generalize dependent e.
induction q; destruct A as (A, ea); 
destruct A' as (A', ea');
intros HImp HExp.

{ (* Relation Rule *)

destruct v as (rn, (A_, e_)).
simpl in HImp.
simpl in HExp.

destruct (findVR rn S) as (rn_, (Ar, er)) eqn: HfindVR.

unfold getvs, getf in HImp. simpl in HImp.
unfold getvs, getf in HExp. simpl in HExp.

inversion HImp as [|
                   eImp SImp HndpRSImp HndpASImp vqImp HndpvQImp
                   e'Imp A'Imp HndpAA'Imp QImp HndpQImp
                   HqImp HsbsmpImp | | | ]; subst.
inversion HExp as [|
                   eExp SExp HndpRSExp HndpASExp vqExp HndpvQExp
                   e'Exp A'Exp HndpAA'Exp QExp HndpQExp
                   HqExp HsbsmpExp| | | ]; subst.

inversion HqImp as [eImp' SImp' HndpRSImp' HndpASImp' 
                   rnImp' A_Imp' A'Imp' HndpA'Imp' e_Imp' e'Imp' 
                   HInVRImp HsatImp |
                   | | | ]; subst.
(*inversion HqExp as [eExp' SExp' HndpRSExp' HndpASExp'
                   rnExp' AExp' HndpA'Exp' e'Exp' 
                   HInVRExp HsatExp|
                   | | | ]; subst.

apply InVR_findVR in HInVRExp
as HInFindExp; try assumption.*)

apply InVR_findVR in HInVRImp
as HInFindImp; try assumption.

rewrite HfindVR in HInFindImp.
inversion HInFindImp; subst.

(*rewrite not_sat_not_prop in HsatExp. 
rewrite <- sat_taut_comp in HsatExp. *)

unfold equiv_vqtype. simpl.
split. 
(* =va= *)apply vatts_inter_pres; assumption.

(* =e= *)simpl_equivE. 
rewrite andb_comm. rewrite <- andb_assoc.
rewrite andb_diag. apply andb_comm.
}

{ (* Project Rule *)
simpl in HImp.
simpl in HExp.

destruct (vtypeImpNOTC (litB true) S ([q] S)) as (Aqs, eqs) eqn:HqST.


destruct a as (Ap, ep).

inversion HImp as [|
                   eImp SImp HndpRSImp HndpASImp vqImp HndpvQImp
                   e'Imp A'Imp HndpAA'Imp QImp HndpQImp
                   HqImp HsbsmpImp | | | ]; subst.
inversion HExp as [|
                   eExp SExp HndpRSExp HndpASExp vqExp HndpvQExp
                   e'Exp A'Exp HndpAA'Exp QExp HndpQExp
                   HqExp HsbsmpExp| | | ]; subst.

apply NoDupAtt_vtypeImpNOTC' in HqST as HndpattAqs; try assumption.

apply eq_equiv_vqtype in HqST.

apply (contex_intro_NOTC (litB true))
with (e':=e) (eq':= (eqs /\(F) e) ) in HqST; try assumption; try reflexivity.

apply vtypeImpNOTC_correct in HqImp as HqSTine; try assumption. 

apply eq_equiv_vqtype in HqSTine.

(* equivalent context intro *)
assert(Htrue_e: (litB true /\(F) e) =e= e ).
{ unfold equivE. simpl. reflexivity. }

apply (contex_equiv_NOTC) with (S:=S) (q:=[q] S) in Htrue_e; try assumption.
rewrite HqST in Htrue_e. rewrite HqSTine in Htrue_e. 

unfold equiv_vqtype in Htrue_e.
simpl in Htrue_e.
destruct Htrue_e as [HAqsAImp HeqseImp].

unfold equiv_vqtype. simpl.
split.

+ rewrite vatts_inter_equiv with (A':=(vatts_inter Ap Aqs)) (B':=Aqs).
rewrite vatts_inter_simpl.
all: try(symmetry; assumption); try(assumption); try(reflexivity). 

+ simpl_equivE. rewrite <- HeqseImp. simpl. symmetry.
rewrite <- andb_diag with (b:=(E[[ eqs]] c)) at 1.
rewrite andb_assoc. rewrite andb_assoc. reflexivity.

}

all: (* Choice / Product / SetOp Rules *)

simpl in HImp;
simpl in HExp;

inversion HImp as [|
                   | 
                   eImp e'Imp SImp HndpRSImp HndpASImp 
                   vq1Imp HndpvQ1Imp vq2Imp HndpvQ2Imp
                   A1Imp HndpAA1Imp e1Imp A2Imp HndpAA2Imp e2Imp 
                   Hq1Imp Hq2Imp 
                   | 
                   eImp SImp HndpRSImp HndpASImp 
                   vq1Imp HndpvQ1Imp vq2Imp HndpvQ2Imp
                   A1Imp HndpAA1Imp e1Imp A2Imp HndpAA2Imp e2Imp 
                   Hq1Imp Hq2Imp HInterImp 
                   | 
                   eImp SImp HndpRSImp HndpASImp 
                   vq1Imp HndpvQ1Imp vq2Imp HndpvQ2Imp
                   A1Imp HndpAA1Imp e1Imp A2Imp HndpAA2Imp e2Imp opImp
                   Hq1Imp Hq2Imp HEquivImp ]; subst; 
inversion HExp as [|
                   |
                   eExp e'Exp SExp HndpRSExp HndpASExp 
                   vq1Exp HndpvQ1Exp vq2Exp HndpvQ2Exp
                   A1Exp HndpAA1Exp e1Exp A2Exp HndpAA2Exp e2Exp 
                   Hq1Exp Hq2Exp 
                   | 
                   eExp SExp HndpRSExp HndpASExp 
                   vq1Exp HndpvQ1Exp vq2Exp HndpvQ2Exp
                   A1Exp HndpAA1Exp e1Exp A2Exp HndpAA2Exp e2Exp 
                   Hq1Exp Hq2Exp HInterExp 
                   | 
                   eExp SExp HndpRSExp HndpASExp 
                   vq1Exp HndpvQ1Exp vq2Exp HndpvQ2Exp
                   A1Exp HndpAA1Exp e1Exp A2Exp HndpAA2Exp e2Exp opExp
                   Hq1Exp Hq2Exp HEquivExp ]; subst;

apply (IHq1 _ _ _ Hq1Imp) in Hq1Exp as Hq1Eq;
apply (IHq2 _ _ _ Hq2Imp) in Hq2Exp as Hq2Eq;

(* 3: setOp rule *) try assumption;

unfold equiv_vqtype in Hq1Eq; simpl in Hq1Eq;
destruct Hq1Eq as [Hq1A Hq1e];

unfold equiv_vqtype in Hq2Eq; simpl in Hq2Eq;
destruct Hq2Eq as [Hq2A Hq2e];

unfold equiv_vqtype; simpl;
split; 

try (apply vatts_union_equiv; try assumption);

try (simpl_equivE; rewrite Hq1e, Hq2e;
reflexivity).


Qed.

Lemma ImpQ_ImpType_implies_ExpQ_ImpType e S q A: 
  { e , S |- q | A }  -> 
  exists A', { e , S |- [q]S | A' }. 
Proof. 
generalize dependent A.
generalize dependent e.
induction q; destruct A as (A, ea);
intros HImp. 

{ 

destruct v as (rn, (A_, e_)).
simpl in HImp. simpl.
inversion HImp as [eImp SImp HndpRSImp HndpASImp rnImp A_Imp
                   A'Imp HndpA'Imp e_Imp e'Imp 
                   HInVRImp | | | | ]; subst.

rename e'Imp into e'.
apply InVR_findVR in HInVRImp as HInFindImp; try assumption.

rewrite HInFindImp.

unfold getvs, getf. simpl.
exists (vqtype_inter_vq (A, litB true /\(F) e') (A, e /\(F) e')).

apply Project_vE_imp; try assumption.

apply NoDupAttvQ_rel_v.

unfold subsumpImp_vqtype. 
intros a ea HIn.
exists ea. assumption.

}

{
simpl in HImp. simpl. 

destruct (vtypeImpNOTC (litB true) S ([q] S)) as (Aqs, eqs) eqn:HqST.

destruct a as (Ap, ep).

inversion HImp as [|
                   eImp SImp HndpRSImp HndpASImp vqImp HndpvQImp
                   e'Imp A'Imp HndpAA'Imp QImp HndpQImp
                   HqImp HsbsmpImp | | | ]; subst.

apply IHq in HqImp as Hqs. destruct Hqs as [(Aqse, eqse) Hqs].
apply vtypeImpNOTC_correct in Hqs as HqSTine; try assumption.

apply NoDupAtt_vtypeImpNOTC' in HqST as HndpattAqs; try assumption.

(*apply eq_equiv_vqtype in HqST as HqSTeqv.*) 

apply (contex_intro_NOTC' (litB true))
with (e':=e) (eq':= (eqs /\(F) e) ) in HqST; try assumption; try reflexivity.

assert(Htrue_e: (litB true /\(F) e) =e= e ).
{ unfold equivE. simpl. reflexivity. }

apply (contex_equiv_NOTC') with (S:=S) (q:=[q] S) in Htrue_e; try assumption.

destruct HqST as [HqSTfst HqSTsnd].
destruct Htrue_e as [Htrue_efst Htrue_esnd].

rewrite HqSTfst in Htrue_efst.
rewrite HqSTsnd in Htrue_esnd.

rewrite HqSTine in Htrue_efst, Htrue_esnd.
simpl in Htrue_efst, Htrue_esnd.


exists (vqtype_inter_vq (vqtype_inter_vq (Ap, ep) (Aqs, eqs)) (Aqse, eqse)).
apply Project_vE_imp; try assumption.

4: { unfold subsumpImp_vqtype. unfold vqtype_inter_vq.
intros a ea HIn. simpl in HIn. 
rewrite Htrue_efst in HIn.

apply In_InAtt_fstVatt in HIn as HInAtt. simpl in HInAtt.
apply InAtt_vatts_inter in HInAtt. destruct HInAtt as [HInAttAp HInAttAqs].
apply  InAtt_In_exfexp. assumption. }
 
2: { rewrite <- Htrue_efst. assumption. }
2: { unfold vqtype_inter_vq. simpl. simpl in *.
     apply NoDupAtt_vatts_inter; assumption. }

all: try (apply NoDupAttvQ_ImptoExp; assumption).

}

{


}

Admitted.

Lemma ImpType_implies_ExpType e S q A: 
  { e , S |- [q]S | A }  -> 
  exists A', { e , S |= [q]S | A' }. 
Proof. 
generalize dependent A.
generalize dependent e.
induction q; destruct A as (A, ea);
intros HImp. 

{ 

destruct v as (rn, (A_, e_)).
simpl in HImp. simpl.
inversion HImp; subst. admit. }

{ simpl in HImp. simpl.

destruct (vtypeImpNOTC (litB true) S ([q] S)) as (Aqs, eqs) eqn:HqST.
exists (). apply Project_vE.

exists (A, ea). inversion HImp; subst. 
assert (HQe: addannot (vatts_inter (vatts_inter (fst a) Aqs) A', (snd a /\(F) eqs)) e'
= (vatts_inter (vatts_inter (fst a) Aqs) A', (snd a /\(F) eqs) /\(F) e')).
unfold addannot. simpl. reflexivity. rewrite <- HQe.

Admitted.

Lemma ImpQ_ImpType_Equiv_ExpQ_ExpType e S q A A': 
  { e , S |-  q   | A }  -> 
  { e , S |= [q]S | A' } -> 
   A =T= A'.
Proof. intros HImp HExp. 
apply ImpQ_ImpType_implies_ExpQ_ImpType in HImp as HImpExp.
destruct HImpExp as [A'' HImpExp].

apply ImpQ_ImpType_Equiv_ExpQ_ImpType with (A':=A'') in HImp; try assumption.
apply ExpQ_ImpType_Equiv_ExpQ_ExpType with (A :=A'') in HExp; try assumption.

transitivity (A''); assumption. Search sublist. 

Qed.

Lemma ImpQ_ImpType_implies_ExpQ_ExpType e S q A: 
  { e , S |-  q   | A }  -> 
  exists A', { e , S |= [q]S | A' }.
Proof. intros HImpQImpT.
apply ImpQ_ImpType_implies_ExpQ_ImpType in HImpQImpT.
destruct HImpQImpT as [A'' HExpQImpT].
apply ImpType_implies_ExpType in HExpQImpT.
destruct HExpQImpT as [A' HExpQExpT].
exists A'. assumption.
Qed.


(** IMPORTANT :: Below can be proved as well
general form of above theorem

Lemma ImpType_Equiv_ExpType e S q A A': 
  { e , S |- q | A }  -> 
  { e , S |= q | A' } -> 
   A =T= A'. *)

(* Proof. 
generalize dependent A'.
generalize dependent A.
generalize dependent e.
induction q; destruct A as (A, ea); 
destruct A' as (A', ea');
intros HImp HExp.

{

inversion HImp as [eImp SImp HndpRSImp HndpASImp 
                   rnImp A_Imp A'Imp HndpA'Imp e_Imp e'Imp 
                   HInVRImp HsatImp |
                   | | | ]; subst.
inversion HExp as [eExp SExp HndpRSExp HndpASExp 
                   rnExp AExp HndpA'Exp e'Exp 
                   HInVRExp HsatExp|
                   | | | ]; subst.

apply InVR_findVR in HInVRExp
as HInFindExp; try assumption.

apply InVR_findVR in HInVRImp
as HInFindImp; try assumption.

rewrite HInFindExp in HInFindImp.
inversion HInFindImp; subst.

rewrite not_sat_not_prop in HsatExp. 
rewrite <- sat_taut_comp in HsatExp. 

unfold equiv_vqtype. simpl.
split. 
(* =va= *)reflexivity. 

(* =e= *)simpl_equivE. 
destruct (E[[ ea']] c) eqn:Hea'.
(* (E[[ ea']] c) = true  *) apply HsatExp in Hea'. rewrite Hea'. eauto.
(* (E[[ ea']] c) = false *) eauto.
}

{
inversion HImp as [|
                   eImp SImp HndpRSImp HndpASImp vqImp HndpvQImp
                   e'Imp A'Imp HndpAA'Imp QImp HndpQImp
                   HqImp HsbsmpImp | | | ]; subst.
inversion HExp as [|
                   eExp SExp HndpRSExp HndpASExp vqExp HndpvQExp
                   e'Exp A'Exp HndpAA'Exp QExp HndpQExp
                   HqExp HsbsmpExp| | | ]; subst.

destruct a as (Ap, ep).
simpl in HImp. simpl in HExp. simpl.
apply (IHq _ _ _ HqImp) in HqExp as IHqEquiv.
unfold equiv_vqtype in IHqEquiv;
simpl in IHqEquiv. destruct IHqEquiv as [IHqA IHqe].

Locate equiv_sublist.
admit.
}


Admitted.

*)

(*

all: inversion HImp as
[ | | e0 S0 f0 HnS b n 
      A1 HnA1 e1 A2 HnA2 e2 
      Hq1 Hq2 
    | e0 S0 HnS b n 
      A1 HnA1 e1 A2 HnA2 e2 
      Hq1 Hq2              | ]  subst;
simpl in HExp; inversion HExp as
[ | | e0 S0 f0 HnSs b n 
      A1s HnA1s e1s A2s HnA2s e2s 
      Hq1s Hq2s
    | e0 S0 HnSs b n 
      A1s HnA1s e1s A2s HnA2s e2s 
      Hq1s Hq2s              | ]; subst.
apply IHq1 with (A':=(A1s, e1s)) in Hq1;
apply IHq2 with (A':=(A2s, e2s)) in Hq2;
try (assumption);
unfold equiv_vqtype in Hq1;
unfold equiv_vqtype in Hq2;
simpl in Hq1; simpl in Hq2;
destruct Hq1 as [Hq1A Hq1e];
destruct Hq2 as [Hq2A Hq2e];
unfold equiv_vqtype; simpl;
split; try (apply vatts_union_equiv;
try (assumption));
unfold equivE; intro ;
simpl; rewrite Hq1e, Hq2e;
reflexivity).

*)

(* Lemma contex_intro q S Aqs Aqs' eqs eqs' e: 
vtypeImpNOTC (litB true) S ([q] S) = (Aqs, eqs)
-> vtypeImpNOTC e S ([q] S) = (Aqs', eqs')->
Aqs = Aqs'  /\ eqs' =e= (eqs /\(F) e). 





intros H1 H2.
simpl. generalize dependent Aqs'.
generalize dependent eqs'.
generalize dependent Aqs. 
generalize dependent eqs.
 induction q.
- intros. destruct v as (rn, (Av, ev)).
simpl in H1. destruct (findVR rn S) as (rn',(Av', ev')) eqn: Hf.
unfold getvs, getf in H1. simpl in H1.
simpl in H2. rewrite Hf in H2. unfold getvs, getf in H2.
simpl in H2. unfold vqtype_inter_vq in H1.
simpl in H1. unfold vqtype_inter_vq in H2.
simpl in H2.  inversion H1; subst. 
inversion H2; subst. split.  reflexivity.
unfold equivE. intro c. simpl.
rewrite andb_assoc. rewrite andb_comm.
rewrite <- andb_assoc. reflexivity.
- admit.
- intros. simpl in H1. simpl in H2. 

destruct (vtypeImpNOTC (litB true) S ([q] S)) as (A', e')
eqn: Htrue.  simpl in H2. destruct (vtypeImpNOTC e S ([q] S)) 
as (A'', e'') eqn: He. simpl in H1.
rewrite Htrue in H1. destruct a as (Q, eq).
unfold vqtype_inter_vq in H1. simpl in H1.
unfold vqtype_inter_vq in H2. simpl in H2.

specialize IHq with (Aqs:=A') (eqs:=e')
(Aqs':=A'') (eqs':=e''). simpl in IHq.
assert (HAe: A' = A'' /\ e'' =e= (e' /\(F) e)).
apply IHq. reflexivity. reflexivity.
destruct HAe. rewrite H in H1.
rewrite H in H2. inversion H1.
inversion H2. split. reflexivity.
unfold equivE. unfold equivE in H0.
intro c. specialize H0 with c.
simpl. rewrite H0. simpl. 
rewrite andb_assoc. reflexivity.

Admitted.*)


 

(*

Lemma contex_intro S q A e A' e': 
  { e ,         S |- q | A  }  -> 
  { e /\(F) e', S |- q | A' } -> 
  (A ^^ e') =T= A'.
Proof. generalize dependent e.
 generalize dependent A.
 generalize dependent A'.
induction q. 
+ admit. + admit. + admit.
+ intros A A' e Ht He.
inversion Ht; subst.
inversion He; subst.
unfold equiv_vqtype.
simpl. 
specialize IHq1 with (e:=litB true /\(F) f)
(A':=(A1, e1)) as H5'.
specialize IHq1 with (e:=e /\(F) f)
(A':=(A0, e3)) as H7'.


intros Ht He. generalize dependent A.

induction He. + admit. + admit. +
intros A'' Ht; inversion Ht; subst. 
+ apply InVR_findVR in H.
apply InVR_findVR in H7.
rewrite H in H7. inversion H7; subst.
unfold equiv_vqtype. all: try(assumption).
split.
++ simpl. reflexivity.
++ simpl. unfold equivE.
simpl. intros. apply andb_comm.


+ specialize IHHe with (A'0, e'0).
apply IHHe in H4. unfold equiv_vqtype in H4.
simpl in H4. destruct H4.
unfold vqtype_inter_vq. 
unfold equiv_vqtype. simpl.
split. 
++ apply equiv_vatts_inter with (A:= fst Q) in H0.
assumption. 
++ simpl. unfold equivE. intros. simpl.
unfold equivE in H1. rewrite <- H1.
simpl. rewrite andb_assoc. reflexivity.

+ 
specialize IHHe1 with (A0, e3).
specialize IHHe2 with (A3, e4).

Admitted.

*)

(*

all: try(assumption).

pose (NoDupAtt_vtypeImpNOTC ) as Hndp.
specialize Hndp with (e:=((e /\(F) e') /\(F) ~(F) f)) (vs:= S) (vq:=q2)
as HnAq2'.

(* inversion H; subst. unfold equiv_vqtype.
simpl. split. simpl in H1. rewrite <-H1.
inversion Hefq1; subst. simpl in H3. 
inversion Hefq2; subst. simpl in H5.
apply vatts_union_equiv. all: try(assumption).
reflexivity. }

all: try(assumption); try(reflexivity).
rewrite H0. unfold equivE. intro c.
inversion H; subst. simpl. symmetry. 
rewrite andb_orb_distrib_l.
reflexivity. 

+ admit.
 
+ intros. simpl in H.

destruct (vtypeImpNOTC e S q1) as (A1, e1) eqn: Hq1.
destruct (vtypeImpNOTC e S q2) as (A2, e2) eqn: Hq2.
apply IHq1 with (e':= e') (eq':= (e1 /\(F) e')) in Hq1.
apply IHq2 with (e':= e') (eq':= (e2 /\(F) e')) in Hq2.
inversion H; subst.
apply (contex_equiv_NOTC) with (e1:= (e /\(F) e'))
(f1:= (eq0 /\(F) e')).
3: {simpl. rewrite Hq1, Hq2. reflexivity.
} all: try (rewrite H0) ; try(reflexivity).
*)
*)

(*Lemma contex_equiv e1 e2 S q A f1 f2:
   e1 =e= e2 ->   f1 =e= f2 ->
 { e1 ,         S |- q | (A, f1)  }  -> 

 { e2 ,         S |- q | (A, f2)  } . 
Proof. 
intros Heq He1 He2.
Admitted.

Lemma contex_intro e S q Aq eq eq' e': 
  { e ,         S |- q | (Aq, eq  ) }  -> 
    eq' =e= (eq /\(F) e') ->
  { e /\(F) e', S |- q | (Aq, eq') }.
Proof. 
generalize dependent e.
 generalize dependent Aq.
 generalize dependent eq. generalize dependent eq'.
generalize dependent e'.
induction q. + admit. + admit. 
+ intros. inversion H; subst.
eapply IHq1 with (e':= e')(eq':= (e1 /\(F) e')) in H5.
eapply IHq2 with (e':= e')(eq':= (e2 /\(F) e')) in H9.
(* context re-ordering to apply Choice_vE_imp *)
assert (Hr: (((e /\(F) f) /\(F) e') =e= ((e /\(F) e') /\(F) f))/\
(((e /\(F) ~(F) f) /\(F) e') =e= ((e /\(F) e') /\(F) ~(F) f))).
split. all: try (unfold equivE; simpl; intro; rewrite <- andb_assoc;
rewrite andb_comm with (b2:=(E[[ e']] c));
rewrite andb_assoc; reflexivity). 
destruct Hr as [Hr1 Hr2]. 
eapply (contex_equiv) with (A:=A1) (q:= q1)
(S:=S) (f1:= (e1 /\(F) e')) (f2:= (e1 /\(F) e')) in Hr1.
eapply (contex_equiv) with (A:=A2) (q:= q2)
(S:=S) (f1:= (e2 /\(F) e')) (f2:= (e2 /\(F) e')) in Hr2.
all: try(assumption); try(reflexivity).
(* apply Choice_vE_imp rule *)
eapply Choice_vE_imp with (vq1:=q1) (A1:=A1) (e1:=e1/\(F)e') in Hr2. 
all: try(assumption).
simpl in Hr2.
unfold vqtype_union_vq in Hr2.
simpl in Hr2. 
apply (contex_equiv) with (e1:= (e /\(F) e'))
(f1:= (e1 /\(F) e' \/(F) e2 /\(F) e')).
all: try(assumption); try(reflexivity).
rewrite H0. unfold equivE.
intro. simpl. Search ((_||_)&&_).
rewrite andb_orb_distrib_l. reflexivity.

(*apply vtypeImpNOTC_correct in Hr1.
apply vtypeImpNOTC_correct in Hr2.
apply vtypeImpNOTC_correct in H6.
apply vtypeImpNOTC_correct in H11.
rewrite Hr1 in H6. rewrite Hr2 in H11.
inversion H6; subst. inversion H11; subst.
simpl. split. reflexivity.
unfold equivE. intro. simpl.
symmetry. rewrite andb_comm. 
rewrite andb_orb_distrib_l.
reflexivity.
all: try(assumption); try(reflexivity).*)



Admitted.*)




