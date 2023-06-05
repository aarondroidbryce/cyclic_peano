From Cyclic_PA.Maths Require Import naturals.
From Cyclic_PA.Maths Require Import ordinals.
From Cyclic_PA.Maths Require Import lists.
From Cyclic_PA.Logic Require Import definitions.
From Cyclic_PA.Logic Require Import fol.
From Cyclic_PA.Logic Require Import PA_cyclic.
Require Import Lia.
Require Import List.
Import ListNotations.

Inductive ptree : Type :=
| node : forall (a : formula), ptree

| deg_up : forall (d' : nat) (P' : ptree), ptree

| ord_up : forall (beta : ord) (P' : ptree), ptree

| exchange_ab : forall (a b : formula) (d : nat) (alpha : ord) (P' : ptree), ptree

| exchange_cab : forall (c a b : formula) (d : nat) (alpha : ord) (P' : ptree), ptree

| exchange_abd : forall (a b d : formula) (d : nat) (alpha : ord) (P' : ptree), ptree

| exchange_cabd : forall (c a b d : formula) (d : nat) (alpha : ord) (P' : ptree), ptree

| contraction_a : forall (a : formula) (d : nat) (alpha : ord) (P' : ptree), ptree

| contraction_ad : forall (a d : formula) (d : nat) (alpha : ord) (P' : ptree), ptree

| negation_a : forall (a : formula) (d : nat) (alpha : ord) (P' : ptree), ptree

| negation_ad :  forall (a d : formula) (d : nat) (alpha : ord) (P' : ptree), ptree

| quantification_a :  forall (a : formula) (m : nat) (t : c_term) (d : nat) (alpha : ord) (P' : ptree), ptree

| quantification_ad : forall (a d : formula) (m : nat) (t : c_term) (d : nat) (alpha : ord) (P' : ptree), ptree

| weakening_ad : forall (a d : formula) (d : nat) (alpha : ord) (P' : ptree), ptree

| demorgan_ab : forall (a b : formula) (d1 d2 : nat) (alpha1 alpha2 : ord) (P1 P2 : ptree), ptree

| demorgan_abd : forall (a b d : formula) (d1 d2 : nat) (alpha1 alpha2 : ord) (P1 P2 : ptree), ptree

| cut_ca : forall (c a : formula) (d1 d2 : nat) (alpha1 alpha2 : ord) (P1 P2 : ptree), ptree

| cut_ad : forall (a d : formula) (d1 d2 : nat) (alpha1 alpha2 : ord) (P1 P2 : ptree), ptree

| cut_cad : forall (c a d : formula) (d1 d2 : nat) (alpha1 alpha2 : ord) (P1 P2 : ptree), ptree

| loop_a : forall (a : formula) (n d1 d2 : nat) (alpha1 alpha2 : ord) (P1 P2 : ptree), ptree

| loop_ca : forall (c a : formula) (n d1 d2 : nat) (alpha1 alpha2 : ord) (P1 P2 : ptree), ptree.

Fixpoint ptree_formula (P : ptree) : formula :=
match P with
| deg_up d P' => ptree_formula P'

| ord_up alpha P' => ptree_formula P'

| node A => A

| exchange_ab A B d alpha P' => lor B A

| exchange_cab C A B d alpha P' => lor (lor C B) A

| exchange_abd A B D d alpha P' => lor (lor B A) D

| exchange_cabd C A B D d alpha P' => lor (lor (lor C B) A) D

| contraction_a A d alpha P' => A

| contraction_ad A D d alpha P' => lor A D

| weakening_ad A D d alpha P' => lor A D

| demorgan_ab A B d1 d2 alpha1 alpha2 P1 P2 => neg (lor A B)

| demorgan_abd A B D d1 d2 alpha1 alpha2 P1 P2 => lor (neg (lor A B)) D

| negation_a A d alpha P' => neg (neg A)

| negation_ad A D d alpha P' => lor (neg (neg A)) D

| quantification_a A n t d alpha P' => neg (univ n A)

| quantification_ad A D n t d alpha P' => lor (neg (univ n A)) D

| loop_a A n d1 d2 alpha1 alpha2 P1 P2 => (univ n A)

| loop_ca C A n d1 d2 alpha1 alpha2 P1 P2 => lor C (univ n A)

| cut_ca C A d1 d2 alpha1 alpha2 P1 P2 => C

| cut_ad A D d1 d2 alpha1 alpha2 P1 P2 => D

| cut_cad C A D d1 d2 alpha1 alpha2 P1 P2 => lor C D
end.


Fixpoint ptree_deg (P : ptree) : nat :=
match P with
| deg_up d P' => d

| ord_up alpha P' => ptree_deg P'

| node A => 0

| exchange_ab A B d alpha P' => d

| exchange_cab E A B d alpha P' => d

| exchange_abd A B D d alpha P' => d

| exchange_cabd E A B D d alpha P' => d

| contraction_a A d alpha P' => d

| contraction_ad A D d alpha P' => d

| weakening_ad A D d alpha P' => d

| demorgan_ab A B d1 d2 alpha1 alpha2 P1 P2 => max d1 d2

| demorgan_abd A B D d1 d2 alpha1 alpha2 P1 P2 => max d1 d2

| negation_a A d alpha P' => d

| negation_ad A D d alpha P' => d

| quantification_a A n t d alpha P' => d

| quantification_ad A D n t d alpha P' => d

| loop_a A n d1 d2 alpha1 alpha2 P1 P2 => max d1 d2

| loop_ca A D n d1 d2 alpha1 alpha2 P1 P2 => max d1 d2

| cut_ca E A d1 d2 alpha1 alpha2 P1 P2 => max (max d1 d2) (num_conn (neg A))

| cut_ad A D d1 d2 alpha1 alpha2 P1 P2 => max (max d1 d2) (num_conn (neg A))

| cut_cad E A D d1 d2 alpha1 alpha2 P1 P2 => max (max d1 d2) (num_conn (neg A))
end.

Fixpoint ptree_ord (P : ptree) : ord :=
match P with
| deg_up d P' => ptree_ord P'

| ord_up alpha P' => alpha

| node A => Zero

| exchange_ab A B d alpha P' => alpha

| exchange_cab E A B d alpha P' => alpha

| exchange_abd A B D d alpha P' => alpha

| exchange_cabd E A B D d alpha P' => alpha

| contraction_a A d alpha P' => alpha

| contraction_ad A D d alpha P' => alpha

| weakening_ad A D d alpha P' => (ord_succ alpha)

| demorgan_ab A B d1 d2 alpha1 alpha2 P1 P2 => ord_succ (ord_max alpha1 alpha2)

| demorgan_abd A B D d1 d2 alpha1 alpha2 P1 P2 => ord_succ (ord_max alpha1 alpha2)

| negation_a A d alpha P' => ord_succ alpha

| negation_ad A D d alpha P' => ord_succ alpha

| quantification_a A n t d alpha P' => ord_succ alpha

| quantification_ad A D n t d alpha P' => ord_succ alpha

| loop_a A n d1 d2 alpha1 alpha2 P1 P2 => ord_succ (ord_add alpha1 (ord_mult alpha2 (wcon (wcon Zero 0 Zero) 0 Zero)))

| loop_ca C A n d1 d2 alpha1 alpha2 P1 P2 => ord_succ (ord_add alpha1 (ord_mult alpha2 (wcon (wcon Zero 0 Zero) 0 Zero)))

| cut_ca E A d1 d2 alpha1 alpha2 P1 P2 => ord_succ (ord_max alpha1 alpha2)

| cut_ad A D d1 d2 alpha1 alpha2 P1 P2 => ord_succ (ord_succ (ord_max alpha1 alpha2))

| cut_cad E A D d1 d2 alpha1 alpha2 P1 P2 => ord_succ (ord_max alpha1 alpha2)
end.

Fixpoint node_extract (P : ptree) : list formula :=
match P with
| deg_up d P' => node_extract P'

| ord_up alpha P' => node_extract P'

| node A => [A]

| exchange_ab A B d alpha P' => node_extract P'

| exchange_cab C A B d alpha P' => node_extract P'

| exchange_abd A B D d alpha P' => node_extract P'

| exchange_cabd C A B D d alpha P' => node_extract P'

| contraction_a A d alpha P' => node_extract P'

| contraction_ad A D d alpha P' => node_extract P'

| weakening_ad A D d alpha P' => node_extract P'

| demorgan_ab A B d1 d2 alpha1 alpha2 P1 P2 => node_extract P1 ++ node_extract P2

| demorgan_abd A B D d1 d2 alpha1 alpha2 P1 P2 => node_extract P1 ++ node_extract P2

| negation_a A d alpha P' => node_extract P'

| negation_ad A D d alpha P' => node_extract P'

| quantification_a A n t d alpha P' => node_extract P'

| quantification_ad A D n t d alpha P' => node_extract P'

| loop_a A n d1 d2 alpha1 alpha2 P1 P2 => (remove form_eq_dec A (node_extract P2)) ++ node_extract P1

| loop_ca C A n d1 d2 alpha1 alpha2 P1 P2 =>  (remove form_eq_dec (lor C A) (node_extract P2)) ++ node_extract P1

| cut_ca C A d1 d2 alpha1 alpha2 P1 P2 => node_extract P1 ++ node_extract P2

| cut_ad A D d1 d2 alpha1 alpha2 P1 P2 => node_extract P1 ++ node_extract P2

| cut_cad C A D d1 d2 alpha1 alpha2 P1 P2 => node_extract P1 ++ node_extract P2
end.

Fixpoint struct_valid (P : ptree) : Type :=
match P with
| deg_up d P' => (struct_valid P') * (d > ptree_deg P')

| ord_up alpha P' => (struct_valid P') * (ord_lt (ptree_ord P') alpha) * (nf alpha)

| node A => (true = true)

| exchange_ab A B d alpha P' =>
    (ptree_formula P' = lor A B) * (struct_valid P') *
    (d = ptree_deg P') * (alpha = ptree_ord P')

| exchange_cab E A B d alpha P' =>
    (ptree_formula P' = lor (lor E A) B) * (struct_valid P') *
    (d = ptree_deg P') * (alpha = ptree_ord P')

| exchange_abd A B D d alpha P' =>
    (ptree_formula P' = lor (lor A B) D) * (struct_valid P') *
    (d = ptree_deg P') * (alpha = ptree_ord P')

| exchange_cabd E A B D d alpha P' =>
    (ptree_formula P' = lor (lor (lor E A) B) D) * (struct_valid P') *
    (d = ptree_deg P') * (alpha = ptree_ord P')

| contraction_a A d alpha P' =>
    (ptree_formula P' = lor A A) * (struct_valid P') *
    (d = ptree_deg P') * (alpha = ptree_ord P')

| contraction_ad A D d alpha P' =>
    (ptree_formula P' = lor (lor A A) D) * (struct_valid P') *
    (d = ptree_deg P') * (alpha = ptree_ord P')

| weakening_ad A D d alpha P' =>
    (ptree_formula P' = D) * (struct_valid P') *
    (d = ptree_deg P') * (alpha = ptree_ord P') *
    (incl (free_list A) (flat_map free_list (node_extract P')))

| demorgan_ab A B d1 d2 alpha1 alpha2 P1 P2 =>
    (ptree_formula P1 = neg A) * (struct_valid P1) *
    (d1 = ptree_deg P1) * (alpha1 = ptree_ord P1) *
    (ptree_formula P2 = neg B) * (struct_valid P2) *
     (d2 = ptree_deg P2) * (alpha2 = ptree_ord P2)

| demorgan_abd A B D d1 d2 alpha1 alpha2 P1 P2 =>
    (ptree_formula P1 = lor (neg A) D) * (struct_valid P1) *
    (d1 = ptree_deg P1) * (alpha1 = ptree_ord P1) *
    (ptree_formula P2 = lor (neg B) D) * (struct_valid P2) *
    (d2 = ptree_deg P2) * (alpha2 = ptree_ord P2)

| negation_a A d alpha P' =>
    (ptree_formula P' = A) * (struct_valid P') *
    (d = ptree_deg P') * (alpha = ptree_ord P')

| negation_ad A D d alpha P' =>
    (ptree_formula P' = lor A D) * (struct_valid P') *
    (d = ptree_deg P') * (alpha = ptree_ord P')


| quantification_a A n t d alpha P' =>
    (ptree_formula P' = neg (substitution A n (projT1 t))) * (struct_valid P') *
    (d = ptree_deg P') * (alpha = ptree_ord P')

| quantification_ad A D n t d alpha P' =>
    (ptree_formula P' = lor (neg (substitution A n (projT1 t))) D) * (struct_valid P') *
    (d = ptree_deg P') * (alpha = ptree_ord P')

| loop_a A n d1 d2 alpha1 alpha2 P1 P2 =>
    (ptree_formula P1 = substitution A n zero) * (struct_valid P1) *
    (d1 = ptree_deg P1) * (alpha1 = ptree_ord P1) *
    (ptree_formula P2 = substitution A n (succ (var n))) * (struct_valid P2) *
    (d2 = ptree_deg P2) * (alpha2 = ptree_ord P2) *
    (In A (node_extract P2))

| loop_ca C A n d1 d2 alpha1 alpha2 P1 P2 =>
    (ptree_formula P1 = lor C (substitution A n zero)) * (struct_valid P1) *
    (d1 = ptree_deg P1) * (alpha1 = ptree_ord P1) * 
    (ptree_formula P2 = (lor C (substitution A n (succ (var n))))) * (struct_valid P2) *
    (d2 = ptree_deg P2) * (alpha2 = ptree_ord P2) *
    (In (lor C A) (node_extract P2))

| cut_ca E A d1 d2 alpha1 alpha2 P1 P2 =>
    (ptree_formula P1 = lor E A) * (struct_valid P1) *
    (d1 = ptree_deg P1) * (alpha1 = ptree_ord P1) * 
    (ptree_formula P2 = neg A) * (struct_valid P2) *
    (d2 = ptree_deg P2) * (alpha2 = ptree_ord P2)

| cut_ad A D d1 d2 alpha1 alpha2 P1 P2 =>
    (ptree_formula P1 = A) * (struct_valid P1) *
    (d1 = ptree_deg P1) * (alpha1 = ptree_ord P1) *
    (ptree_formula P2 = lor (neg A) D) * (struct_valid P2) *
    (d2 = ptree_deg P2) * (alpha2 = ptree_ord P2)

| cut_cad E A D d1 d2 alpha1 alpha2 P1 P2 =>
    (ptree_formula P1 = lor E A) * (struct_valid P1) *
    (d1 = ptree_deg P1) * (alpha1 = ptree_ord P1) *
    (ptree_formula P2 = lor (neg A) D) * (struct_valid P2) *
    (d2 = ptree_deg P2) * (alpha2 = ptree_ord P2)
end.

Definition valid (P : ptree) : Type := (struct_valid P) * (forall (A : formula), In A (node_extract P) -> PA_cyclic_axiom A = true).

Definition P_proves (P : ptree) (A : formula) (d : nat) (alpha : ord) : Type :=
  (ptree_formula P = A) * (valid P) *
  (d = ptree_deg P) * (alpha = ptree_ord P).

Definition provable (A : formula) (d : nat) (alpha : ord) : Type :=
  {P : ptree & P_proves P A d alpha}.

Lemma structural_pre_theorem :
    forall {A : formula} {d : nat} {alpha : ord} {L : list formula} (ST : PA_cyclic_pre A d alpha L),
        {P : ptree & prod (prod( prod (prod (ptree_formula P = A) (struct_valid P)) (d = ptree_deg P)) (alpha = ptree_ord P)) (node_extract P = L)}.
intros A d alpha L TS.
induction TS;
try destruct IHTS as [P [[[[PF PSV] PD] PO] PN]];
try destruct IHTS1 as [P1 [[[[P1F P1SV] P1D] P1H] P1N]];
try destruct IHTS2 as [P2 [[[[P2F P2SV] P2D] P2H] P2N]].
- exists (deg_up d' P). repeat split; auto. lia.
- exists (ord_up beta P). repeat split; auto. rewrite <- PO. auto.
- exists (node A). repeat split.
- exists (exchange_ab A B (ptree_deg P) alpha P). repeat split; auto.
- exists (exchange_cab C A B (ptree_deg P) alpha P). repeat split; auto.
- exists (exchange_abd A B D (ptree_deg P) alpha P). repeat split; auto.
- exists (exchange_cabd C A B D (ptree_deg P) alpha P). repeat split; auto.
- exists (contraction_a A (ptree_deg P) alpha P). repeat split; auto.
- exists (contraction_ad A D (ptree_deg P) alpha P). repeat split; auto.
- exists (weakening_ad A D (ptree_deg P) alpha P). repeat split; auto. rewrite PN. apply FLSub.
- exists (demorgan_ab A B (ptree_deg P1) (ptree_deg P2) alpha1 alpha2 P1 P2). repeat split; simpl; auto.  rewrite P1N,P2N. reflexivity.
- exists (demorgan_abd A B D (ptree_deg P1) (ptree_deg P2) alpha1 alpha2 P1 P2). repeat split; simpl; auto. rewrite P1N,P2N. reflexivity.
- exists (negation_a A (ptree_deg P) alpha P). repeat split; auto.
- exists (negation_ad A D (ptree_deg P) alpha P). repeat split; auto.
- exists (quantification_a A n c (ptree_deg P) alpha P). repeat split; auto.
- exists (quantification_ad A D n c (ptree_deg P) alpha P). repeat split; auto.
- exists (loop_a A n d1 d2 alpha1 alpha2 P1 P2).
  repeat split; simpl; auto.
  + rewrite P2N.
    apply i.
  + rewrite P2N,P1N.
    reflexivity.
- exists (loop_ca C A n d1 d2 alpha1 alpha2 P1 P2).
  repeat split; simpl; auto.
  + rewrite P2N.
    apply i.
  + rewrite P2N, P1N.
    reflexivity.
- exists (cut_ca C A (ptree_deg P1) (ptree_deg P2) alpha1 alpha2 P1 P2). repeat split; simpl; auto. rewrite P1N,P2N. reflexivity.
- exists (cut_ad A D (ptree_deg P1) (ptree_deg P2) alpha1 alpha2 P1 P2). repeat split; simpl; auto. rewrite P1N,P2N. reflexivity.
- exists (cut_cad C A D (ptree_deg P1) (ptree_deg P2) alpha1 alpha2 P1 P2). repeat split; simpl; auto. rewrite P1N,P2N. reflexivity.
Qed.

Lemma provable_theorem :
    forall (A : formula) (d : nat) (alpha : ord),
        PA_cyclic_theorem A d alpha -> provable A d alpha.
Proof.
intros A d alpha T.
apply true_theorem in T. 
destruct T as [L [TS TAX]].
unfold provable.
induction TS;
try destruct (IHTS TAX) as [P [[[PF [PSV PAX]] PD] PO]];
try destruct (IHTS1 (fun B INB => TAX B (proj2 (in_app_iff _ _ _) (or_introl INB)))) as [P1 [[[P1F [P1SV P1AX]] P1D] P1H]];
try destruct (IHTS2 (fun B INB => TAX B (proj2 (in_app_iff _ _ _) (or_intror INB)))) as [P2 [[[P2F [P2SV P2AX]] P2D] P2H]];
try rewrite PF in PFC;
try rewrite P1F in P1FC;
try rewrite P2F in P2FC;
repeat apply and_bool_prop in PFC as [PFC ?];
repeat apply and_bool_prop in P1FC as [P1FC ?];
repeat apply and_bool_prop in P2FC as [P2FC ?].
- exists (deg_up d' P).
  repeat split; auto. lia.
- exists (ord_up beta P).
  repeat split; auto.
  rewrite <- PO. auto.
- exists (node A).
  repeat split.
  + intros A' IN. inversion IN.
    * destruct H. apply TAX, or_introl, eq_refl.
    * inversion H.
- exists (exchange_ab A B (ptree_deg P) alpha P). repeat split; auto.
- exists (exchange_cab C A B (ptree_deg P) alpha P). repeat split; auto.
- exists (exchange_abd A B D (ptree_deg P) alpha P). repeat split; auto.
- exists (exchange_cabd C A B D (ptree_deg P) alpha P). repeat split; auto.
- exists (contraction_a A (ptree_deg P) alpha P). repeat split; auto.
- exists (contraction_ad A D (ptree_deg P) alpha P). repeat split; auto.
- pose proof (structural_pre_theorem TS) as [P' [[[[P'F P'SV] P'D] P'O] P'L]].
  exists (weakening_ad A D (ptree_deg P') alpha P'). repeat split; simpl; auto;
  try rewrite P'L.
  + apply FLSub.
  + apply TAX.
- exists (demorgan_ab A B (ptree_deg P1) (ptree_deg P2) alpha1 alpha2 P1 P2).
  repeat split; simpl; auto.
  + intros A' IN. apply in_app_iff in IN as [IN1 | IN2].
    * apply P1AX, IN1.
    * apply P2AX, IN2.
- exists (demorgan_abd A B D (ptree_deg P1) (ptree_deg P2) alpha1 alpha2 P1 P2).
  repeat split; simpl; auto.
  + intros A' IN. apply in_app_iff in IN as [IN1 | IN2].
    * apply P1AX, IN1.
    * apply P2AX, IN2.
- exists (negation_a A (ptree_deg P) alpha P). repeat split; auto.
- exists (negation_ad A D (ptree_deg P) alpha P). repeat split; auto.
- exists (quantification_a A n c (ptree_deg P) alpha P). repeat split; auto.
- exists (quantification_ad A D n c (ptree_deg P) alpha P). repeat split; auto.
- pose proof (structural_pre_theorem TS1) as [P1 [[[[P1F P1SV] P1D] P1O] P1L]].
  pose proof (structural_pre_theorem TS2) as [P2 [[[[P2F P2SV] P2D] P2O] P2L]].
  exists (loop_a A n d1 d2 alpha1 alpha2 P1 P2).
  repeat split; simpl; auto.
  + rewrite P2L.
    apply i.
  + intros B INB.
    rewrite P2L, P1L in INB.
    apply TAX, INB.
- pose proof (structural_pre_theorem TS1) as [P1 [[[[P1F P1SV] P1D] P1O] P1L]].
  pose proof (structural_pre_theorem TS2) as [P2 [[[[P2F P2SV] P2D] P2O] P2L]].
  exists (loop_ca C A n d1 d2 alpha1 alpha2 P1 P2).
  repeat split; simpl; auto.
  + rewrite P2L.
    apply i.
  + intros B INB.
    rewrite P2L, P1L in INB.
    apply TAX, INB.
- exists (cut_ca C A (ptree_deg P1) (ptree_deg P2) alpha1 alpha2 P1 P2).
  repeat split; simpl; auto.
  + intros A' IN. apply in_app_iff in IN as [IN1 | IN2].
    * apply P1AX, IN1.
    * apply P2AX, IN2.
- exists (cut_ad A D (ptree_deg P1) (ptree_deg P2) alpha1 alpha2 P1 P2).
  repeat split; simpl; auto.
  + intros A' IN. apply in_app_iff in IN as [IN1 | IN2].
    * apply P1AX, IN1.
    * apply P2AX, IN2.
- exists (cut_cad C A D (ptree_deg P1) (ptree_deg P2) alpha1 alpha2 P1 P2).
  repeat split; simpl; auto.
  + intros A' IN. apply in_app_iff in IN as [IN1 | IN2].
    * apply P1AX, IN1.
    * apply P2AX, IN2.
Qed.

Lemma pre_theorem_structural :
    forall (P : ptree) (PSV : struct_valid P),
        PA_cyclic_pre (ptree_formula P) (ptree_deg P) (ptree_ord P) (node_extract P).
Proof.
intros P PSV. induction P.

1 : destruct PSV as []. (*node*)
2 : destruct PSV as [PSV LT]. (*deg up*)
3 : destruct PSV as [[PSV LT] NO]. (*ord up*)

4-13 : destruct PSV as [[[PF PSV] PD] PO]. (*single hyp*)
14 : destruct PSV as [[[[PF PSV] PD] PO] CPF]. (*weakening*)
2-14 :  try rewrite PF,<-PD,<-PO in IHP;
        pose proof (IHP PSV) as P'.

15-19 : destruct PSV as [[[[[[[P1F P1SV] P1D] P1O] P2F] P2SV] P2D] P2O]. (*double hyp*)
20-21 : destruct PSV as [[[[[[[[P1F P1SV] P1D] P1O] P2F] P2SV] P2D] P2O] INA]. (*loop*)
15-21 : rewrite P1F,<-P1D,<-P1O in IHP1;
        rewrite P2F,<-P2D,<-P2O in IHP2;
        pose proof (IHP1 P1SV) as P1';
        pose proof (IHP2 P2SV) as P2'.

apply (axiom _).
apply (deg_incr _ _ P' LT).
apply (ord_incr _ _ P' LT NO).
apply (exchange1 P').
apply (exchange2 P').
apply (exchange3 P').
apply (exchange4 P').
apply (contraction1 P').
apply (contraction2 _ P').
apply (negation1 P').
apply (negation2 P').
apply (quantification1 P').
apply (quantification2 P').
apply (weakening _ CPF P').
apply (demorgan1 P1' P2').
apply (demorgan2 P1' P2').
apply (cut1 _ _ P1' P2').
apply (cut2 _ _ P1' P2').
apply (cut3 _ _ _ P1' P2').
1 : apply (loop1 _ _ INA (IHP1 P1SV) (IHP2 P2SV)).
1 : apply (loop2 _ _ INA (IHP1 P1SV) (IHP2 P2SV)).
Qed.

Lemma theorem_provable' :
    forall (P : ptree),
        valid P ->
            PA_cyclic_theorem (ptree_formula P) (ptree_deg P) (ptree_ord P).
Proof.
intros P [PSV PAX].
induction P.

1 : destruct PSV as []. (*node*)
2 : destruct PSV as [PSV LT]. (*deg up*)
3 : destruct PSV as [[PSV LT] NO]. (*ord up*)

4-13 : destruct PSV as [[[PF PSV] PD] PO]. (*single hyp*)
14 : destruct PSV as [[[[PF PSV] PD] PO] CPF]. (*weakening*)
2-13 :  try rewrite PF,<-PD,<-PO in IHP;
        pose proof (projT1 (projT2 (true_theorem (IHP PSV PAX)))) as P';
        pose proof (projT2 (projT2 (true_theorem (IHP PSV PAX)))) as PAX'.

15-19 : destruct PSV as [[[[[[[P1F P1SV] P1D] P1O] P2F] P2SV] P2D] P2O]. (*double hyp*)
20-21 : destruct PSV as [[[[[[[[P1F P1SV] P1D] P1O] P2F] P2SV] P2D] P2O] INA]. (*loop*)
15-21 : rewrite P1F, <- P1D, <- P1O in IHP1;
        rewrite P2F, <- P2D, <- P2O in IHP2;
        try pose proof (projT1 (projT2 (true_theorem (IHP1 P1SV (fun B INB => PAX B (proj2 (in_app_iff _ _ _) (or_introl INB))))))) as P1';
        try pose proof (projT1 (projT2 (true_theorem (IHP2 P2SV (fun B INB => PAX B (proj2 (in_app_iff _ _ _) (or_intror INB))))))) as P2';
        try pose proof (projT2 (projT2 (true_theorem (IHP1 P1SV (fun B INB => PAX B (proj2 (in_app_iff _ _ _) (or_introl INB))))))) as AX1';
        try pose proof (projT2 (projT2 (true_theorem (IHP2 P2SV (fun B INB => PAX B (proj2 (in_app_iff _ _ _) (or_intror INB))))))) as AX2';
        try fold node_extract in *.

1 : apply (prune (axiom _) PAX).
1 : apply (prune (deg_incr _ _ P' LT) PAX').
1 : apply (prune (ord_incr _ _ P' LT NO) PAX').
1 : apply (prune (exchange1 P') PAX').
1 : apply (prune (exchange2 P') PAX').
1 : apply (prune (exchange3 P') PAX').
1 : apply (prune (exchange4 P') PAX').
1 : apply (prune (contraction1 P') PAX').
1 : apply (prune (contraction2 _ P') PAX').
1 : apply (prune (negation1 P') PAX').
1 : apply (prune (negation2 P') PAX').
1 : apply (prune (quantification1 P') PAX').
1 : apply (prune (quantification2 P') PAX').
1 : rewrite <-PF, PD, PO.
    apply (prune (weakening _ CPF (pre_theorem_structural _ PSV)) PAX).
1 : refine (prune (demorgan1 P1' P2') _).
2 : refine (prune (demorgan2 P1' P2') _).
3 : refine (prune (cut1 _ _ P1' P2') _).
4 : refine (prune (cut2 _ _ P1' P2') _).
5 : refine (prune (cut3 _ _ _ P1' P2') _).

1-5 : intros B INB;
      apply in_app_iff in INB as [INB1 | INB2];
      try apply (AX1' _ INB1);
      apply (AX2' _ INB2).

1,2 : pose proof (pre_theorem_structural P1 P1SV) as P1';
      pose proof (pre_theorem_structural P2 P2SV) as P2';
      rewrite P1F, <-P1D, <-P1O in P1';
      rewrite P2F, <-P2D, <-P2O in P2'.

2 : apply (prune (loop2 _ _ INA P1' P2') PAX).

1 : apply (prune (loop1 _ _ INA P1' P2') PAX).
Qed.

Lemma theorem_provable :
    forall (A : formula) (d : nat) (alpha : ord),
        provable A d alpha ->
            PA_cyclic_theorem A d alpha.
Proof.
intros A d alpha [P [[[PF [PSV PAX]] PD] PO]].
rewrite <- PF, PD, PO.
apply (theorem_provable' _ (PSV, PAX)).
Qed.

Lemma ptree_ord_nf :
    forall (P : ptree),
        valid P ->
            nf (ptree_ord P).
Proof.
intros P PV.
pose proof (theorem_provable' _ PV) as PT.
apply (ord_nf _ PT).
Qed.

Lemma ptree_ord_nf_struct :
    forall (P : ptree),
        struct_valid P ->
            nf (ptree_ord P).
Proof.
intros P PV.
pose proof (pre_theorem_structural _ PV) as PT.
apply (ord_nf_pre _ PT).
Qed.

Lemma ptree_ord_nf_hyp :
    forall (alpha : ord) (P : ptree),
        alpha = ptree_ord P ->
            valid P ->
                nf alpha.
Proof.
intros alpha P EQ PV.
rewrite EQ.
apply ptree_ord_nf, PV.
Qed.

Lemma ptree_ord_nf_struct_hyp :
    forall (alpha : ord) (P : ptree),
        alpha = ptree_ord P ->
            struct_valid P ->
                nf alpha.
Proof.
intros alpha P EQ PV.
rewrite EQ.
apply ptree_ord_nf_struct, PV.
Qed.

Lemma associativity_1 :
    forall (C A B : formula) (d : nat) (alpha : ord),
        provable (lor (lor C A) B) d alpha ->
            provable (lor C (lor A B)) d alpha.
Proof.
intros C A B d alpha [P [[[PF [PSV PA]] PD] PO]].
exists (exchange_ab
          (lor A B) C (ptree_deg P) alpha
          (exchange_cab
              A C B (ptree_deg P) alpha
              (exchange_abd C A B (ptree_deg P) alpha P))).
repeat split; auto.
Qed.

Lemma associativity_2 :
    forall (C A B : formula) (d : nat) (alpha : ord),
        provable (lor C (lor A B)) d alpha ->
            provable (lor (lor C A) B) d alpha.
Proof.
intros C A B d alpha [P [[[PF [PSV PA]] PD] PO]].
exists (exchange_abd
            A C B (ptree_deg P) alpha
            (exchange_cab
                A B C (ptree_deg P) alpha
                (exchange_ab C (lor A B) (ptree_deg P) alpha P))).
repeat split; auto.
Qed.

Lemma provable_closed :
    forall (A : formula) (d : nat) (alpha : ord),
        provable A d alpha ->
            closed A = true.
Proof.
intros A d alpha PA.
apply (theorem_closed _ d alpha), theorem_provable, PA.
Qed.

Lemma provable_closed' :
    forall (P : ptree) (A : formula),
        valid P ->
            ptree_formula P = A ->
                closed A = true.
Proof.
intros P A [PSV PAX] PF.
pose (ptree_deg P) as d.
pose (ptree_ord P) as alpha.
apply (provable_closed _ d alpha).
exists P.
repeat split; auto.
Qed.

Lemma struct_non_empty_nodes : 
    forall (P : ptree),
            node_extract P <> [].
Proof.
induction P;
unfold node_extract;
fold node_extract.

all : try apply IHP.

1 : discriminate.

all : intros FAL;
      try case (closed c) eqn:CC;
      try case (closed (univ n a)) eqn:CuA;
      try inversion FAL;
      try apply app_eq_nil in FAL as [FAL1 FAL2];
      try apply (IHP1 FAL1);
      try apply (IHP1 FAL2);
      try apply (IHP2 FAL2).
Qed.

Lemma struct_node_sum_less_l {L : list formula} {P : ptree} :
    length L < length (L ++ (node_extract P)).
Proof.
rewrite app_length.
case (node_extract P) eqn:L2.
- destruct (struct_non_empty_nodes _ L2).
- unfold length;
  fold (@length formula).
  lia.
Qed.

Lemma struct_node_sum_less_r {L : list formula} {P : ptree} :
    length L < length ((node_extract P) ++ L).
Proof.
rewrite app_length.
case (node_extract P) eqn:L1.
- destruct (struct_non_empty_nodes _ L1).
- unfold length;
  fold (@length formula).
  lia.
Qed.

(*Could keep track of height, as exact increase of 1 if required*)

(*
Theorem macro_weakening :
    forall (P : ptree) (B C : formula),
        closed C = true ->
            struct_valid P ->
                In B (node_extract P) ->
                    {Q : ptree & (In (lor C B) (node_extract Q) * (ptree_formula Q = lor C (ptree_formula P)) * (ptree_deg Q = ptree_deg P) * struct_valid Q)%type}.
Proof.
intros P.
induction P;
intros B C CB PSV INB.

1 : destruct PSV. (*node*)
2 : destruct PSV as [PSV DU]. (*deg up*)
3 : destruct PSV as [[PSV OU] NO]. (*ord up*)

4-13 : destruct PSV as [[[PF PSV] PD] PO]. (*single hyp*)
14 : destruct PSV as [[[[PF PSV] PD] PO] CPF]. (*weakening*)

2-14 : destruct (IHP B C CB PSV INB) as [Q [[[INQ QF] QD] QSV]].

15-19 : destruct PSV as [[[[[[[P1F P1SV] P1D] P1O] P2F] P2SV] P2D] P2O]. (*double hyp*)
20-21 : destruct PSV as [[[[[[[[P1F P1SV] P1D] P1O] P2F] P2SV] P2D] P2O] INA]. (*loop*)

15-21 : unfold node_extract in INB; fold node_extract in INB;
        apply (@in_app_bor _ form_eq_dec) in INB as [INB1 | INB2];
        try destruct (IHP1 B C CB P1SV INB1) as [Q1 [[[INQ1 Q1F] Q1D] Q1SV]];
        try destruct (IHP1 B C CB P1SV INB2) as [Q1 [[[INQ1 Q1F] Q1D] Q1SV]];
        try destruct (IHP2 B C CB P2SV INB1) as [Q2 [[[INQ2 Q2F] Q2D] Q2SV]];
        try destruct (IHP2 B C CB P2SV INB2) as [Q2 [[[INQ2 Q2F] Q2D] Q2SV]].

1 : exists (node (lor C a)).
    repeat split.
    unfold node_extract in *.
    inversion INB as [EQ | FAL].
    destruct EQ.
    apply or_introl, eq_refl.
    inversion FAL.

1 : exists (deg_up d' Q).

2 : exists Q.

3 : exists (exchange_ab (lor b a) C d (ptree_ord Q)
            (exchange_abd a b C d (ptree_ord Q)
            (exchange_ab C (lor a b) d (ptree_ord Q) Q))).

4 : exists (exchange_ab (lor (lor c b) a) C d (ptree_ord Q)
            (exchange_cabd c a b C d (ptree_ord Q)
            (exchange_ab C (lor (lor c a) b) d (ptree_ord Q) Q))).

5 : exists (exchange_ab (lor (lor b a) d) C d0 (ptree_ord Q)
            (exchange_abd d (lor b a) C d0 (ptree_ord Q)
            (exchange_cab d C (lor b a) d0 (ptree_ord Q)
            (exchange_ab (lor b a) (lor d C) d0 (ptree_ord Q)
            (exchange_abd a b (lor d C) d0 (ptree_ord Q)
            (exchange_ab (lor d C) (lor a b) d0 (ptree_ord Q)
            (exchange_cab d (lor a b) C d0 (ptree_ord Q)
            (exchange_abd (lor a b) d C d0 (ptree_ord Q)
            (exchange_ab C (lor (lor a b) d) d0 (ptree_ord Q) Q))))))))).

6 : exists (exchange_ab (lor (lor (lor c b) a) d) C d0 (ptree_ord Q)
            (exchange_abd d (lor (lor c b) a) C d0 (ptree_ord Q)
            (exchange_cab d C (lor (lor c b) a) d0 (ptree_ord Q)
            (exchange_ab (lor (lor c b) a) (lor d C) d0 (ptree_ord Q)
                (exchange_cabd c a b (lor d C) d0 (ptree_ord Q)
            (exchange_ab (lor d C) (lor (lor c a) b) d0 (ptree_ord Q)
            (exchange_cab d (lor (lor c a) b) C d0 (ptree_ord Q)
            (exchange_abd (lor (lor c a) b) d C d0 (ptree_ord Q)
            (exchange_ab C (lor (lor (lor c a) b) d) d0 (ptree_ord Q) Q))))))))).

7 : exists (exchange_ab a C d (ptree_ord Q)
            (contraction_ad a C d (ptree_ord Q)
            (exchange_ab C (lor a a) d (ptree_ord Q) Q))).

8 : exists (exchange_ab (lor a d) C d0 (ptree_ord Q)
            (exchange_abd d a C d0 (ptree_ord Q)
            (exchange_cab d C a d0 (ptree_ord Q)
            (exchange_ab a (lor d C) d0 (ptree_ord Q)
                (contraction_ad a (lor d C) d0 (ptree_ord Q)
            (exchange_ab (lor d C) (lor a a ) d0 (ptree_ord Q)
            (exchange_cab d (lor a a) C d0 (ptree_ord Q)
            (exchange_abd (lor a a) d C d0 (ptree_ord Q)
            (exchange_ab C (lor (lor a a) d) d0 (ptree_ord Q) Q))))))))).

9 : exists (exchange_ab (neg (neg a)) C d (ord_succ (ptree_ord Q))
            (negation_ad a C d (ptree_ord Q)
            (exchange_ab C a d (ptree_ord Q) Q))).

10 : exists (exchange_ab (lor (neg (neg a)) d) C d0 (ord_succ (ptree_ord Q))
            (exchange_abd d (neg (neg a)) C d0 (ord_succ (ptree_ord Q))
            (exchange_cab d C (neg (neg a)) d0 (ord_succ (ptree_ord Q))
            (exchange_ab (neg (neg a)) (lor d C) d0 (ord_succ (ptree_ord Q))
                (negation_ad a (lor d C) d0 (ptree_ord Q)
            (exchange_ab (lor d C) a d0 (ptree_ord Q)
            (exchange_cab d a C d0 (ptree_ord Q)
            (exchange_abd a d C d0 (ptree_ord Q)
            (exchange_ab C (lor a d) d0 (ptree_ord Q) Q))))))))).

11 : exists (exchange_ab (neg (univ m a)) C d (ord_succ (ptree_ord Q))
            (quantification_ad a C m t d (ptree_ord Q)
            (exchange_ab C (neg (substitution a m (projT1 t))) d (ptree_ord Q) Q))).

12 : exists (exchange_ab (lor (neg (univ m a)) d) C d0 (ord_succ (ptree_ord Q))
            (exchange_abd d (neg (univ m a)) C d0 (ord_succ (ptree_ord Q))
            (exchange_cab d C (neg (univ m a)) d0 (ord_succ (ptree_ord Q))
            (exchange_ab (neg (univ m a)) (lor d C) d0 (ord_succ (ptree_ord Q))
                (quantification_ad a (lor d C) m t d0 (ptree_ord Q)
            (exchange_ab (lor d C) (neg (substitution a m (projT1 t))) d0 (ptree_ord Q)
            (exchange_cab d (neg (substitution a m (projT1 t))) C d0 (ptree_ord Q)
            (exchange_abd (neg (substitution a m (projT1 t))) d C d0 (ptree_ord Q)
            (exchange_ab C (lor (neg (substitution a m (projT1 t))) d) d0 (ptree_ord Q) Q))))))))).

13 : exists (exchange_ab (lor a d) C d0 (ord_succ (ptree_ord Q))
            (exchange_abd d a C d0 (ord_succ (ptree_ord Q))
            (exchange_cab d C a d0 (ord_succ (ptree_ord Q))
            (exchange_ab a (lor d C) d0 (ord_succ (ptree_ord Q))
                (weakening_ad a (lor d C) d0 (ptree_ord Q)
            (exchange_ab C d d0 (ptree_ord Q) Q)))))).

14 : exists (exchange_ab (neg (lor a b)) C (max d1 d2) (ord_succ (ord_max (ptree_ord Q1) (ord_succ alpha2)))
            (demorgan_abd a b C d1 d2 (ptree_ord Q1) (ord_succ alpha2)
                (exchange_ab C (neg a) d1 (ptree_ord Q1) Q1)
                (exchange_ab C (neg b) d2 (ord_succ alpha2)
                    (weakening_ad C (neg b) d2 alpha2 P2)))).

15 : exists (exchange_ab (neg (lor a b)) C (max d1 d2) (ord_succ (ord_max (ord_succ alpha1) (ptree_ord Q2)))
            (demorgan_abd a b C d1 d2 (ord_succ alpha1) (ptree_ord Q2)
                (exchange_ab C (neg a) d1 (ord_succ alpha1)
                    (weakening_ad C (neg a) d1 alpha1 P1))
                (exchange_ab C (neg b) d2 (ptree_ord Q2) Q2))).

16 : exists (exchange_ab (lor (neg (lor a b)) d) C (max d1 d2) (ord_succ (ord_max (ptree_ord Q1) (ord_succ alpha2)))
            (exchange_abd d (neg (lor a b)) C (max d1 d2) (ord_succ (ord_max (ptree_ord Q1) (ord_succ alpha2)))
            (exchange_cab d C (neg (lor a b)) (max d1 d2) (ord_succ (ord_max (ptree_ord Q1) (ord_succ alpha2)))
            (exchange_ab (neg (lor a b)) (lor d C) (max d1 d2) (ord_succ (ord_max (ptree_ord Q1) (ord_succ alpha2)))
                (demorgan_abd a b (lor d C) d1 d2 (ptree_ord Q1) (ord_succ alpha2)
                    (exchange_ab (lor d C) (neg a) d1 (ptree_ord Q1)
                        (exchange_cab d (neg a) C d1 (ptree_ord Q1)
                        (exchange_abd (neg a) d C d1 (ptree_ord Q1)
                        (exchange_ab C (lor (neg a) d) d1 (ptree_ord Q1) Q1))))
                    (exchange_ab (lor d C) (neg b) d2 (ord_succ alpha2)
                        (exchange_cab d (neg b) C d2 (ord_succ alpha2)
                        (exchange_abd (neg b) d C d2 (ord_succ alpha2)
                        (exchange_ab C (lor (neg b) d) d2 (ord_succ alpha2)
                        (weakening_ad C (lor (neg b) d) d2 alpha2 P2)))))))))).

17 : exists (exchange_ab (lor (neg (lor a b)) d) C (max d1 d2) (ord_succ (ord_max (ord_succ alpha1) (ptree_ord Q2)))
            (exchange_abd d (neg (lor a b)) C (max d1 d2) (ord_succ (ord_max (ord_succ alpha1) (ptree_ord Q2)))
            (exchange_cab d C (neg (lor a b)) (max d1 d2) (ord_succ (ord_max (ord_succ alpha1) (ptree_ord Q2)))
            (exchange_ab (neg (lor a b)) (lor d C) (max d1 d2) (ord_succ (ord_max (ord_succ alpha1) (ptree_ord Q2)))
                (demorgan_abd a b (lor d C) d1 d2 (ord_succ alpha1) (ptree_ord Q2)
                    (exchange_ab (lor d C) (neg a) d1 (ord_succ alpha1)
                        (exchange_cab d (neg a) C d1 (ord_succ alpha1)
                        (exchange_abd (neg a) d C d1 (ord_succ alpha1)
                        (exchange_ab C (lor (neg a) d) d1 (ord_succ alpha1)
                        (weakening_ad C (lor (neg a) d) d1 alpha1 P1)))))
                    (exchange_ab (lor d C) (neg b) d2 (ptree_ord Q2)
                        (exchange_cab d (neg b) C d2 (ptree_ord Q2)
                        ((exchange_abd (neg b) d C d2 (ptree_ord Q2)
                        (exchange_ab C (lor (neg b) d) d2 (ptree_ord Q2) Q2)))))))))).

18 : exists (cut_ca (lor C c) a d1 d2 (ptree_ord Q1) alpha2
                (exchange_abd c C a d1 (ptree_ord Q1)
                    (exchange_cab c a C d1 (ptree_ord Q1)
                    (exchange_ab C (lor c a) d1 (ptree_ord Q1) Q1)))
                P2).

19 : exists (exchange_ab c C (max (max d1 d2) (S (num_conn a))) (ord_succ (ord_max alpha1 (ptree_ord Q2)))
                (cut_cad c a C d1 d2 alpha1 (ptree_ord Q2)
                    P1
                    (exchange_ab C (neg a) d2 (ptree_ord Q2) Q2))).

20 : exists (cut_cad C a d d1 d2 (ptree_ord Q1) alpha2 Q1 P2).

21 : exists (exchange_ab d C (max (max d1 d2) (S (num_conn a))) (ord_succ (ord_succ (ord_max alpha1 (ptree_ord Q2))))
                (cut_ad a (lor d C) d1 d2 alpha1 (ptree_ord Q2)
                    P1
                    (exchange_ab (lor d C) (neg a) d2 (ptree_ord Q2)
                        (exchange_cab d (neg a) C d2 (ptree_ord Q2)
                        (exchange_abd (neg a) d C d2 (ptree_ord Q2)
                        (exchange_ab C (lor (neg a) d) d2 (ptree_ord Q2) Q2)))))).

22 : exists (exchange_ab (lor c d) C (max (max d1 d2) (S (num_conn a))) (ord_succ (ord_max (ptree_ord Q1) alpha2))
            (exchange_cab c C d (max (max d1 d2) (S (num_conn a))) (ord_succ (ord_max (ptree_ord Q1) alpha2))
            (exchange_abd C c d (max (max d1 d2) (S (num_conn a))) (ord_succ (ord_max (ptree_ord Q1) alpha2))
                (cut_cad (lor C c) a d d1 d2 (ptree_ord Q1) alpha2
                    (exchange_abd c C a d1 (ptree_ord Q1)
                        (exchange_cab c a C d1 (ptree_ord Q1)
                        (exchange_ab C (lor c a) d1 (ptree_ord Q1) Q1)))
                    P2)))).

23 : exists (exchange_ab (lor c d) C (max (max d1 d2) (S (num_conn a))) (ord_succ (ord_max alpha1 (ptree_ord Q2)))
            (exchange_abd d c C (max (max d1 d2) (S (num_conn a))) (ord_succ (ord_max alpha1 (ptree_ord Q2)))
            (exchange_cab d C c (max (max d1 d2) (S (num_conn a))) (ord_succ (ord_max alpha1 (ptree_ord Q2)))
            (exchange_ab c (lor d C) (max (max d1 d2) (S (num_conn a))) (ord_succ (ord_max alpha1 (ptree_ord Q2)))
                (cut_cad c a (lor d C) d1 d2 alpha1 (ptree_ord Q2)
                    P1
                    (exchange_ab (lor d C) (neg a) d2 (ptree_ord Q2)
                        (exchange_cab d (neg a) C d2 (ptree_ord Q2)
                        (exchange_abd (neg a) d C d2 (ptree_ord Q2)
                        (exchange_ab C (lor (neg a) d) d2 (ptree_ord Q2) Q2))))))))).

24 : exists P1.

25 : exists (loop_ca C a n d1 d2 (ptree_ord Q1) alpha2 Q1 P2).

26 : exists P1.

27 : exists (exchange_ab (lor c (univ n a)) C (max d1 d2) (ord_succ (ord_add (ptree_ord Q1) (ord_mult alpha2 (wcon (wcon Zero 0 Zero) 0 Zero))))
            (exchange_cab c C (univ n a) (max d1 d2) (ord_succ (ord_add (ptree_ord Q1) (ord_mult alpha2 (wcon (wcon Zero 0 Zero) 0 Zero))))
                (loop_ca (lor c C) a n d1 d2 (ptree_ord Q1) alpha2
                    (exchange_cab c (substitution a n zero) C d1 (ptree_ord Q1)
                        (exchange_ab C (lor c (substitution a n zero)) d1 (ptree_ord Q1) Q1))
                    P2))).
(*
(exchange_ab (lor d C) (neg a) d1 (ptree_ord Q1) (exchange_cab d (neg a) C d1 (ptree_ord Q1) ((exchange_abd (neg a) d C d1 (ptree_ord Q1) (exchange_ab C (lor (neg a)) d) d1 (ptree_ord Q1) Q1))))
*)

26 : admit.

24 : admit.


all : repeat split;
      try apply INQ;
      try apply QF;
      try apply Q1F;
      try apply Q2F;
      try apply QD;
      try apply Q1D;
      try apply Q2D;
      try apply QO;
      try apply Q1O;
      try apply Q2O;
      try apply QSV;
      try apply Q1SV;
      try apply Q2SV;
      try rewrite QO;
      try rewrite Q1O;
      try rewrite Q2O;
      try apply OU;
      try apply NO;
      try rewrite QD;
      try rewrite Q1D;
      try rewrite Q2D;
      try apply DU;
      try apply PF;
      try apply P1F;
      try apply P2F;
      try rewrite <- PF;
      try rewrite <- P1F;
      try rewrite <- P2F;
      try apply QF;
      try apply Q1F;
      try apply Q2F;
      try apply PD;
      try apply P1D;
      try apply P2D;
      try apply PO;
      try apply P1O;
      try apply P2O;
      try apply PSV;
      try apply P1SV;
      try apply P2SV;
      try reflexivity;
      unfold node_extract;
      fold node_extract;
      try apply in_or_app;
      try apply (or_introl INQ1);
      try apply (or_intror INQ1);
      try apply (or_intror INQ2);
      try rewrite (closed_free_list _ CB);
      try apply INA;
      try apply incl_nil_l.

      rewrite Q2F.
      rewrite P1F.
      rewrite P2F.
      reflexivity.

all :      simpl.

Qed.

*)

(*
Master destruct tactic.

1 : destruct PSV. (*node*)
2 : destruct PSV as [PSV DU]. (*deg up*)
3 : destruct PSV as [[PSV OU] NO]. (*ord up*)

4-13 : destruct PSV as [[[PF PSV] PD] PO]. (*single hyp*)
14 : destruct PSV as [[[[PF PSV] PD] PO] CPF]. (*weakening*)

15-19 : destruct PSV as [[[[[[[P1F P1SV] P1D] P1O] P2F] P2SV] P2D] P2O]. (*double hyp*)
20-21 : destruct PSV as [[[[[[[[P1F P1SV] P1D] P1O] P2F] P2SV] P2D] P2O] INA]. (*loop*)
*)