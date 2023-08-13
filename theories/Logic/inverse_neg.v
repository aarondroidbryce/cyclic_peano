From Cyclic_PA.Maths Require Import naturals.
From Cyclic_PA.Maths Require Import lists.
From Cyclic_PA.Maths Require Import ordinals.

From Cyclic_PA.Logic Require Import definitions.
From Cyclic_PA.Logic Require Import fol.
From Cyclic_PA.Logic Require Import proof_trees.
From Cyclic_PA.Logic Require Import substitute.
From Cyclic_PA.Logic Require Import PA_cyclic.

Require Import Coq.Arith.Wf_nat.

Require Import List.
Import ListNotations.

Require Import Lia.

Definition dub_neg_sub_formula (A E : formula) (S : subst_ind) : formula :=
  formula_sub_ind A (neg (neg E)) E S.

Lemma dub_neg_formula_free :
  forall (A E : formula) (S : subst_ind),
      free_list (dub_neg_sub_formula A E S) = free_list A.
Proof.
intros A E S.
unfold dub_neg_sub_formula, formula_sub_ind.
case (subst_ind_fit A S) eqn:FIT.
- apply formula_sub_ind_free_list.
  reflexivity.
- reflexivity.
Qed.

Lemma dub_neg_sub_formula_closed :
    forall (A : formula),
        forall (E : formula) (S : subst_ind),
            closed A = closed (dub_neg_sub_formula A E S).
Proof.
intros A E S.
case (closed A) eqn:CA.
- unfold dub_neg_sub_formula.
  symmetry.
  apply (formula_sub_ind_closed _ _ _ CA).
  unfold closed; fold closed.
  intros CE.
  apply CE.
- case (closed (dub_neg_sub_formula A E S)) eqn:CnA.
  + apply closed_free_list in CnA.
    rewrite dub_neg_formula_free in CnA.
    apply free_list_closed in CnA.
    rewrite CnA in CA.
    inversion CA.
  + reflexivity.
Qed.

Fixpoint dub_neg_sub_ptree_fit
  (P : ptree) (E : formula) (S : subst_ind) : ptree :=
match P, S with
| deg_up d P', _ => deg_up d (dub_neg_sub_ptree_fit P' E S)

| ord_up alpha P', _ => ord_up alpha (dub_neg_sub_ptree_fit P' E S)

| leaf_ex n P', _ => leaf_ex n (dub_neg_sub_ptree_fit P' E S)

| node A, _ => node (dub_neg_sub_formula A E S)

| exchange_ab A B d alpha P', lor_ind S_B S_A =>
    exchange_ab
      (dub_neg_sub_formula A E S_A)
      (dub_neg_sub_formula B E S_B)
      d alpha
      (dub_neg_sub_ptree_fit P' E (lor_ind S_A S_B))

| exchange_cab C A B d alpha P', lor_ind (lor_ind S_C S_B) S_A =>
    exchange_cab
      (dub_neg_sub_formula C E S_C)
      (dub_neg_sub_formula A E S_A)
      (dub_neg_sub_formula B E S_B)
      d alpha
      (dub_neg_sub_ptree_fit P' E (lor_ind (lor_ind S_C S_A) S_B))

| exchange_abd A B D d alpha P', lor_ind (lor_ind S_B S_A) S_D =>
    exchange_abd
      (dub_neg_sub_formula A E S_A)
      (dub_neg_sub_formula B E S_B)
      (dub_neg_sub_formula D E S_D)
      d alpha
      (dub_neg_sub_ptree_fit P' E (lor_ind (lor_ind S_A S_B) S_D))

| exchange_cabd C A B D d alpha P', lor_ind (lor_ind (lor_ind S_C S_B) S_A) S_D =>
    exchange_cabd
      (dub_neg_sub_formula C E S_C)
      (dub_neg_sub_formula A E S_A)
      (dub_neg_sub_formula B E S_B)
      (dub_neg_sub_formula D E S_D)
      d alpha
      (dub_neg_sub_ptree_fit P' E (lor_ind (lor_ind (lor_ind S_C S_A) S_B) S_D))

| contraction_a A d alpha P', _ =>
    contraction_a
      (dub_neg_sub_formula A E S)
      d alpha
      (dub_neg_sub_ptree_fit P' E (lor_ind S S))

| contraction_ad A D d alpha P', lor_ind S_A S_D =>
    contraction_ad
      (dub_neg_sub_formula A E S_A)
      (dub_neg_sub_formula D E S_D)
      d alpha
      (dub_neg_sub_ptree_fit P' E (lor_ind (lor_ind S_A S_A) S_D))

| weakening_ad A D d alpha P', lor_ind S_A S_D =>
    (weakening_ad
      (dub_neg_sub_formula A E S_A)
      (dub_neg_sub_formula D E S_D)
      d alpha
      (dub_neg_sub_ptree_fit P' E S_D))

| demorgan_ab A B d1 d2 alpha1 alpha2 P1 P2, _ => P

| demorgan_abd A B D d1 d2 alpha1 alpha2 P1 P2, lor_ind S_AB S_D =>
    demorgan_abd
      A B (dub_neg_sub_formula D E S_D) d1 d2 alpha1 alpha2
      (dub_neg_sub_ptree_fit P1 E (lor_ind (0) S_D))
      (dub_neg_sub_ptree_fit P2 E (lor_ind (0) S_D))

| negation_a A d alpha P', _ =>
    (match S, form_eqb A E with
    | (1), true => ord_up (ord_succ alpha) P'
    | _, _ => P
    end)

| negation_ad A D d alpha P', lor_ind S_A S_D =>
    (match S_A, form_eqb A E with
    | (1), true => ord_up (ord_succ alpha) (dub_neg_sub_ptree_fit P' E (lor_ind (non_target A) S_D))
    | _, _ => 
        negation_ad
          A
          (dub_neg_sub_formula D E S_D)
          d alpha
          (dub_neg_sub_ptree_fit P' E (lor_ind (non_target A) S_D))
    end)

| quantification_a A n t d alpha P', _ => P

| quantification_ad A D n t d alpha P', lor_ind S_A S_D =>
    quantification_ad
      A
      (dub_neg_sub_formula D E S_D)
      n t d alpha
      (dub_neg_sub_ptree_fit P' E (lor_ind (0) S_D))


| loop_a A n d1 d2 alpha1 alpha2 P1 P2, _ => P

| loop_ca C A n d1 d2 alpha1 alpha2 P1 P2, (lor_ind SC SA) =>
    loop_ca
      (dub_neg_sub_formula C E SC)
      A n d1 d2 alpha1 alpha2
      (dub_neg_sub_ptree_fit P1 E (lor_ind SC (non_target A)))
      (dub_neg_sub_ptree_fit P2 E (lor_ind SC (non_target A)))

| cut_ca C A d1 d2 alpha1 alpha2 P1 P2, _ =>
    cut_ca
      (dub_neg_sub_formula C E S)
      A d1 d2 alpha1 alpha2
      (dub_neg_sub_ptree_fit P1 E (lor_ind S (non_target A)))
      P2

| cut_ad A D d1 d2 alpha1 alpha2 P1 P2, _ =>
    cut_ad
      A (dub_neg_sub_formula D E S) d1 d2 alpha1 alpha2
      P1
      (dub_neg_sub_ptree_fit P2 E (lor_ind (0) S))

| cut_cad C A D d1 d2 alpha1 alpha2 P1 P2, lor_ind S_C S_D =>
    cut_cad
      (dub_neg_sub_formula C E S_C)
      A (dub_neg_sub_formula D E S_D) d1 d2 alpha1 alpha2
      (dub_neg_sub_ptree_fit P1 E (lor_ind S_C (non_target A)))
      (dub_neg_sub_ptree_fit P2 E (lor_ind (0) S_D))

| _, _ => P
end.

Fixpoint dub_neg_node_fit (P : ptree) (S : subst_ind) : list subst_ind :=
match P, S with
| deg_up d P', _ => dub_neg_node_fit P' S

| ord_up alpha P', _ => dub_neg_node_fit P' S

| leaf_ex n P', _ => bury (dub_neg_node_fit P' S) n

| node A, _ => [S]

| exchange_ab A B d alpha P', (lor_ind S_B S_A) => dub_neg_node_fit P' (lor_ind S_A S_B)

| exchange_cab C A B d alpha P', (lor_ind (lor_ind S_C S_B) S_A) => dub_neg_node_fit P' (lor_ind (lor_ind S_C S_A) S_B)

| exchange_abd A B D d alpha P', (lor_ind (lor_ind S_B S_A) S_D) => dub_neg_node_fit P' (lor_ind (lor_ind S_A S_B) S_D)

| exchange_cabd C A B D d alpha P', (lor_ind (lor_ind (lor_ind S_C S_B) S_A) S_D) => dub_neg_node_fit P' (lor_ind (lor_ind (lor_ind S_C S_A) S_B) S_D)

| contraction_a A d alpha P', _ => dub_neg_node_fit P' (lor_ind S S)

| contraction_ad A D d alpha P', (lor_ind S_A S_D) => dub_neg_node_fit P' (lor_ind (lor_ind S_A S_A) S_D)

| weakening_ad A D d alpha P', (lor_ind S_A S_D) => dub_neg_node_fit P' S_D

| demorgan_ab A B d1 d2 alpha1 alpha2 P1 P2, _ => dub_neg_node_fit P1 (0) ++ dub_neg_node_fit P2 (0)

| demorgan_abd A B D d1 d2 alpha1 alpha2 P1 P2, (lor_ind S_AB S_D) => dub_neg_node_fit P1 (lor_ind (0) S_D) ++ dub_neg_node_fit P2 (lor_ind (0) S_D)

| negation_a A d alpha P', _ => dub_neg_node_fit P' (non_target A)

| negation_ad A D d alpha P', (lor_ind S_A S_D) => dub_neg_node_fit P' (lor_ind (non_target A) S_D)

| quantification_a A n t d alpha P', _ => dub_neg_node_fit P' (0)

| quantification_ad A D n t d alpha P', (lor_ind S_A S_D) => dub_neg_node_fit P' (lor_ind (0) S_D)

| loop_a A n d1 d2 alpha1 alpha2 P1 P2, _ => tl (dub_neg_node_fit P2 (non_target A)) ++ dub_neg_node_fit P1 (non_target A)

| loop_ca C A n d1 d2 alpha1 alpha2 P1 P2, (lor_ind S_C S_A) => tl (dub_neg_node_fit P2 (lor_ind S_C (non_target A))) ++ dub_neg_node_fit P1 (lor_ind S_C (non_target A))

| cut_ca C A d1 d2 alpha1 alpha2 P1 P2, _ => dub_neg_node_fit P1 (lor_ind S (non_target A)) ++ dub_neg_node_fit P2 (0)

| cut_ad A D d1 d2 alpha1 alpha2 P1 P2, _ => dub_neg_node_fit P1 (non_target A) ++ dub_neg_node_fit P2 (lor_ind (0) S)

| cut_cad C A D d1 d2 alpha1 alpha2 P1 P2, (lor_ind S_C S_D) => dub_neg_node_fit P1 (lor_ind S_C (non_target A)) ++ dub_neg_node_fit P2 (lor_ind (0) S_D)

| _,_ => []
end.

Definition dub_neg_sub_ptree (P : ptree) (E : formula) (S : subst_ind) : ptree :=
match subst_ind_fit (ptree_formula P) S with
| false => P
| true => dub_neg_sub_ptree_fit P E S
end.

Definition dub_neg_node (P : ptree) (S : subst_ind) : list subst_ind :=
match subst_ind_fit (ptree_formula P) S with
| false => map non_target (node_extract P)
| true => dub_neg_node_fit P S
end.

(*
Fixpoint dub_neg_node_valid_fit (P : ptree) (S : subst_ind): Type :=
match P, S with
| deg_up d P', _ => (dub_neg_node_valid_fit P' S)

| ord_up alpha P', _ => (dub_neg_node_valid_fit P' S)

| leaf_ex n P', _ => (dub_neg_node_valid_fit P' S) * (n < length (node_extract P'))

| leaf_con P' , _ => (dub_neg_node_valid_fit P' S) * ({L : list subst_ind & {s : subst_ind & (dub_neg_node P' S) = s :: s :: L}})

| node A, _ => (true = true)

| exchange_ab A B d alpha P', (lor_ind S_B S_A) => (dub_neg_node_valid_fit P' (lor_ind S_A S_B))

| exchange_cab C A B d alpha P', (lor_ind (lor_ind S_C S_B) S_A) => (dub_neg_node_valid_fit P' (lor_ind (lor_ind S_C S_A) S_B))

| exchange_abd A B D d alpha P', (lor_ind (lor_ind S_B S_A) S_D) => (dub_neg_node_valid_fit P' (lor_ind (lor_ind S_A S_B) S_D))

| exchange_cabd C A B D d alpha P', (lor_ind (lor_ind (lor_ind S_C S_B) S_A) S_D) => (dub_neg_node_valid_fit P' (lor_ind (lor_ind (lor_ind S_C S_A) S_B) S_D))

| contraction_a A d alpha P', _ => (dub_neg_node_valid_fit P' (lor_ind S S))

| contraction_ad A D d alpha P', (lor_ind S_A S_D) => (dub_neg_node_valid_fit P' (lor_ind (lor_ind S_A S_A) S_D))

| weakening_ad A D d alpha P', (lor_ind S_A S_D) => (dub_neg_node_valid_fit P' S_D)

| demorgan_ab A B d1 d2 alpha1 alpha2 P1 P2, _ => (dub_neg_node_valid_fit P1 (0)) * (dub_neg_node_valid_fit P2 (0))

| demorgan_abd A B D d1 d2 alpha1 alpha2 P1 P2, (lor_ind S_AB S_D) => (dub_neg_node_valid_fit P1 (lor_ind (0) S_D)) * (dub_neg_node_valid_fit P2 (lor_ind (0) S_D))

| negation_a A d alpha P', _ => (dub_neg_node_valid_fit P' (non_target A))

| negation_ad A D d alpha P', (lor_ind S_A S_D) => (dub_neg_node_valid_fit P' (lor_ind (non_target A) S_D))

| quantification_a A n t d alpha P', _ => (dub_neg_node_valid_fit P' (0))

| quantification_ad A D n t d alpha P', (lor_ind S_A S_D) => (dub_neg_node_valid_fit P' (lor_ind (0) S_D))

| loop_a A n d1 d2 alpha1 alpha2 P1 P2, _ => (dub_neg_node_valid_fit P2 (non_target A)) * (dub_neg_node_valid_fit P1 (non_target A)) * ({L : list subst_ind & (non_target A) :: L = dub_neg_node P2 (non_target A)})

| loop_ca C A n d1 d2 alpha1 alpha2 P1 P2, (lor_ind S_C S_A) => (dub_neg_node_valid_fit P2 (lor_ind S_C (non_target A))) * (dub_neg_node_valid_fit P1 (lor_ind S_C (non_target A))) * ({L : list subst_ind & (lor_ind S_C (non_target A)) :: L = dub_neg_node P2 (lor_ind S_C (non_target A))})

| cut_ca C A d1 d2 alpha1 alpha2 P1 P2, _ => (dub_neg_node_valid_fit P1 (lor_ind S (non_target A))) * (dub_neg_node_valid_fit P2 (0))

| cut_ad A D d1 d2 alpha1 alpha2 P1 P2, _ => (dub_neg_node_valid_fit P1 (non_target A)) * (dub_neg_node_valid_fit P2 (lor_ind (0) S))

| cut_cad C A D d1 d2 alpha1 alpha2 P1 P2, (lor_ind S_C S_D) => (dub_neg_node_valid_fit P1 (lor_ind S_C (non_target A))) * (dub_neg_node_valid_fit P2 (lor_ind (0) S_D))

| _,_ => (false = true)
end.

Definition dub_neg_node_valid (P : ptree) (S : subst_ind) : Type :=
match subst_ind_fit (ptree_formula P) S with
| false => (false = true)
| true => dub_neg_node_valid_fit P S
end.
*)

Lemma dub_neg_ptree_formula_true :
    forall (P : ptree) (E : formula) (S : subst_ind),
        subst_ind_fit (ptree_formula P) S = true ->
            dub_neg_sub_ptree_fit P E S = dub_neg_sub_ptree P E S.
Proof. intros. unfold dub_neg_sub_ptree. destruct P; rewrite H; auto. Qed.

Lemma dub_neg_node_formula_true :
    forall (P : ptree) (S : subst_ind),
        subst_ind_fit (ptree_formula P) S = true ->
            dub_neg_node_fit P S = dub_neg_node P S.
Proof. intros. unfold dub_neg_node. rewrite H. reflexivity. Qed.

(*
Lemma dub_neg_node_valid_formula_true :
    forall (P : ptree) (S : subst_ind),
        subst_ind_fit (ptree_formula P) S = true ->
            dub_neg_node_valid_fit P S = dub_neg_node_valid P S.
Proof. intros. unfold dub_neg_node_valid. rewrite H. reflexivity. Qed.
*)

Lemma dub_neg_axiom_id :
    forall (A E : formula) (S : subst_ind),
        PA_cyclic_axiom A = true ->
            dub_neg_sub_formula A E S = A.
Proof.
intros A E S AX.
induction A;
inversion AX as [AX'];
unfold dub_neg_sub_formula, formula_sub_ind, formula_sub_ind_fit, form_eqb;
fold form_eqb;
case subst_ind_fit;
try reflexivity.
destruct A;
inversion AX as [AX''].
unfold form_eqb.
reflexivity.
Qed.

Lemma dub_neg_ptree_formula' : forall (P : ptree) (E : formula),
  struct_valid P ->
      forall (S : subst_ind),
          subst_ind_fit (ptree_formula P) S = true ->
              ptree_formula (dub_neg_sub_ptree P E S) =
                  dub_neg_sub_formula (ptree_formula P) E S.
Proof.
intros P E PSV.
induction P.

1 : destruct PSV. (*node*)
2 : destruct PSV as [PSV PL]. (*leaf exchange*)
3 : destruct PSV as [PSV DU]. (*deg up*)
4 : destruct PSV as [[PSV OU] NO]. (*ord up*)
5-14 : destruct PSV as [[[PF PSV] PD] PO]. (*single hyp*)
15 : destruct PSV as [[[[PF PSV] PD] PO] CPF]. (*weakening*)

16-20 : destruct PSV as [[[[[[[P1F P1SV] P1D] P1O] P2F] P2SV] P2D] P2O]. (*double hyp*)
21-22 : destruct PSV as [[[[[[[[[P1F P1SV] P1D] P1O] P2F] P2SV] P2D] P2O] [L P2N]] FREEA]. (*loop*)

all : intros S FS;
      unfold dub_neg_sub_ptree;
      try rewrite FS;
      unfold dub_neg_sub_ptree_fit;
      fold dub_neg_sub_ptree_fit;
      unfold ptree_formula in *;
      fold ptree_formula in *;
      try reflexivity.

1-3 : rewrite (dub_neg_ptree_formula_true _ _ _ FS);
      unfold ptree_formula; fold ptree_formula;
      apply (IHP PSV _ FS).

7,10,13 :
    unfold dub_neg_sub_formula, formula_sub_ind;
    try rewrite FS;
    try reflexivity.

all : destruct S;
      inversion FS as [FS'];
      try reflexivity;
      try apply and_bool_prop in FS' as [FS' FS1];
      unfold ptree_formula, dub_neg_sub_formula, formula_sub_ind, formula_sub_ind_fit, subst_ind_fit, form_eqb;
      fold form_eqb formula_sub_ind_fit ptree_formula subst_ind_fit.

6-8 : case (form_eqb a E) eqn:FEQ;
      try reflexivity;
      try apply form_eqb_eq in FEQ;
      try destruct FEQ;
      try apply PF.

2-4,6-8,10 : 
    destruct S1;
    inversion FS' as [FS''];
    try apply and_bool_prop in FS' as [FS' FS2].

4 : destruct S1_1;
    inversion FS'' as [FS'''];
    apply and_bool_prop in FS' as [FS' FS3].

all : unfold "&&";
      try rewrite FS;
      try rewrite FS';
      try rewrite FS'';
      try rewrite FS1;
      try rewrite FS2;
      try rewrite FS3;
      unfold ptree_formula;
      fold ptree_formula;
      try reflexivity.

1 : rewrite dub_neg_ptree_formula_true, (IHP PSV);
    try rewrite PF;
    unfold dub_neg_sub_formula, subst_ind_fit;
    fold subst_ind_fit.
    rewrite formula_sub_ind_lor, non_target_sub.

2,3,4 : rewrite non_target_fit, FS1;
        reflexivity.

1 : unfold formula_sub_ind.
    rewrite FS1.
    reflexivity.
Qed.

Lemma dub_neg_ptree_formula : forall (P : ptree) (E : formula),
  struct_valid P ->
      forall (S : subst_ind),
          ptree_formula (dub_neg_sub_ptree P E S) =
              dub_neg_sub_formula (ptree_formula P) E S.
Proof.
intros P E PSV S.
case (subst_ind_fit (ptree_formula P) S) eqn:FS.
- apply (dub_neg_ptree_formula' _ _ PSV), FS.
- unfold dub_neg_sub_formula, formula_sub_ind, dub_neg_sub_ptree.
  rewrite FS.
  reflexivity.
Qed.

Lemma dub_neg_ptree_deg :
    forall (P : ptree) (E : formula),
        struct_valid P ->
            forall (S : subst_ind),
                ptree_deg (dub_neg_sub_ptree P E S) = ptree_deg P.
Proof.
intros P E PSV.
unfold dub_neg_sub_ptree.
pose (ptree_formula P) as A.
induction P; intros S;
case (subst_ind_fit A S) eqn:FS;
unfold A in FS;
try rewrite FS;
unfold dub_neg_sub_ptree_fit; fold dub_neg_sub_ptree_fit;
unfold ptree_deg in *; fold ptree_deg in *;
try reflexivity.


1 : destruct PSV as [PSV PN].
2 : destruct PSV as [[PSV OU] NO].

8,9 : destruct PSV as [[[PF PSV] PD] PO].

1,2 : unfold ptree_formula in FS; fold ptree_formula in FS;
      pose proof (IHP PSV S) as IHPS;
      rewrite FS in IHPS;
      apply IHPS.

all : destruct S; inversion FS as [FS'];
      try reflexivity.

4,5 : case (form_eqb a E) eqn:EQ;
      unfold ptree_deg; fold ptree_deg;
      try rewrite PD;
      try reflexivity.

all : destruct S1; inversion FS' as [FS''].

3 : destruct S1_1; inversion FS'' as [FS'''].

all : unfold ptree_deg; fold ptree_deg;
      try reflexivity.

- assert (subst_ind_fit (ptree_formula P) (lor_ind (non_target a) S2) = true) as FSP.
  { rewrite PF.
    unfold subst_ind_fit; fold subst_ind_fit.
    rewrite non_target_fit.
    unfold "&&".
    apply FS''. }
  pose proof (IHP PSV (lor_ind (non_target a) S2)) as IHPS.
  rewrite FSP in IHPS.
  apply IHPS.
Qed.

Lemma dub_neg_ptree_ord :
    forall (P : ptree) (E : formula),
        struct_valid P ->
            forall (S : subst_ind),
                (ptree_ord (dub_neg_sub_ptree P E S)) = (ptree_ord P).
Proof.
intros P E PSV.
unfold dub_neg_sub_ptree.
pose (ptree_formula P) as A.
induction P; intros S;
case (subst_ind_fit A S) eqn:FS;
unfold A in FS;
try rewrite FS;
unfold dub_neg_sub_ptree_fit; fold dub_neg_sub_ptree_fit;
unfold ptree_ord in *; fold ptree_ord in *;
try reflexivity.

1 : destruct PSV as [PSV PN].
2 : destruct PSV as [PSV DU].

8,9 : destruct PSV as [[[PF PSV] PD] PO].

1,2 : unfold ptree_formula in FS; fold ptree_formula in FS;
      pose proof (IHP PSV S) as IHPS;
      rewrite FS in IHPS;
      apply IHPS.

all : destruct S; inversion FS as [FS'];
      try reflexivity.

4,5 : case (form_eqb a E) eqn:EQ;
      unfold ptree_deg; fold ptree_deg;
      try rewrite PD;
      try reflexivity.

all : destruct S1; inversion FS' as [FS''].

3 : destruct S1_1; inversion FS'' as [FS'''].

all : unfold ptree_deg; fold ptree_deg;
      try reflexivity.
Qed.

(*Start List Rules Need to Rehome*)

Definition dub_neg_trans (L : (list (formula * subst_ind))) (E : formula) := map (fun A => dub_neg_sub_formula (fst A) E (snd A)) L.

Lemma combine_non_target_triv : 
  forall (L : list formula) (E : formula),
      dub_neg_trans (combine L (map non_target L)) E = L.
Proof.
induction L;
intros E.
- reflexivity.
- unfold map, combine;
  fold (map non_target) (@combine formula subst_ind).
  unfold dub_neg_trans in *.
  unfold map at 1.
  fold (map (fun A : formula * subst_ind => dub_neg_sub_formula (fst A) E (snd A))).
  unfold dub_neg_sub_formula at 1.
  rewrite non_target_sub.
  rewrite (IHL E).
  reflexivity.
Qed.

Lemma non_target_lor :
    forall {A B : formula},
        (lor_ind (non_target A) (non_target B)) = (non_target (lor A B)). Proof. reflexivity. Qed.

Lemma dub_neg_node_non_target :
    forall (P : ptree),
        struct_valid P ->
            dub_neg_node P (non_target (ptree_formula P)) = map non_target (node_extract P).
Proof.
intros P.
induction P;
intros PSV;
unfold dub_neg_node, node_extract, dub_neg_node_fit;
rewrite non_target_fit;
fold node_extract dub_neg_node_fit.

1 : destruct PSV. (*node*)
2 : destruct PSV as [PSV PL]. (*leaf exchange*)
3 : destruct PSV as [PSV DU]. (*deg up*)
4 : destruct PSV as [[PSV OU] NO]. (*ord up*)
5-14 : destruct PSV as [[[PF PSV] PD] PO]. (*single hyp*)
15 : destruct PSV as [[[[PF PSV] PD] PO] CPF]. (*weakening*)

16-20 : destruct PSV as [[[[[[[P1F P1SV] P1D] P1O] P2F] P2SV] P2D] P2O]. (*double hyp*)
21-22 : destruct PSV as [[[[[[[[[P1F P1SV] P1D] P1O] P2F] P2SV] P2D] P2O] [L P2N]] FREEA]. (*loop*)

1 : reflexivity.


all : unfold ptree_formula;
      fold ptree_formula;
      unfold non_target;
      fold non_target;
      repeat rewrite dub_neg_node_formula_true;
      repeat rewrite non_target_lor.

all : try rewrite <- (IHP PSV);
      try rewrite map_app;
      try rewrite <- (IHP1 P1SV);
      try rewrite <- (IHP2 P2SV);
      try rewrite PF;
      try rewrite P1F;
      try rewrite P2F;
      unfold subst_ind_fit;
      fold subst_ind_fit;
      unfold non_target;
      fold non_target;
      repeat rewrite non_target_fit;
      repeat rewrite non_target_sub_fit;
      try reflexivity.

1 : { rewrite bury_map, (IHP PSV).
      reflexivity. }

all : rewrite <- non_target_term_sub;
      rewrite (non_target_term_sub a n (succ (var n))) at 1;
      try rewrite non_target_lor;
      rewrite <- P2F;
      rewrite (IHP2 P2SV);
      rewrite <- P2N;
      reflexivity.
Qed.

Lemma dub_neg_node_len : 
    forall (P : ptree) (S : subst_ind),
        struct_valid P ->
            length (node_extract P) = length (dub_neg_node P S).
Proof.
intros P;
induction P;
intros S PSV.

1 : destruct PSV. (*node*)
2 : destruct PSV as [PSV PL]. (*leaf exchange*)
3 : destruct PSV as [PSV DU]. (*deg up*)
4 : destruct PSV as [[PSV OU] NO]. (*ord up*)
5-14 : destruct PSV as [[[PF PSV] PD] PO]. (*single hyp*)
15 : destruct PSV as [[[[PF PSV] PD] PO] CPF]. (*weakening*)

16-20 : destruct PSV as [[[[[[[P1F P1SV] P1D] P1O] P2F] P2SV] P2D] P2O]. (*double hyp*)
21-22 : destruct PSV as [[[[[[[[[P1F P1SV] P1D] P1O] P2F] P2SV] P2D] P2O] [L P2N]] FREEA]. (*loop*)

all : unfold dub_neg_node;
      case subst_ind_fit eqn:FS;
      try rewrite map_length;
      try reflexivity;
      unfold node_extract, dub_neg_node_fit;
      fold node_extract dub_neg_node_fit;
      unfold ptree_formula in *;
      fold ptree_formula in *.

1 : { rewrite (dub_neg_node_formula_true _ _ FS).
      repeat rewrite bury_length.
      apply (IHP _ PSV). }

3-6,8-15,18-20 :
  destruct S;
  inversion FS as [FS'];
  try rewrite FS';
  try destruct (and_bool_prop _ _ FS') as [FS1 FS2].

4-6,10,13,17 :
  destruct S1;
  inversion FS' as [FS''];
  try rewrite FS'';
  try destruct (and_bool_prop _ _ FS1) as [FS1_1 FS1_2].

6 : destruct S1_1;
  inversion FS'' as [FS'''];
  try rewrite FS''';
  destruct (and_bool_prop _ _ FS1_1) as [FS1_1_1 FS1_1_2].

all : repeat rewrite dub_neg_node_formula_true;
      try apply IHP;
      repeat rewrite app_length;
      try rewrite <- IHP1;
      try rewrite <- IHP2;
      try apply PSV;
      try apply P1SV;
      try apply P2SV;
      try apply FS;
      try rewrite PF;
      try rewrite P1F;
      try rewrite P2F;
      unfold subst_ind_fit;
      fold subst_ind_fit;
      repeat rewrite FS;
      try rewrite FS1;
      try rewrite FS2;
      try rewrite FS1_1;
      try rewrite FS1_2;
      try rewrite FS1_1_1;
      try rewrite FS1_1_2;
      try rewrite non_target_fit;
      try rewrite non_target_sub_fit;
      try reflexivity.

1,2 : rewrite (non_target_term_sub a n (succ (var n))) at 1;
      rewrite <- P2F;
      rewrite (dub_neg_node_non_target _ P2SV);
      rewrite <- P2N;
      unfold map;
      fold (map non_target);
      unfold tl;
      rewrite map_length;
      reflexivity.

1 : rewrite cons_tl_len.
    rewrite cons_tl_len.
    rewrite <- (IHP2 _ P2SV).
    reflexivity.
    intros FAL.
    symmetry in FAL.
    apply length_zero_iff_nil in FAL.
    rewrite <- (IHP2 _ P2SV) in FAL.
    apply length_zero_iff_nil in FAL.
    apply (struct_non_empty_nodes _ P2SV FAL).
    rewrite <- P2N.
    discriminate.
Qed.

(*
Lemma dub_neg_non_target_triv_len :
    forall (LF : list formula) (P : ptree),
        LF = node_extract P ->
            forall (E : formula),
                struct_valid P ->
                    node_extract P = dub_neg_trans (combine (node_extract P) (dub_neg_node P (non_target (ptree_formula P)))) E.
Proof.
intros LF.
induction LF as [LF IND] using (induction_ltof1 _ (@length formula)).

induction P;
intros EQL E PSV;
unfold dub_neg_trans, dub_neg_node, dub_neg_node_fit, ptree_formula, node_extract;
rewrite non_target_fit;
fold ptree_formula node_extract dub_neg_node_fit.

1 : destruct PSV. (*node*)
2 : destruct PSV as [PSV DU]. (*deg up*)
3 : destruct PSV as [[PSV OU] NO]. (*ord up*)

4-13 : destruct PSV as [[[PF PSV] PD] PO]. (*single hyp*)
14 : destruct PSV as [[[[PF PSV] PD] PO] CPF]. (*weakening*)

15-19 : destruct PSV as [[[[[[[P1F P1SV] P1D] P1O] P2F] P2SV] P2D] P2O]. (*double hyp*)
20-21 : destruct PSV as [[[[[[[[P1F P1SV] P1D] P1O] P2F] P2SV] P2D] P2O] INA]. (*loop*)

1 : unfold combine, map, fst, snd, dub_neg_sub_formula.
    rewrite non_target_sub.
    reflexivity.

all : unfold non_target;
      fold non_target;
      unfold node_extract in EQL;
      fold node_extract in EQL;
      repeat rewrite dub_neg_node_formula_true;
      try rewrite PF;
      try rewrite P1F;
      try rewrite P2F;
      try apply non_target_fit;
      unfold subst_ind_fit;
      fold subst_ind_fit;
      try rewrite non_target_fit;
      try apply non_target_sub_fit;
      repeat rewrite non_target_lor;
      try rewrite <- PF;
      try rewrite <- P1F;
      try rewrite <- P2F.

11,12 : fold (non_target (neg (substitution a m (projT1 t))));
        try rewrite non_target_lor;
        rewrite <- PF.

all : try apply (IHP EQL _ PSV).

1-5 : try rewrite <- (combine_eq_len _ _ _ _ (dub_neg_node_len _ _ P1SV));
      try rewrite map_app;
      unfold ltof in IND;
      rewrite EQL in IND;
      rewrite (IND _ (struct_node_sum_less_l) _ eq_refl E P1SV), (IND _ (struct_node_sum_less_r) _ eq_refl E P2SV) at 1;
      rewrite P1F, P2F;
      reflexivity.

1 : { rewrite <- remove_alt at 2.
      unfold remove'.
      rewrite <- combine_eq_len.
      rewrite (combine_with_filter_split (fun Y => if form_eq_dec a Y then false else true) (node_extract P2)).
      - rewrite map_app.
        destruct (remove form_eq_dec a (node_extract P2)) as [ | L2] eqn:EQ.
        + rewrite app_nil_l in *.
          rewrite (IHP1 EQL E P1SV) at 1.
          admit.
        + unfold ltof in IND;
        rewrite EQL in IND;
        rewrite (IND _ (struct_node_sum_less_l) _ EQ E P2SV), (IND _ (struct_node_sum_less_r) _ eq_refl E P2SV) at 1;
        rewrite P1F, P2F;
        reflexivity.

      - apply dub_neg_node_len, P2SV.
      - rewrite split_length_r.
        rewrite <- (combine_filter_fst _ (dub_neg_node P2 (non_target a))).
        reflexivity.
        apply dub_neg_node_len, P2SV. }

1 : { rewrite <- remove_alt at 2.
      unfold remove'.
      rewrite <- combine_eq_len.
      rewrite (combine_with_filter_split (fun Y => if form_eq_dec (lor c a) Y then false else true) (node_extract P2)).
      - admit.
      - apply dub_neg_node_len, P2SV.
      - rewrite split_length_r.
        rewrite <- (combine_filter_fst _ (dub_neg_node P2 (non_target (lor c a)))).
        reflexivity.
        apply dub_neg_node_len, P2SV. }


Qed.
*)

(*
Lemma dub_neg_node_non_target_triv_aux :
    forall (P : ptree) (A E : formula) (F : formula -> bool),
        struct_valid P ->
            filter F (node_extract P) = dub_neg_trans (filter (fun X => F (fst X)) (combine (node_extract P) (dub_neg_node P (non_target (ptree_formula P))))) E.
Proof.
  intros P;
  induction P;
  intros A E F PSV;
  unfold dub_neg_trans, dub_neg_node, dub_neg_node_fit, ptree_formula, node_extract;
  rewrite non_target_fit;
  fold ptree_formula node_extract dub_neg_node_fit.
  
  1 : destruct PSV. (*node*)
  2 : destruct PSV as [PSV DU]. (*deg up*)
  3 : destruct PSV as [[PSV OU] NO]. (*ord up*)
  
  4-13 : destruct PSV as [[[PF PSV] PD] PO]. (*single hyp*)
  14 : destruct PSV as [[[[PF PSV] PD] PO] CPF]. (*weakening*)
  
  15-19 : destruct PSV as [[[[[[[P1F P1SV] P1D] P1O] P2F] P2SV] P2D] P2O]. (*double hyp*)
  20-21 : destruct PSV as [[[[[[[[P1F P1SV] P1D] P1O] P2F] P2SV] P2D] P2O] INA]. (*loop*)
  
1 : unfold combine, map, fst, snd, dub_neg_sub_formula.
    unfold filter.
    case (F a);
    try rewrite non_target_sub;
    reflexivity.

all : unfold non_target;
      fold non_target;
      repeat rewrite dub_neg_node_formula_true;
      try rewrite PF;
      try rewrite P1F;
      try rewrite P2F;
      try apply non_target_fit;
      unfold subst_ind_fit;
      fold subst_ind_fit;
      try rewrite non_target_fit;
      try apply non_target_sub_fit;
      repeat rewrite non_target_lor;
      try rewrite <- PF;
      try rewrite <- P1F;
      try rewrite <- P2F.

11,12 :  fold (non_target (neg (substitution a m (projT1 t))));
      try rewrite non_target_lor;
      rewrite <- PF.

all : try apply (IHP _ _ _ PSV).

1-5 : try rewrite <- (combine_eq_len _ _ _ _ (dub_neg_node_len _ _ P1SV));
      try rewrite filter_app;
      try rewrite remove_app;
      try rewrite map_app;
      try rewrite (IHP1 A E P1SV) at 1;
      try rewrite (IHP2 A E P2SV) at 1;
      try rewrite P1F, P2F;
      try reflexivity.
*)

Lemma dub_neg_non_target_triv :
    forall (P : ptree) (E : formula),
        struct_valid P ->
            node_extract P = dub_neg_trans (combine (node_extract P) (dub_neg_node P (non_target (ptree_formula P)))) E.
Proof.
intros P;
induction P;
intros E PSV;
unfold dub_neg_trans, dub_neg_node, dub_neg_node_fit, ptree_formula, node_extract;
rewrite non_target_fit;
fold ptree_formula node_extract dub_neg_node_fit.

1 : destruct PSV. (*node*)
2 : destruct PSV as [PSV PL]. (*leaf exchange*)
3 : destruct PSV as [PSV DU]. (*deg up*)
4 : destruct PSV as [[PSV OU] NO]. (*ord up*)
5-14 : destruct PSV as [[[PF PSV] PD] PO]. (*single hyp*)
15 : destruct PSV as [[[[PF PSV] PD] PO] CPF]. (*weakening*)

16-20 : destruct PSV as [[[[[[[P1F P1SV] P1D] P1O] P2F] P2SV] P2D] P2O]. (*double hyp*)
21-22 : destruct PSV as [[[[[[[[[P1F P1SV] P1D] P1O] P2F] P2SV] P2D] P2O] [L P2N]] FREEA]. (*loop*)

1 : unfold combine, map, fst, snd, dub_neg_sub_formula.
    rewrite non_target_sub.
    reflexivity.

1 : { rewrite (dub_neg_node_formula_true _ _ (non_target_fit _)).
      rewrite (bury_combine (dub_neg_node_len _ _ PSV)).
      rewrite bury_map.
      rewrite (IHP E PSV) at 1.
      reflexivity. }

all : unfold non_target;
      fold non_target;
      repeat rewrite dub_neg_node_formula_true;
      try rewrite PF;
      try rewrite P1F;
      try rewrite P2F;
      try apply non_target_fit;
      unfold subst_ind_fit;
      fold subst_ind_fit;
      try rewrite non_target_fit;
      try apply non_target_sub_fit;
      repeat rewrite non_target_lor;
      try rewrite <- PF;
      try rewrite <- P1F;
      try rewrite <- P2F.

11,12 : fold (non_target (neg (substitution a m (projT1 t))));
        try rewrite non_target_lor;
        rewrite <- PF.

all : try apply (IHP _ PSV).

1-5 : try rewrite <- (combine_eq_len (dub_neg_node_len _ _ P1SV));
      try rewrite map_app;
      try rewrite (IHP1 E P1SV) at 1;
      try rewrite (IHP2 E P2SV) at 1;
      try rewrite P1F, P2F;
      try reflexivity.
      
1 : { assert (tl (node_extract P2) = L). { rewrite <- P2N. reflexivity. }
      destruct H.
      rewrite <- combine_eq_len.
      rewrite map_app.
      rewrite combine_tail.
      rewrite <- map_tail.
      rewrite (non_target_term_sub a n zero) at 2.
      rewrite <- P1F.  
      rewrite <- (IHP1 E P1SV) at 1.
      rewrite (non_target_term_sub a n (succ (var n))) at 1.
      rewrite <- P2F.
      rewrite <- (IHP2 E P2SV) at 1.
      reflexivity.
      apply tail_len_eq, dub_neg_node_len, P2SV. }

1 : { assert (tl (node_extract P2) = L). { rewrite <- P2N. reflexivity. }
      destruct H.
      rewrite <- combine_eq_len.
      rewrite map_app.
      rewrite combine_tail.
      rewrite <- map_tail.
      rewrite <- non_target_lor.
      rewrite (non_target_term_sub a n zero) at 2.
      rewrite (non_target_term_sub a n (succ (var n))) at 1.
      repeat rewrite non_target_lor.
      rewrite <- P1F.
      rewrite <- (IHP1 E P1SV) at 1.
      rewrite <- P2F.
      rewrite <- (IHP2 E P2SV) at 1.
      reflexivity.
      apply tail_len_eq, dub_neg_node_len, P2SV. }
Qed.

Lemma dub_neg_node_size :
    forall (P : ptree) (E : formula) (S : subst_ind),
        struct_valid P ->
            subst_ind_fit (ptree_formula P) S = true ->
                length (node_extract P) = length (node_extract (dub_neg_sub_ptree P E S)).
Proof.
intros P.
induction P;
intros E S PSV FS;
unfold dub_neg_sub_ptree, node_extract, dub_neg_sub_ptree_fit;
rewrite FS;
fold node_extract dub_neg_sub_ptree_fit.

1 : destruct PSV. (*node*)
2 : destruct PSV as [PSV PL]. (*leaf exchange*)
3 : destruct PSV as [PSV DU]. (*deg up*)
4 : destruct PSV as [[PSV OU] NO]. (*ord up*)
5-14 : destruct PSV as [[[PF PSV] PD] PO]. (*single hyp*)
15 : destruct PSV as [[[[PF PSV] PD] PO] CPF]. (*weakening*)

16-20 : destruct PSV as [[[[[[[P1F P1SV] P1D] P1O] P2F] P2SV] P2D] P2O]. (*double hyp*)
21-22 : destruct PSV as [[[[[[[[[P1F P1SV] P1D] P1O] P2F] P2SV] P2D] P2O] [L P2N]] FREEA]. (*loop*)

1 : reflexivity.

1 : repeat rewrite bury_length.
    unfold ptree_formula in FS;
    fold ptree_formula in FS.
    rewrite (dub_neg_ptree_formula_true _ _ _ FS).
    apply (IHP _ _ PSV FS).

3-6,8-15,18-20 :
      destruct S;
      inversion FS as [FS'];
      try rewrite FS';
      try destruct (and_bool_prop _ _ FS') as [FS1 FS2].
  
4-6,10,13,17 :
    destruct S1;
    inversion FS' as [FS''];
    try rewrite FS'';
    try destruct (and_bool_prop _ _ FS1) as [FS1_1 FS1_2].
  
6 : destruct S1_1;
    inversion FS'' as [FS'''];
    try rewrite FS''';
    destruct (and_bool_prop _ _ FS1_1) as [FS1_1_1 FS1_1_2].

8,15 : case form_eqb eqn:EQ.

all : repeat rewrite dub_neg_ptree_formula_true;
      unfold node_extract, ptree_formula in *;
      fold node_extract ptree_formula in *;
      try apply (IHP _ _ PSV);
      repeat rewrite app_length;
      try rewrite <- (IHP1 _ _ P1SV);
      try rewrite <- (IHP2 _ _ P2SV);
      try rewrite PF;
      try rewrite P1F;
      try rewrite P2F;
      unfold subst_ind_fit;
      fold subst_ind_fit;
      try rewrite FS;
      try rewrite FS';
      try rewrite FS1;
      try rewrite FS2;
      try rewrite FS1_1;
      try rewrite FS1_2;
      try rewrite FS1_1_1;
      try rewrite FS1_1_2;
      try rewrite non_target_fit;
      try rewrite non_target_sub_fit;
      try reflexivity.

1 : rewrite cons_tl_len.
    rewrite cons_tl_len.
    rewrite <- (IHP2 _ _ P2SV).
    reflexivity.
    rewrite P2F.
    unfold subst_ind_fit;
    fold subst_ind_fit.
    rewrite FS1.
    apply non_target_sub_fit.
    intros FAL.
    symmetry in FAL.
    apply length_zero_iff_nil in FAL.
    rewrite <- (IHP2 _ _ P2SV) in FAL.
    apply length_zero_iff_nil in FAL.
    apply (struct_non_empty_nodes _ P2SV FAL).
    rewrite P2F.
    unfold subst_ind_fit;
    fold subst_ind_fit.
    rewrite FS1.
    apply non_target_sub_fit.
    rewrite <- P2N.
    discriminate.
Qed.

Lemma dub_neg_node_transform :
    forall (P : ptree) (E : formula) (S : subst_ind),
        struct_valid P ->
            subst_ind_fit (ptree_formula P) S = true ->
                node_extract (dub_neg_sub_ptree P E S) = (dub_neg_trans (combine (node_extract P) (dub_neg_node P S)) E).
Proof.
intros P.
induction P;
intros E S PSV FS;
unfold dub_neg_sub_ptree, node_extract, dub_neg_sub_ptree_fit, dub_neg_node, dub_neg_node_fit;
rewrite FS;
fold node_extract dub_neg_sub_ptree_fit dub_neg_node_fit.

1 : destruct PSV. (*node*)
2 : destruct PSV as [PSV PL]. (*leaf exchange*)
3 : destruct PSV as [PSV DU]. (*deg up*)
4 : destruct PSV as [[PSV OU] NO]. (*ord up*)
5-14 : destruct PSV as [[[PF PSV] PD] PO]. (*single hyp*)
15 : destruct PSV as [[[[PF PSV] PD] PO] CPF]. (*weakening*)

16-20 : destruct PSV as [[[[[[[P1F P1SV] P1D] P1O] P2F] P2SV] P2D] P2O]. (*double hyp*)
21-22 : destruct PSV as [[[[[[[[[P1F P1SV] P1D] P1O] P2F] P2SV] P2D] P2O] [L P2N]] FREEA]. (*loop*)

1 : reflexivity.

1 : { pose proof FS as FS'.
      unfold ptree_formula in FS'.
      rewrite (dub_neg_ptree_formula_true _ _ _ FS').
      rewrite (dub_neg_node_formula_true _ _ FS').
      clear FS'.
      rewrite (IHP _ _ PSV FS).
      rewrite (bury_combine (dub_neg_node_len _ _ PSV)).
      unfold dub_neg_trans.
      rewrite bury_map.
      reflexivity. }

3-6,8-15,18-20 :
  destruct S;
  inversion FS as [FS'];
  try rewrite FS';
  try destruct (and_bool_prop _ _ FS') as [FS1 FS2].

4-6,10,13,17 :
  destruct S1;
  inversion FS' as [FS''];
  try rewrite FS'';
  try destruct (and_bool_prop _ _ FS1) as [FS1_1 FS1_2].

6 : destruct S1_1;
  inversion FS'' as [FS'''];
  try rewrite FS''';
  destruct (and_bool_prop _ _ FS1_1) as [FS1_1_1 FS1_1_2].

8,15 : case form_eqb eqn:EQ.

all : repeat rewrite dub_neg_ptree_formula_true;
      repeat rewrite dub_neg_node_formula_true;
      unfold node_extract, ptree_formula in *;
      fold node_extract ptree_formula in *;
      try rewrite (IHP _ _ PSV);
      try rewrite (IHP1 _ _ P1SV);
      try rewrite (IHP2 _ _ P2SV); 
      try rewrite PF;
      try rewrite P1F;
      try rewrite P2F;
      unfold subst_ind_fit;
      fold subst_ind_fit;
      try rewrite FS;
      try rewrite FS';
      try rewrite FS1;
      try rewrite FS2;
      try rewrite FS1_1;
      try rewrite FS1_2;
      try rewrite FS1_1_1;
      try rewrite FS1_1_2;
      try rewrite non_target_fit;
      try rewrite non_target_sub_fit;
      try reflexivity.

  15 :  try refine (existT _ ((map non_target (node_extract P1)) ++ (projT1 (IHP2 E _ P2SV _))) (conj _ _));
        try destruct IHP2 as [L2 [EQ2 EL2]];
        unfold projT1, dub_neg_trans;
        try rewrite <- (combine_eq_len (eq_sym (map_length _ _)));
        try rewrite map_app;
        try rewrite app_length;
        try rewrite map_length;
        try rewrite EL2;
        try rewrite (combine_non_target_triv (node_extract P1) E) at 1;
        try rewrite EQ2;
        try reflexivity.

  14 :  try refine (existT _ ((projT1 (IHP1 E _ P1SV _)) ++ (map non_target (node_extract P2))) (conj _ _));
        try destruct IHP1 as [L1 [EQ1 EL1]];
        unfold projT1, dub_neg_trans;
        try rewrite <- (combine_eq_len (eq_sym EL1));
        try rewrite map_app;
        try rewrite app_length;
        try rewrite map_length;
        try rewrite EL1;
        try rewrite (combine_non_target_triv (node_extract P2) E) at 1;
        try rewrite EQ1;
        try reflexivity.
        
  6,7 : fold (non_target (neg (substitution a m (projT1 t)))).

  8,9 : fold (non_target (neg a));
        unfold non_target at 2;
        fold (non_target (neg b)).

  15 :  { rewrite (dub_neg_non_target_triv P1 E P1SV) at 1.
          rewrite <- (combine_eq_len (dub_neg_node_len _ _ P1SV)).
          rewrite map_app.
          rewrite P1F.
          reflexivity. }

  14 :  { rewrite (dub_neg_non_target_triv P2 E P2SV) at 1.
          rewrite <- (combine_eq_len (dub_neg_node_len _ _ P1SV)).
          rewrite map_app.
          rewrite P2F.
          reflexivity. }

  13 :  { rewrite <- combine_eq_len.
          unfold dub_neg_trans.
          rewrite map_app.
          rewrite combine_tail.
          rewrite <- map_tail.
          reflexivity.
          apply tail_len_eq, dub_neg_node_len, P2SV. }

  12 :  { rewrite <- combine_eq_len.
          unfold dub_neg_trans.
          rewrite map_app.
          rewrite combine_tail.
          rewrite <- map_tail.
          rewrite (dub_neg_non_target_triv _ E P2SV) at 1.
          rewrite (dub_neg_non_target_triv _ E P1SV) at 1.
          rewrite P1F, P2F, <- non_target_term_sub, <- non_target_term_sub.
          reflexivity.
          apply tail_len_eq, dub_neg_node_len, P2SV. }

  11 :  { rewrite <- combine_eq_len.
          unfold dub_neg_trans.
          rewrite map_app.
          rewrite combine_tail.
          rewrite <- map_tail.
          rewrite (dub_neg_non_target_triv _ E P2SV) at 1.
          rewrite (dub_neg_non_target_triv _ E P1SV) at 1.
          rewrite P1F, P2F, <- non_target_term_sub, <- non_target_term_sub.
          reflexivity.
          apply tail_len_eq, dub_neg_node_len, P2SV. }

  all : try rewrite <- PF;
        try apply dub_neg_non_target_triv;
        try rewrite <- (combine_eq_len (dub_neg_node_len _ _ P1SV));
        unfold dub_neg_trans;
        try rewrite map_app;
        try apply PSV;
        try apply P1SV;
        try apply P2SV;
        try reflexivity.

  all : try rewrite <- P1F;
        try rewrite <- P2F;
        try rewrite (dub_neg_non_target_triv P1 E) at 1;
        try rewrite (dub_neg_non_target_triv P2 E) at 1;
        try apply P1SV;
        try apply P2SV;
        try reflexivity.
Qed.

Lemma dub_neg_sub_nth_node_free :
    forall (P : ptree) (E : formula) (S : subst_ind),
        struct_valid P ->
            subst_ind_fit (ptree_formula P) S = true ->
                forall (m : nat),
                    free_list (nth m (node_extract P) (atom (equ zero zero))) = free_list (nth m (node_extract (dub_neg_sub_ptree P E S)) (atom (equ zero zero))).
Proof.
  intros P E.
  induction P;
  intros S PSV FS.

  1 : destruct PSV. (*node*)
  2 : destruct PSV as [PSV PL]. (*leaf exchange*)
  3 : destruct PSV as [PSV DU]. (*deg up*)
  4 : destruct PSV as [[PSV OU] NO]. (*ord up*)
  5-14 : destruct PSV as [[[PF PSV] PD] PO]. (*single hyp*)
  15 : destruct PSV as [[[[PF PSV] PD] PO] CPF]. (*weakening*)

  16-20 : destruct PSV as [[[[[[[P1F P1SV] P1D] P1O] P2F] P2SV] P2D] P2O]. (*double hyp*)
  21-22 : destruct PSV as [[[[[[[[[P1F P1SV] P1D] P1O] P2F] P2SV] P2D] P2O] [L P2N]] FREEA]. (*loop*)

  1 : { unfold dub_neg_sub_ptree.
        rewrite FS.
        unfold dub_neg_sub_ptree_fit.
        intros m.
        unfold node_extract.
        destruct m;
        unfold nth;
        try rewrite dub_neg_formula_free;
        reflexivity. }

  4-7,9-16,19-21 :
      destruct S;
      inversion FS as [FS'];
      try rewrite FS';
      try destruct (and_bool_prop _ _ FS') as [FS1 FS2].
  
  5-7,11,14,18 :
      destruct S1;
      inversion FS' as [FS''];
      try rewrite FS'';
      try destruct (and_bool_prop _ _ FS1) as [FS1_1 FS1_2].
  
  7 : destruct S1_1;
      inversion FS'' as [FS'''];
      try rewrite FS''';
      destruct (and_bool_prop _ _ FS1_1) as [FS1_1_1 FS1_1_2].
  
  all : unfold dub_neg_sub_ptree;
        rewrite FS;
        unfold dub_neg_sub_ptree_fit;
        fold dub_neg_sub_ptree_fit;
        unfold node_extract in *;
        fold node_extract in *;
        try rewrite dub_neg_ptree_formula_true;
        try rewrite dub_neg_ptree_formula_true;
        try rewrite PF;
        try rewrite P1F;
        try rewrite P2F;
        unfold ptree_formula in FS;
        fold ptree_formula in FS;
        unfold subst_ind_fit;
        fold subst_ind_fit;
        try rewrite FS;
        try rewrite FS';
        try rewrite FS1;
        try rewrite FS2;
        try rewrite FS1_1;
        try rewrite FS1_2;
        try rewrite FS1_1_1;
        try rewrite FS1_1_2;
        try rewrite non_target_fit;
        try rewrite non_target_sub_fit;
        try reflexivity.

  all : try case form_eqb eqn:EQ;
        repeat apply incl_app_app;
        try apply incl_refl;
        try apply (fun FSUB => IHP _ PSV FSUB);
        try rewrite (fun FSUB => IHP1 _ P1SV FSUB);
        try rewrite (fun FSUB => IHP2 _ P2SV FSUB);
        try rewrite PF;
        try rewrite P1F;
        try rewrite P2F;
        unfold ptree_formula in FS;
        fold ptree_formula in FS;
        unfold subst_ind_fit;
        fold subst_ind_fit;
        try rewrite FS;
        try rewrite FS';
        try rewrite FS1;
        try rewrite FS2;
        try rewrite FS1_1;
        try rewrite FS1_2;
        try rewrite FS1_1_1;
        try rewrite FS1_1_2;
        try rewrite non_target_fit;
        try rewrite non_target_sub_fit;
        try reflexivity.

  1 : { intros m.
        destruct (nat_semiconnex m (length (node_extract P))) as [LT | [GT | EQ]].
        1 : destruct (nat_semiconnex m n) as [LT' | [GT' | EQ']].
        1 : repeat rewrite (nth_pre_bury LT').
            apply (IHP _ PSV FS).
        1,2 : inversion LT as [EQ | x LE EQ].
        1,3 : rewrite (nth_end_bury PL EQ);
              rewrite (dub_neg_node_size _ E _ PSV FS) in PL, EQ;
              rewrite (nth_end_bury PL EQ);
              apply (IHP _ PSV FS).
        1,2 : rewrite (nth_post_bury);
              try lia;
              rewrite (dub_neg_node_size _ E _ PSV FS) in PL, EQ;
              rewrite (nth_post_bury);
              try lia;
              try apply (IHP _ PSV FS).
        all : repeat rewrite nth_overflow;
              try rewrite bury_length;
              try reflexivity;
              repeat rewrite <- (dub_neg_node_size _ _ _ PSV FS);
              try lia. }

  4 : { intros m.
        rewrite (app_tail (struct_non_empty_nodes _ P2SV)).
        rewrite app_tail.
        repeat rewrite nth_tail;
        destruct (nat_semiconnex (S m) (length (node_extract P2))) as [LT | [GT | EQ]];
        try destruct (eq_sym EQ);
        try rewrite (app_nth1 _ _ _ LT);
        try rewrite (dub_neg_node_size _ E (lor_ind S1 (non_target a)) P2SV) in LT;
        try rewrite (app_nth1 _ _ _ LT);
        try rewrite (app_nth2 _ _ _ (le_S_n _ _ (le_S _ _ GT)));
        try rewrite (dub_neg_node_size _ E (lor_ind S1 (non_target a)) P2SV) in GT;
        try rewrite (app_nth2 _ _ _ (le_S_n _ _ (le_S _ _ GT)));
        try rewrite (app_nth2 _ _ _ (le_n _));
        try rewrite (dub_neg_node_size _ E (lor_ind S1 (non_target a)) P2SV);
        try rewrite (app_nth2 _ _ _ (le_n _));
        try apply (IHP1 _ P1SV);
        try apply (IHP2 _ P2SV);
        try rewrite P1F;
        try rewrite P2F;
        unfold subst_ind_fit;
        fold subst_ind_fit;
        try rewrite FS1;
        try rewrite non_target_sub_fit;
        try reflexivity.
        intros FAL.
        apply length_zero_iff_nil in FAL.
        rewrite <- (dub_neg_node_size _ _ _ P2SV) in FAL.
        apply length_zero_iff_nil in FAL.
        apply (struct_non_empty_nodes _ P2SV FAL).
        rewrite P2F.
        unfold subst_ind_fit;
        fold subst_ind_fit.
        rewrite FS1.
        rewrite non_target_sub_fit.
        reflexivity. }

  all : intros m;
        destruct (nat_semiconnex m (length (node_extract P1))) as [LT | [GT | EQ]].

  1,4,7,10,13 : rewrite (app_nth1 _ _ _ LT).

  6-15 :  try destruct (eq_sym EQ);
          try rewrite (app_nth2 _ _ _ (le_S_n _ _ (le_S _ _ GT)));
          try rewrite (app_nth2 _ _ _ (le_n _)).

  1-5 : rewrite app_nth1.

  11-20 : rewrite app_nth2.

  all : try rewrite <- (dub_neg_node_size _ E _ P1SV);
        try apply LT;
        try apply (le_S_n _ _ (le_S _ _ GT));
        try apply (le_n _);
        try apply (IHP1 _ P1SV);
        try apply (IHP2 _ P2SV);
        try reflexivity;
        try rewrite PF;
        try rewrite P1F;
        try rewrite P2F;
        unfold ptree_formula in FS;
        fold ptree_formula in FS;
        unfold subst_ind_fit;
        fold subst_ind_fit;
        try rewrite FS;
        try rewrite FS';
        try rewrite FS1;
        try rewrite FS2;
        try rewrite FS1_1;
        try rewrite FS1_2;
        try rewrite FS1_1_1;
        try rewrite FS1_1_2;
        try rewrite non_target_fit;
        try rewrite non_target_sub_fit;
        try reflexivity.
Qed.  

Lemma dub_neg_free_sub :
    forall (P : ptree) (E : formula) (S : subst_ind),
        struct_valid P ->
            subst_ind_fit (ptree_formula P) S = true ->
                (flat_map free_list (node_extract P)) = (flat_map free_list (node_extract (dub_neg_sub_ptree P E S))).
Proof.
  intros P E.
  induction P;
  intros S PSV FS.

  1 : destruct PSV. (*node*)
  2 : destruct PSV as [PSV PL]. (*leaf exchange*)
  3 : destruct PSV as [PSV DU]. (*deg up*)
  4 : destruct PSV as [[PSV OU] NO]. (*ord up*)
  5-14 : destruct PSV as [[[PF PSV] PD] PO]. (*single hyp*)
  15 : destruct PSV as [[[[PF PSV] PD] PO] CPF]. (*weakening*)

  16-20 : destruct PSV as [[[[[[[P1F P1SV] P1D] P1O] P2F] P2SV] P2D] P2O]. (*double hyp*)
  21-22 : destruct PSV as [[[[[[[[[P1F P1SV] P1D] P1O] P2F] P2SV] P2D] P2O] [L P2N]] FREEA]. (*loop*)

  1 : { unfold dub_neg_sub_ptree.
        rewrite FS.
        unfold dub_neg_sub_ptree_fit.
        unfold node_extract, flat_map.
        repeat rewrite app_nil_r.
        rewrite dub_neg_formula_free.
        reflexivity. }

  4-7,9-16,19-21 :
      destruct S;
      inversion FS as [FS'];
      try rewrite FS';
      try destruct (and_bool_prop _ _ FS') as [FS1 FS2].
  
  5-7,11,14,18 :
      destruct S1;
      inversion FS' as [FS''];
      try rewrite FS'';
      try destruct (and_bool_prop _ _ FS1) as [FS1_1 FS1_2].
  
  7 : destruct S1_1;
      inversion FS'' as [FS'''];
      try rewrite FS''';
      destruct (and_bool_prop _ _ FS1_1) as [FS1_1_1 FS1_1_2].
  
  all : unfold dub_neg_sub_ptree;
        rewrite FS;
        unfold dub_neg_sub_ptree_fit;
        fold dub_neg_sub_ptree_fit;
        unfold node_extract in *;
        fold node_extract in *;
        try rewrite dub_neg_ptree_formula_true;
        try rewrite dub_neg_ptree_formula_true;
        try rewrite PF;
        try rewrite P1F;
        try rewrite P2F;
        unfold ptree_formula in FS;
        fold ptree_formula in FS;
        unfold subst_ind_fit;
        fold subst_ind_fit;
        try rewrite FS;
        try rewrite FS';
        try rewrite FS1;
        try rewrite FS2;
        try rewrite FS1_1;
        try rewrite FS1_2;
        try rewrite FS1_1_1;
        try rewrite FS1_1_2;
        try rewrite non_target_fit;
        try rewrite non_target_sub_fit;
        try reflexivity.

  all : try case form_eqb eqn:EQ;
        try case (closed (univ n a)) eqn:CuA;
        unfold flat_map;
        fold (flat_map free_list);
        repeat rewrite flat_map_app;
        repeat apply incl_app_app;
        try apply incl_refl;
        try apply (fun FSUB => IHP _ PSV FSUB);
        try rewrite <- (fun FSUB => IHP1 _ P1SV FSUB);
        try rewrite <- (fun FSUB => IHP2 _ P2SV FSUB);
        try rewrite PF;
        try rewrite P1F;
        try rewrite P2F;
        unfold ptree_formula in FS;
        fold ptree_formula in FS;
        unfold subst_ind_fit;
        fold subst_ind_fit;
        try rewrite FS;
        try rewrite FS';
        try rewrite FS1;
        try rewrite FS2;
        try rewrite FS1_1;
        try rewrite FS1_2;
        try rewrite FS1_1_1;
        try rewrite FS1_1_2;
        try rewrite non_target_fit;
        try rewrite non_target_sub_fit;
        try reflexivity.

  1 : apply (flat_map_nth_ext_bury (dub_neg_node_size _ _ _ PSV FS) (dub_neg_sub_nth_node_free _ _ _ PSV FS)).

  1,2 : rewrite (@flat_map_nth_ext_tl _ _ (node_extract P2) (node_extract (dub_neg_sub_ptree P2 E (lor_ind S1 (non_target a)))) _ (atom (equ zero zero)));
        try apply (dub_neg_node_size _ _ _ P2SV);
        try apply (dub_neg_sub_nth_node_free _ _ _ P2SV);
        try rewrite P2F;
        unfold subst_ind_fit;
        fold subst_ind_fit;
        try rewrite FS1;
        try rewrite non_target_sub_fit;
        try reflexivity.
Qed.

Lemma dub_neg_all_ax_trans : 
    forall (P : ptree) (E : formula) (S : subst_ind),
        struct_valid P ->
            subst_ind_fit (ptree_formula P) S = true ->
                (forall (A : formula), In A (node_extract P) -> PA_cyclic_axiom A = true) ->
                    (forall (A : formula), In A (node_extract (dub_neg_sub_ptree P E S)) -> PA_cyclic_axiom A = true).
Proof.
intros P E S PSV FS PAX A.
rewrite (dub_neg_node_transform _ _ _ PSV FS).
unfold dub_neg_trans.
intros INA.
apply in_map_iff in INA as [[B SB] [EQ IN]].
destruct EQ.
unfold fst, snd.
pose proof (PAX _ (in_combine_l _ _ _ _ IN)) as AX.
rewrite dub_neg_axiom_id;
apply AX.
Qed.

Lemma dub_neg_axiom_nth_eq :
    forall (P : ptree) (E : formula) (S : subst_ind),
        struct_valid P ->
            subst_ind_fit (ptree_formula P) S = true ->
                forall (A : formula) (n : nat),
                    PA_cyclic_axiom (nth n (node_extract P) A) = true ->
                        nth n (node_extract P) A = nth n (node_extract (dub_neg_sub_ptree P E S)) A.
Proof.
  intros P E.
  induction P; try intros S PSV FS A x AX;
  unfold dub_neg_sub_ptree;
  rewrite FS;
  unfold ptree_formula in *; fold ptree_formula in *;
  unfold dub_neg_sub_ptree_fit; fold dub_neg_sub_ptree_fit;
  unfold node_extract in *; fold node_extract in *.

  1 : destruct PSV. (*node*)
  2 : destruct PSV as [PSV PL]. (*leaf exchange*)
  3 : destruct PSV as [PSV DU]. (*deg up*)
  4 : destruct PSV as [[PSV OU] NO]. (*ord up*)
  5-14 : destruct PSV as [[[PF PSV] PD] PO]. (*single hyp*)
  15 : destruct PSV as [[[[PF PSV] PD] PO] CPF]. (*weakening*)

  16-20 : destruct PSV as [[[[[[[P1F P1SV] P1D] P1O] P2F] P2SV] P2D] P2O]. (*double hyp*)
  21-22 : destruct PSV as [[[[[[[[[P1F P1SV] P1D] P1O] P2F] P2SV] P2D] P2O] [L P2N]] FREEA]. (*loop*)

  1 : { destruct x.
        - rewrite dub_neg_axiom_id.
          reflexivity.
          apply AX.
        - repeat rewrite nth_overflow;
          unfold length;
          try lia.
          reflexivity. }        

  
  1 : { destruct (nat_semiconnex x (length (node_extract P))) as [LT | [GT | EQ]];
        rewrite (dub_neg_ptree_formula_true _ _ _ FS).
        
        1 : destruct (nat_semiconnex x n) as [LT' | [GT' | EQ']].
        1 : repeat rewrite (nth_pre_bury LT') in *.
            apply (IHP _ PSV FS _ _ AX).
        1,2 : inversion LT as [EQ | y LE EQ].
        1,3 : rewrite (nth_end_bury PL EQ);
              rewrite (nth_end_bury PL EQ) in AX;
              rewrite (dub_neg_node_size _ E _ PSV FS) in PL, EQ;
              rewrite (nth_end_bury PL EQ);
              refine (IHP _ PSV FS _ _ AX);
              try lia.
        1,2 : rewrite (nth_post_bury);
              rewrite (nth_post_bury) in AX;
              try lia;
              rewrite (dub_neg_node_size _ E _ PSV FS) in PL, EQ;
              rewrite (nth_post_bury);
              try lia;
              refine (IHP _ PSV FS _ _ AX);
              rewrite (dub_neg_node_size _ E _ PSV FS);
              try lia.
        1,2 : repeat rewrite nth_overflow;
              try rewrite bury_length;
              try rewrite <- (dub_neg_node_size _ _ _ PSV FS);
              try lia;
              try reflexivity. }

  3-6,8-13,15-20 : 
      destruct S; inversion FS as [FS'];
      try destruct (and_bool_prop _ _ FS') as [FS1 FS2].

  4-6,10 :  destruct S1; inversion FS' as [FS''];
            try destruct (and_bool_prop _ _ FS1) as [FS1_1 FS1_2].

  6 : destruct S1_1; inversion FS'' as [FS'''];
      destruct (and_bool_prop _ _ FS1_1) as [FS1_1_1 FS1_1_2].

  8,11 : case (form_eqb a E) eqn:EQ.

  all : try apply form_eqb_eq in EQ;
        try destruct EQ;
        repeat rewrite dub_neg_ptree_formula_true;
        try apply IHP;
        try rewrite IHP1;
        try rewrite IHP2;
        try rewrite dub_neg_ptree_formula;
        try rewrite PF;
        try rewrite P1F;
        try rewrite P2F;
        unfold dub_neg_sub_formula, formula_sub_ind;
        try apply PSV;
        try apply P1SV;
        try apply P2SV;
        try apply PAX;
        unfold subst_ind_fit; fold subst_ind_fit;
        try rewrite non_target_fit;
        try rewrite non_target_sub_fit;
        try rewrite FS;
        try rewrite FS';
        try rewrite FS'';
        try rewrite FS1;
        try rewrite FS1_1;
        try rewrite FS1_2;
        try rewrite FS1_1_1;
        try rewrite FS1_1_2;
        try rewrite FS2;
        unfold node_extract;
        fold node_extract;
        try apply (fun B INB => PAX B (proj2 (in_app_iff _ _ _) (or_introl INB)));
        try apply (fun B INB => PAX B (proj2 (in_app_iff _ _ _) (or_intror INB)));
        unfold "&&";
        unfold formula_sub_ind_fit; fold formula_sub_ind_fit;
        unfold form_eqb; fold form_eqb;
        try rewrite non_target_sub_term';
        try rewrite non_target_sub';
        try rewrite <- (sub_fit_true _ _ _ _ FS1);
        try case form_eqb eqn:FEQ;
        try apply LT;
        try apply AX;
        try reflexivity.

  9 : { rewrite (app_tail (struct_non_empty_nodes _ P2SV)) in AX.
        rewrite (app_tail (struct_non_empty_nodes _ P2SV)).
        rewrite app_tail.
        repeat rewrite nth_tail in *.
        destruct (nat_semiconnex (S x) (length (node_extract P2))) as [LT | [GT | EQ]].
        1 : rewrite (app_nth1 _ _ _ LT) in AX;
            repeat rewrite app_nth1;
            try rewrite <- (dub_neg_node_size _ _ _ P2SV);
            try apply LT;
            try refine (IHP2 _ P2SV _ _ _ AX);
            try reflexivity.
        3 : rewrite (app_nth2 _ _ _ (le_S_n _ _ (le_S _ _ GT))) in AX;
            repeat rewrite app_nth2;
            try rewrite <- (dub_neg_node_size _ _ _ P2SV);
            try apply (le_S_n _ _ (le_S _ _ GT));
            try refine (IHP1 _ P1SV _ _ _ AX);
            try reflexivity.
        6 : destruct (eq_sym EQ);
            rewrite (app_nth2 _ _ _ (le_n _ )) in AX;
            repeat rewrite app_nth2;
            try rewrite <- (dub_neg_node_size _ _ _ P2SV);
            try apply (le_n _);
            try refine (IHP1 _ P1SV _ _ _ AX).

        1-9 : try rewrite P1F;
              try rewrite P2F;
              unfold subst_ind_fit;
              fold subst_ind_fit;
              try rewrite FS';
              try rewrite FS1;
              try rewrite FS2;
              try rewrite non_target_fit;
              try rewrite non_target_sub_fit;
              try reflexivity.

        1 : intros FAL.
            apply length_zero_iff_nil in FAL.
            rewrite <- (dub_neg_node_size _ _ _ P2SV) in FAL.
            apply length_zero_iff_nil in FAL.
            apply (struct_non_empty_nodes _ P2SV FAL).
            rewrite P2F.
            unfold subst_ind_fit;
            fold subst_ind_fit.
            rewrite FS1.
            rewrite non_target_sub_fit.
            reflexivity. }

  1-8 : destruct (nat_semiconnex x (length (node_extract P1))) as [LT | [GT | EQ]].

  1,4,7,10,13,16,19,22 :  rewrite (app_nth1 _ _ _ LT) in AX;
                          repeat rewrite app_nth1;
                          try rewrite <- (dub_neg_node_size _ _ _ P1SV);
                          try apply LT;
                          try refine (IHP1 _ P1SV _ _ _ AX);
                          try reflexivity.

  11,13,15,17,19,21,23,25 : rewrite (app_nth2 _ _ _ (le_S_n _ _ (le_S _ _ GT))) in AX;
                            repeat rewrite app_nth2;
                            try rewrite <- (dub_neg_node_size _ _ _ P1SV);
                            try apply (le_S_n _ _ (le_S _ _ GT));
                            try refine (IHP2 _ P2SV _ _ _ AX);
                            try reflexivity.

  26-33 : destruct (eq_sym EQ);
          rewrite (app_nth2 _ _ _ (le_n _ )) in AX;
          repeat rewrite app_nth2;
          try rewrite <- (dub_neg_node_size _ _ _ P1SV);
          try apply (le_n _);
          try refine (IHP2 _ P2SV _ _ _ AX).
        
  all : try rewrite P1F;
        try rewrite P2F;
        unfold subst_ind_fit;
        fold subst_ind_fit;
        try rewrite FS';
        try rewrite FS1;
        try rewrite FS2;
        try rewrite non_target_fit;
        try reflexivity.
Qed.

Lemma dub_neg_valid_node :
    forall (P : ptree) (E : formula),
        valid P ->
            forall (S : subst_ind),
                subst_ind_fit (ptree_formula P) S = true ->
                    node_extract (dub_neg_sub_ptree P E S) = node_extract P.
Proof.
  intros P E [PSV PAX] S FS.
  symmetry.
  apply (nth_ext _ _ (atom (equ zero zero)) (atom (equ zero zero)) (dub_neg_node_size _ _ _ PSV FS)).
  intros n LT.
  apply (dub_neg_axiom_nth_eq _ _ _ PSV FS  _ _ (PAX _ (nth_In _ _ LT))).
Qed.

Lemma dub_neg_tail_valid_node : 
    forall (P : ptree) (E : formula),
        struct_valid P ->
            (forall (A : formula) , In A (tl (node_extract P)) -> PA_cyclic_axiom A = true) ->
                forall (S : subst_ind),
                    subst_ind_fit (ptree_formula P) S = true ->
                        tl (node_extract (dub_neg_sub_ptree P E S)) = tl (node_extract P).
Proof.
intros P E PSV PAX S FS.
symmetry.
apply (nth_ext _ _ (atom (equ zero zero)) (atom (equ zero zero)) (tail_len_eq (dub_neg_node_size _ _ _ PSV FS))).
intros n LT.
repeat rewrite nth_tail.
apply (dub_neg_axiom_nth_eq _ _ _ PSV FS _ _).
rewrite <- nth_tail.
apply PAX, nth_In, LT.
Qed.


(*
Lemma who_knows :
    forall (P : ptree),
        struct_valid (leaf_con P) ->
            forall (S : subst_ind),
                subst_ind_fit (ptree_formula P) S = true ->
                    {L : list subst_ind & {S' : subst_ind & dub_neg_node P S = S' :: S' :: L}}.
Proof.
intros P PSV;
induction P;
intros S FS;
pose proof FS as TFS;
destruct PSV as [PSV [L' [B' PN']]].

1 : destruct PSV. (*node*)
2 : destruct PSV as [PSV PL]. (*leaf exchange*)
3 : destruct PSV as [PSV [L [B PN]]]. (*leaf contraction*)
4 : destruct PSV as [PSV DU]. (*deg up*)
5 : destruct PSV as [[PSV OU] NO]. (*ord up*)
6-15 : destruct PSV as [[[PF PSV] PD] PO]. (*single hyp*)
16 : destruct PSV as [[[[PF PSV] PD] PO] CPF]. (*weakening*)
  
17-21 : destruct PSV as [[[[[[[P1F P1SV] P1D] P1O] P2F] P2SV] P2D] P2O]. (*double hyp*)
22-23 : destruct PSV as [[[[[[[[[P1F P1SV] P1D] P1O] P2F] P2SV] P2D] P2O] [L [P2N NINA]]] FREEA]. (*loop*)

1 : inversion PN'.

1 : admit.

1 : admit.

3-6,8-13,15,16,17,18 : 
    destruct S; inversion FS as [FS'];
    try destruct (and_bool_prop _ _ FS') as [FS1 FS2].

4-6,10 :  destruct S1; inversion FS' as [FS''];
          try destruct (and_bool_prop _ _ FS1) as [FS1_1 FS1_2].

6 : destruct S1_1; inversion FS'' as [FS'''];
    destruct (and_bool_prop _ _ FS1_1) as [FS1_1_1 FS1_1_2].

1 : apply (IHP (PSV,(existT _ L' (existT _ B' PN'))) _ FS).

1 : apply (IHP (PSV,(existT _ L' (existT _ B' PN'))) _ FS).

1-13,22 : unfold dub_neg_node, dub_neg_node_fit;
          fold dub_neg_node_fit;
          rewrite TFS;
          rewrite dub_neg_node_formula_true;
          try refine (IHP (PSV,(existT _ L' (existT _ B' PN'))) _ _);
          try rewrite PF;
          unfold subst_ind_fit;
          fold subst_ind_fit;
          unfold ptree_formula in TFS;
          fold ptree_formula in TFS;
          try rewrite non_target_fit;
          try rewrite non_target_sub_fit;
          try rewrite TFS;
          try rewrite FS;
          try rewrite FS';
          try rewrite FS'';
          try rewrite FS1;
          try rewrite FS1_1;
          try rewrite FS1_2;
          try rewrite FS1_1_1;
          try rewrite FS1_1_2;
          try rewrite FS2;
          try reflexivity.

1-9 : unfold dub_neg_node, dub_neg_node_fit;
      fold dub_neg_node_fit;
      rewrite TFS;
      repeat rewrite dub_neg_node_formula_true;
      try rewrite PF;
      try rewrite P1F;
      try rewrite P2F;
      unfold subst_ind_fit;
      fold subst_ind_fit;
      try rewrite non_target_fit;
      try rewrite non_target_sub_fit;
      try rewrite FS;
      try rewrite FS';
      try rewrite FS'';
      try rewrite FS1;
      try rewrite FS1_1;
      try rewrite FS1_2;
      try rewrite FS1_1_1;
      try rewrite FS1_1_2;
      try rewrite FS2;
      try reflexivity.

9 : { fold (non_target (neg a)).
      unfold non_target at 2.
      fold (non_target (neg b)).
      rewrite <- P1F, <- P2F, dub_neg_node_non_target, dub_neg_node_non_target.
      exists (map non_target L').
      exists (non_target B').
      rewrite <- map_app.
      unfold node_extract in PN';
      fold node_extract in PN'.
      rewrite PN'.
      reflexivity.
      apply P2SV.
      apply P1SV. }

7 : {  }



        unfold node_extract in PN';
        fold node_extract in PN';
        destruct (node_extract P1) as [| A L] eqn:EQ;
        try contradict (struct_non_empty_nodes _ P1SV EQ);
        destruct L;
        inversion PN' as [[EQ' P2N]].
        destruct EQ'.
        exists (tl (dub_neg_node P2 (lor_ind (0) S2))).
        exists (hd (0) (dub_neg_node P2 (lor_ind (0) S2))).
        rewrite <- (equalsish _ _ P1SV P2SV _ _ _ EQ P2N) at 1.
        rewrite head_tail_combine.
        rewrite <- (@len_1_head _ (dub_neg_node P1 _) (0)).
        reflexivity.
        rewrite <- dub_neg_node_len.
        rewrite EQ.
        reflexivity.
        apply P1SV.
        rewrite <- length_zero_iff_nil, <- dub_neg_node_len, length_zero_iff_nil.
        apply (struct_non_empty_nodes _ P2SV).
        apply P2SV.
*)

(*
Lemma dub_neg_structural_node_valid :
    forall (P : ptree),
        struct_valid P ->
            forall (S : subst_ind),
                subst_ind_fit (ptree_formula P) S = true ->
                    dub_neg_node_valid P S.
Proof.
intros P PSV;
induction P;
intros S FS;
unfold dub_neg_node_valid, dub_neg_node_valid_fit;
rewrite FS;
fold dub_neg_node_valid_fit.

1 : destruct PSV. (*node*)
2 : destruct PSV as [PSV PL]. (*leaf exchange*)
3 : destruct PSV as [PSV [L [B PN]]]. (*leaf contraction*)
4 : destruct PSV as [PSV DU]. (*deg up*)
5 : destruct PSV as [[PSV OU] NO]. (*ord up*)
6-15 : destruct PSV as [[[PF PSV] PD] PO]. (*single hyp*)
16 : destruct PSV as [[[[PF PSV] PD] PO] CPF]. (*weakening*)

17-21 : destruct PSV as [[[[[[[P1F P1SV] P1D] P1O] P2F] P2SV] P2D] P2O]. (*double hyp*)
22-23 : destruct PSV as [[[[[[[[[P1F P1SV] P1D] P1O] P2F] P2SV] P2D] P2O] [L [P2N NINA]]] FREEA]. (*loop*)

1 : reflexivity.

1 : { split.
      rewrite dub_neg_node_valid_formula_true.
      apply (IHP PSV _ FS).
      apply FS.
      apply PL. }

1 : { split.
      rewrite dub_neg_node_valid_formula_true.
      apply (IHP PSV _ FS).
      apply FS.

       }

3-6,8-15,18-20 :
  destruct S;
  inversion FS as [FS'];
  try rewrite FS';
  try destruct (and_bool_prop _ _ FS') as [FS1 FS2].

4-6,10,13,17 :
  destruct S1;
  inversion FS' as [FS''];
  try rewrite FS'';
  try destruct (and_bool_prop _ _ FS1) as [FS1_1 FS1_2].

6 : destruct S1_1;
  inversion FS'' as [FS'''];
  try rewrite FS''';
  destruct (and_bool_prop _ _ FS1_1) as [FS1_1_1 FS1_1_2].

all : repeat rewrite dub_neg_node_valid_formula_true;
      repeat split;
      try apply (IHP PSV);
      try apply (IHP1 P1SV);
      try apply (IHP2 P2SV);
      try rewrite PF;
      try rewrite P1F;
      try rewrite P2F;
      unfold subst_ind_fit;
      fold subst_ind_fit;
      unfold ptree_formula in FS;
      fold ptree_formula in FS;
      try rewrite non_target_fit;
      try rewrite non_target_sub_fit;
      try rewrite FS;
      try rewrite FS';
      try rewrite FS'';
      try rewrite FS1;
      try rewrite FS1_1;
      try rewrite FS1_2;
      try rewrite FS1_1_1;
      try rewrite FS1_1_2;
      try rewrite FS2;
      try reflexivity.

}

all : 


*)

Lemma dub_neg_structural :
    forall (P : ptree) (E : formula),
        struct_valid P ->
            forall (S : subst_ind),
                subst_ind_fit (ptree_formula P) S = true ->
                    struct_valid (dub_neg_sub_ptree P E S).
Proof.
intros P E PSV.
induction P; try intros S FS;
unfold dub_neg_sub_ptree;
rewrite FS;
unfold ptree_formula in *; fold ptree_formula in *;
unfold dub_neg_sub_ptree_fit; fold dub_neg_sub_ptree_fit.

all : try apply PSV.

1 : { destruct PSV as [PSV PL].
      rewrite dub_neg_ptree_formula_true.
      repeat split;
      unfold node_extract;
      fold node_extract.
      - apply (IHP PSV _ FS).
      - rewrite <- (dub_neg_node_size _ _ _ PSV FS).
        apply PL.
      - apply FS. }

1 : destruct PSV as [PSV DU].
2 : destruct PSV as [[PSV OU] NO].
3-11 : destruct PSV as [[[PF PSV] PD] PO].
12 : destruct PSV as [[[[PF PSV] PD] PO] FC].
13-16 : destruct PSV as [[[[[[[P1F P1SV] P1D] P1O] P2F] P2SV] P2D] P2O].
17 :  pose proof PSV as PSV'; 
      destruct PSV as [[[[[[[[[P1F P1SV] P1D] P1O] P2F] P2SV] P2D] P2O] [L P2N]] FREEA].

3-6,8-13,16,17 : 
    destruct S; inversion FS as [FS'];
    try destruct (and_bool_prop _ _ FS') as [FS1 FS2].

4-6,10 :  destruct S1; inversion FS' as [FS''];
          try destruct (and_bool_prop _ _ FS1) as [FS1_1 FS1_2].

6 : destruct S1_1; inversion FS'' as [FS'''];
    destruct (and_bool_prop _ _ FS1_1) as [FS1_1_1 FS1_1_2].

8,11 : case (form_eqb a E) eqn:EQ.

18  : { repeat rewrite dub_neg_ptree_formula_true;
        repeat split;
        try rewrite dub_neg_ptree_formula;
        try rewrite dub_neg_ptree_deg;
        try rewrite dub_neg_ptree_ord;
        try rewrite P1F;
        try rewrite P2F;
        try rewrite P1D;
        try rewrite P2D;
        try rewrite P1O;
        try rewrite P2O;
        try apply P1SV;
        try apply P2SV;
        unfold dub_neg_sub_formula;
        try rewrite formula_sub_ind_lor;
        try rewrite non_target_sub_term;
        unfold subst_ind_fit;
        fold subst_ind_fit;
        try rewrite FS1;
        try rewrite non_target_sub_fit;
        try reflexivity.

        - apply (IHP1 P1SV).
          rewrite P1F;
          unfold subst_ind_fit;
          fold subst_ind_fit;
          try rewrite FS1;
          try rewrite non_target_sub_fit;
          try reflexivity.
        - apply (IHP2 P2SV).
          rewrite P2F;
          unfold subst_ind_fit;
          fold subst_ind_fit;
          rewrite FS1.
          apply non_target_sub_fit.
        - assert (subst_ind_fit (ptree_formula P2) (lor_ind S1 (non_target a)) = true) as FIT2.
          { rewrite P2F.
            unfold subst_ind_fit;
            fold subst_ind_fit;
            rewrite FS1, non_target_sub_fit;
            unfold "&&";
            reflexivity. }
          refine (existT _ (tl (node_extract (dub_neg_sub_ptree P2 E (lor_ind S1 (non_target a))))) _).
          rewrite <- (@head_tail_combine _ _ E (struct_non_empty_nodes _ (IHP2 P2SV _ FIT2))) at 2.
          rewrite (dub_neg_node_transform _ _ _ P2SV FIT2).
          rewrite <- P2N.
          admit.
        - apply FREEA. }

all : try apply form_eqb_eq in EQ;
      try destruct EQ;
      repeat rewrite dub_neg_ptree_formula_true;
      repeat split;
      try apply IHP;
      try apply IHP1;
      try apply IHP2;
      try rewrite dub_neg_ptree_deg;
      try rewrite dub_neg_ptree_ord;
      try rewrite dub_neg_ptree_formula;
      try rewrite PF;
      try rewrite P1F;
      try rewrite P2F;
      unfold dub_neg_sub_formula, formula_sub_ind;
      try apply PSV;
      try rewrite PD;
      try rewrite PO;
      try apply P1SV;
      try rewrite P1D;
      try rewrite P1O;
      try apply P2SV;
      try rewrite P2D;
      try rewrite P2O;
      try apply DU;
      try apply OU;
      try apply NO;
      try apply INA;
      unfold subst_ind_fit; fold subst_ind_fit;
      try rewrite non_target_fit;
      try rewrite non_target_sub_fit;
      try rewrite FS;
      try rewrite FS';
      try rewrite FS'';
      try rewrite FS1;
      try rewrite FS1_1;
      try rewrite FS1_2;
      try rewrite FS1_1_1;
      try rewrite FS1_1_2;
      try rewrite FS2;
      unfold node_extract;
      fold node_extract;
      try apply (fun B INB => PAX B (proj2 (in_app_iff _ _ _) (or_introl INB)));
      try apply (fun B INB => PAX B (proj2 (in_app_iff _ _ _) (or_intror INB)));
      unfold "&&";
      unfold formula_sub_ind_fit; fold formula_sub_ind_fit;
      unfold form_eqb; fold form_eqb;
      try rewrite non_target_sub_term';
      try rewrite non_target_sub';
      try rewrite <- (sub_fit_true _ _ _ _ FS1);
      try case form_eqb eqn:FEQ;
      try reflexivity.

1,3 : apply ord_succ_monot.

1,2 : try apply nf_nf_succ;
      try apply ptree_ord_nf_struct;
      try apply PSV.

1 : { rewrite <- dub_neg_free_sub.
      unfold formula_sub_ind.
      rewrite FS1.
      rewrite formula_sub_ind_free_list.
      apply FC.
      reflexivity.
      apply PSV.
      rewrite PF.
      apply FS2. }
Admitted.

(*
Proof.
intros P E PSV.
induction P; try intros S FS;
unfold dub_neg_sub_ptree;
rewrite FS;
unfold ptree_formula in *; fold ptree_formula in *;
unfold dub_neg_sub_ptree_fit; fold dub_neg_sub_ptree_fit.

all : try apply PSV.

1 : { destruct PSV as [PSV PL].
      rewrite (dub_neg_ptree_formula_true _ _ _ FS).
      repeat split;
      unfold node_extract;
      fold node_extract.
      - apply (IHP PSV _ FS).
      - rewrite <- (dub_neg_node_size _ _ _ PSV FS).
        apply PL. }

1 : { destruct PSV as [PSV [L [A PN]]].
      rewrite (dub_neg_ptree_formula_true _ _ _ FS).
      repeat split;
      unfold node_extract;
      fold node_extract.
      - apply (IHP PSV _ FS).
      - exists (tl (tl (dub_neg_trans (combine (node_extract P) (dub_neg_node P S)) E))).
        exists (hd (atom (equ zero zero)) (dub_neg_trans (combine (node_extract P) (dub_neg_node P S)) E)).
        rewrite hd_tl.
        
        apply PN.
      - apply PAX.
      - apply FS. }

1 : destruct PSV as [PSV DU].
2 : destruct PSV as [[PSV OU] NO].
3-11 : destruct PSV as [[[PF PSV] PD] PO].
12 : destruct PSV as [[[[PF PSV] PD] PO] FC].
13-16 : destruct PSV as [[[[[[[P1F P1SV] P1D] P1O] P2F] P2SV] P2D] P2O].
17 : destruct PSV as [[[[[[[[[[P1F P1SV] P1D] P1O] P2F] P2SV] P2D] P2O] P2N] NINA] FREEA].

3-6,8-13,16,17 : 
    destruct S; inversion FS as [FS'];
    try destruct (and_bool_prop _ _ FS') as [FS1 FS2].

4-6,10 :  destruct S1; inversion FS' as [FS''];
          try destruct (and_bool_prop _ _ FS1) as [FS1_1 FS1_2].

6 : destruct S1_1; inversion FS'' as [FS'''];
    destruct (and_bool_prop _ _ FS1_1) as [FS1_1_1 FS1_1_2].

8,11 : case (form_eqb a E) eqn:EQ.

18  : { repeat rewrite dub_neg_ptree_formula_true;
        repeat split;
        try rewrite dub_neg_ptree_formula;
        try rewrite dub_neg_ptree_deg;
        try rewrite dub_neg_ptree_ord;
        try rewrite P1F;
        try rewrite P2F;
        try rewrite P1D;
        try rewrite P2D;
        try rewrite P1O;
        try rewrite P2O;
        try apply P1SV;
        try apply P2SV;
        unfold dub_neg_sub_formula;
        try rewrite formula_sub_ind_lor;
        try rewrite non_target_sub_term;
        unfold subst_ind_fit;
        fold subst_ind_fit;
        try rewrite FS1;
        try rewrite non_target_sub_fit;
        try reflexivity.

        - apply (IHP1 P1SV (proj2 (axiom_app_split _ _ PAX)) (lor_ind S1 (non_target a))).
          rewrite P1F;
          unfold subst_ind_fit;
          fold subst_ind_fit;
          try rewrite FS1;
          try rewrite non_target_sub_fit;
          try reflexivity.
        - admit.
        - admit.
        - intros IN.
          pose proof (closed_free_list _ (axiom_closed _ (PAX _ (in_or_app _ _ _ (or_introl IN))))) as FAL.
          unfold free_list in FAL;
          fold free_list in FAL.
          apply nodup_nil, app_eq_nil in FAL as [_ FAL].
          rewrite FAL in FREEA.
          inversion FREEA.
        - apply FREEA.
        - unfold node_extract;
          fold node_extract.
          rewrite dub_neg_valid_node.
          apply PAX.
          apply (P1SV,(proj2 (axiom_app_split _ _ PAX))).
          rewrite P1F;
          unfold subst_ind_fit;
          fold subst_ind_fit;
          try rewrite FS1;
          try rewrite non_target_sub_fit;
          try reflexivity. }

all : try apply form_eqb_eq in EQ;
      try destruct EQ;
      repeat rewrite dub_neg_ptree_formula_true;
      repeat split;
      try apply IHP;
      try apply IHP1;
      try apply IHP2;
      try rewrite dub_neg_ptree_deg;
      try rewrite dub_neg_ptree_ord;
      try rewrite dub_neg_ptree_formula;
      try rewrite PF;
      try rewrite P1F;
      try rewrite P2F;
      unfold dub_neg_sub_formula, formula_sub_ind;
      try apply (PSV,PAX);
      try rewrite PD;
      try rewrite PO;
      try apply P1SV;
      try apply (P1SV,(fun B INB => PAX B (proj2 (in_app_iff _ _ _) (or_introl INB))));
      try rewrite P1D;
      try rewrite P1O;
      try apply P2SV;
      try apply (P2SV,(fun B INB => PAX B (proj2 (in_app_iff _ _ _) (or_intror INB))));
      try rewrite P2D;
      try rewrite P2O;
      try apply DU;
      try apply OU;
      try apply NO;
      try apply INA;
      unfold subst_ind_fit; fold subst_ind_fit;
      try rewrite non_target_fit;
      try rewrite non_target_sub_fit;
      try rewrite FS;
      try rewrite FS';
      try rewrite FS'';
      try rewrite FS1;
      try rewrite FS1_1;
      try rewrite FS1_2;
      try rewrite FS1_1_1;
      try rewrite FS1_1_2;
      try rewrite FS2;
      unfold node_extract;
      fold node_extract;
      try apply (fun B INB => PAX B (proj2 (in_app_iff _ _ _) (or_introl INB)));
      try apply (fun B INB => PAX B (proj2 (in_app_iff _ _ _) (or_intror INB)));
      unfold "&&";
      unfold formula_sub_ind_fit; fold formula_sub_ind_fit;
      unfold form_eqb; fold form_eqb;
      try rewrite non_target_sub_term';
      try rewrite non_target_sub';
      try rewrite <- (sub_fit_true _ _ _ _ FS1);
      try case form_eqb eqn:FEQ;
      try reflexivity.

1,3 : apply ord_succ_monot.

1,2 : try apply nf_nf_succ;
      try apply ptree_ord_nf_struct;
      try apply PSV.

1 : { try rewrite <- (dub_neg_node_eq _ _ _ PSV).
      unfold formula_sub_ind.
      rewrite FS1.
      rewrite formula_sub_ind_free_list.
      apply (incl_tran FC), (dub_neg_free_sub _ _ _ PSV).
      rewrite PF.
      apply FS2.
      reflexivity. }

all : intros A IN;
      try apply in_app_or in IN as [IN1 | IN2];
      try apply (fun FSUB => dub_neg_all_ax_trans _ _ _ P1SV FSUB (fun B INB1 => PAX B (in_or_app _ _ _ (or_introl INB1))) _ IN1);
      try apply (fun FSUB => dub_neg_all_ax_trans _ _ _ P2SV FSUB (fun B INB2 => PAX B (in_or_app _ _ _ (or_intror INB2))) _ IN2);
      try rewrite P1F;
      try rewrite P2F;
      unfold subst_ind_fit;
      fold subst_ind_fit;
      try rewrite FS;
      try rewrite FS1;
      try rewrite FS2;
      try rewrite non_target_fit;
      try apply ((fun B INB1 => PAX B (in_or_app _ _ _ (or_introl INB1))) _ IN1);
      try apply ((fun B INB2 => PAX B (in_or_app _ _ _ (or_intror INB2))) _ IN2);
      try reflexivity.
Qed.
*)

Lemma dub_neg_valid :
    forall (P : ptree) (E : formula),
        valid P ->
            forall (S : subst_ind),
                subst_ind_fit (ptree_formula P) S = true ->
                    valid (dub_neg_sub_ptree P E S).
Proof.
intros P E [PSV PAX].
induction P; try intros S FS;
unfold dub_neg_sub_ptree;
rewrite FS;
unfold ptree_formula in *; fold ptree_formula in *;
unfold dub_neg_sub_ptree_fit; fold dub_neg_sub_ptree_fit.

all : try apply (PSV,PAX).

1 : { repeat split.
      unfold node_extract in *.
      specialize (PAX _ (or_introl eq_refl)).
      intros A IN.
      destruct a;
      try destruct a;
      inversion PAX as [AX'];
      unfold dub_neg_sub_formula, formula_sub_ind, formula_sub_ind_fit, form_eqb in IN;
      rewrite FS in IN;
      inversion IN as [EQ | FAL];
      try inversion FAL;
      destruct EQ;
      reflexivity. }

1 : { destruct PSV as [PSV PL].
      pose proof (fun A INA => PAX A (proj1 (in_bury _) INA)) as PAX2.
      destruct (IHP PSV PAX2 _ FS) as [PSV' PAX'].
      rewrite dub_neg_ptree_formula_true.
      repeat split;
      unfold node_extract;
      fold node_extract.
      - apply PSV'.
      - rewrite <- (dub_neg_node_size _ _ _ PSV FS).
        apply PL.
      - apply (fun A INA => PAX' A (proj2 (in_bury _) INA)).
      - apply FS. }

1 : destruct PSV as [PSV DU].
2 : destruct PSV as [[PSV OU] NO].
3-11 : destruct PSV as [[[PF PSV] PD] PO].
12 : destruct PSV as [[[[PF PSV] PD] PO] FC].
13-16 : destruct PSV as [[[[[[[P1F P1SV] P1D] P1O] P2F] P2SV] P2D] P2O].
17 :  pose proof PSV as PSV'; 
      destruct PSV as [[[[[[[[[P1F P1SV] P1D] P1O] P2F] P2SV] P2D] P2O] [L P2N]] FREEA].

3-6,8-13,16,17 : 
    destruct S; inversion FS as [FS'];
    try destruct (and_bool_prop _ _ FS') as [FS1 FS2].

4-6,10 :  destruct S1; inversion FS' as [FS''];
          try destruct (and_bool_prop _ _ FS1) as [FS1_1 FS1_2].

6 : destruct S1_1; inversion FS'' as [FS'''];
    destruct (and_bool_prop _ _ FS1_1) as [FS1_1_1 FS1_1_2].

8,11 : case (form_eqb a E) eqn:EQ.

18  : { repeat rewrite dub_neg_ptree_formula_true;
        repeat split;
        try rewrite dub_neg_ptree_formula;
        try rewrite dub_neg_ptree_deg;
        try rewrite dub_neg_ptree_ord;
        try rewrite P1F;
        try rewrite P2F;
        try rewrite P1D;
        try rewrite P2D;
        try rewrite P1O;
        try rewrite P2O;
        try apply P1SV;
        try apply P2SV;
        unfold dub_neg_sub_formula;
        try rewrite formula_sub_ind_lor;
        try rewrite non_target_sub_term;
        unfold subst_ind_fit;
        fold subst_ind_fit;
        try rewrite FS1;
        try rewrite non_target_sub_fit;
        try reflexivity.

        - apply (IHP1 P1SV (proj2 (axiom_app_split _ _ PAX)) (lor_ind S1 (non_target a))).
          rewrite P1F;
          unfold subst_ind_fit;
          fold subst_ind_fit;
          try rewrite FS1;
          try rewrite non_target_sub_fit;
          try reflexivity.
        - apply (dub_neg_structural _ _ P2SV).
          rewrite P2F;
          unfold subst_ind_fit;
          fold subst_ind_fit;
          rewrite FS1.
          apply non_target_sub_fit.
        - assert (subst_ind_fit (ptree_formula P2) (lor_ind S1 (non_target a)) = true) as FIT2.
          { rewrite P2F.
            unfold subst_ind_fit;
            fold subst_ind_fit;
            rewrite FS1, non_target_sub_fit;
            unfold "&&";
            reflexivity. }
          refine (existT _ L _).
          pose proof (dub_neg_structural _ E PSV' (lor_ind S1 S2) FS') as HELP.
          unfold dub_neg_sub_ptree, dub_neg_node, dub_neg_sub_ptree_fit, dub_neg_node_fit in HELP;
          fold dub_neg_sub_ptree_fit dub_neg_node_fit in HELP.
          unfold ptree_formula, subst_ind_fit in HELP;
          fold ptree_formula subst_ind_fit in HELP.
          rewrite FS' in HELP.
          destruct HELP as [[[[[[[[[P1F' P1SV'] P1D'] P1O'] P2F'] P2SV'] P2D'] P2O'] [L' P2N']] FREEA'].
          rewrite (dub_neg_ptree_formula_true _ _ _ FIT2) in P2N'.
          rewrite <- P2N'.
          pose proof (dub_neg_tail_valid_node _ E P2SV (fun A INA => PAX _ (in_or_app _ _ _ (or_introl INA))) _ FIT2) as EQ.
          rewrite <- P2N, <- P2N' in EQ.
          unfold tl in EQ.
          rewrite EQ.
          reflexivity.
        - apply FREEA.
        - unfold node_extract;
          fold node_extract.
          intros A INA.
          apply in_app_or in INA as [IN2 | IN1].
          + destruct (In_nth _ _ A IN2) as [x [LT ID]].
            rewrite nth_tail in ID.
            assert (PA_cyclic_axiom (nth (S x) (node_extract P2) A) = true) as AX.
            { apply PAX.
              unfold node_extract;
              fold node_extract.
              rewrite <- nth_tail.
              apply in_or_app, or_introl, nth_In.
              rewrite (@tail_len_eq _ _ _ (node_extract (dub_neg_sub_ptree P2 E (lor_ind S1 (non_target a))))).
              apply LT.
              apply (dub_neg_node_size P2 E (lor_ind S1 (non_target a)) P2SV).
              rewrite P2F.
              unfold subst_ind_fit;
              fold subst_ind_fit.
              rewrite FS1.
              apply non_target_sub_fit. }
            rewrite <- ID.
            rewrite <- (dub_neg_axiom_nth_eq _ E (lor_ind S1 (non_target a)) P2SV);
            try apply AX.
            rewrite P2F.
            unfold subst_ind_fit;
            fold subst_ind_fit.
            rewrite FS1.
            apply non_target_sub_fit.
            
          + destruct (IHP1 P1SV (fun B INB => PAX B (proj2 (in_app_iff _ _ _) (or_intror INB))) (lor_ind S1 (non_target a))) as [P1SV' PAX1].
            rewrite P1F.
            unfold subst_ind_fit;
            fold subst_ind_fit.
            rewrite FS1.
            apply non_target_sub_fit.
            apply (PAX1 _ IN1). }

all : try apply form_eqb_eq in EQ;
      try destruct EQ;
      repeat rewrite dub_neg_ptree_formula_true;
      repeat split;
      try apply IHP;
      try apply IHP1;
      try apply IHP2;
      try rewrite dub_neg_ptree_deg;
      try rewrite dub_neg_ptree_ord;
      try rewrite dub_neg_ptree_formula;
      try rewrite PF;
      try rewrite P1F;
      try rewrite P2F;
      unfold dub_neg_sub_formula, formula_sub_ind;
      try apply (PSV,PAX);
      try rewrite PD;
      try rewrite PO;
      try apply P1SV;
      try apply (P1SV,(fun B INB => PAX B (proj2 (in_app_iff _ _ _) (or_introl INB))));
      try rewrite P1D;
      try rewrite P1O;
      try apply P2SV;
      try apply (P2SV,(fun B INB => PAX B (proj2 (in_app_iff _ _ _) (or_intror INB))));
      try rewrite P2D;
      try rewrite P2O;
      try apply DU;
      try apply OU;
      try apply NO;
      try apply INA;
      unfold subst_ind_fit; fold subst_ind_fit;
      try rewrite non_target_fit;
      try rewrite non_target_sub_fit;
      try rewrite FS;
      try rewrite FS';
      try rewrite FS'';
      try rewrite FS1;
      try rewrite FS1_1;
      try rewrite FS1_2;
      try rewrite FS1_1_1;
      try rewrite FS1_1_2;
      try rewrite FS2;
      unfold node_extract;
      fold node_extract;
      try apply (fun B INB => PAX B (proj2 (in_app_iff _ _ _) (or_introl INB)));
      try apply (fun B INB => PAX B (proj2 (in_app_iff _ _ _) (or_intror INB)));
      unfold "&&";
      unfold formula_sub_ind_fit; fold formula_sub_ind_fit;
      unfold form_eqb; fold form_eqb;
      try rewrite non_target_sub_term';
      try rewrite non_target_sub';
      try rewrite <- (sub_fit_true _ _ _ _ FS1);
      try case form_eqb eqn:FEQ;
      try reflexivity.

1,3 : apply ord_succ_monot.

1,2 : try apply nf_nf_succ;
      try apply ptree_ord_nf_struct;
      try apply PSV.

1 : { rewrite <- dub_neg_free_sub.
      unfold formula_sub_ind.
      rewrite FS1.
      rewrite formula_sub_ind_free_list.
      apply FC.
      reflexivity.
      apply PSV.
      rewrite PF.
      apply FS2. }

all : intros A IN;
      try apply in_app_or in IN as [IN1 | IN2];
      try apply (fun FSUB => dub_neg_all_ax_trans _ _ _ P1SV FSUB (fun B INB1 => PAX B (in_or_app _ _ _ (or_introl INB1))) _ IN1);
      try apply (fun FSUB => dub_neg_all_ax_trans _ _ _ P2SV FSUB (fun B INB2 => PAX B (in_or_app _ _ _ (or_intror INB2))) _ IN2);
      try rewrite P1F;
      try rewrite P2F;
      unfold subst_ind_fit;
      fold subst_ind_fit;
      try rewrite FS;
      try rewrite FS1;
      try rewrite FS2;
      try rewrite non_target_fit;
      try apply ((fun B INB1 => PAX B (in_or_app _ _ _ (or_introl INB1))) _ IN1);
      try apply ((fun B INB2 => PAX B (in_or_app _ _ _ (or_intror INB2))) _ IN2);
      try reflexivity.
Qed.