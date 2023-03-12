From Cyclic_PA.Maths Require Import naturals.
From Cyclic_PA.Maths Require Import lists.
From Cyclic_PA.Maths Require Import ordinals.

From Cyclic_PA.Logic Require Import definitions.
From Cyclic_PA.Logic Require Import fol.
From Cyclic_PA.Logic Require Import proof_trees.
From Cyclic_PA.Logic Require Import substitute.
From Cyclic_PA.Logic Require Import PA_cyclic.

Require Import List.
Import ListNotations.

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

| node A, _ => P

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
      P2

| loop_ad A D n d1 d2 alpha1 alpha2 P1 P2, (lor_ind SA SD) =>
    loop_ad
      A (dub_neg_sub_formula D E SD)
      n d1 d2 alpha1 alpha2
      P1 (dub_neg_sub_ptree_fit P2 E (lor_ind (non_target A) SD))

| loop_cad C A D n d1 d2 alpha1 alpha2 P1 P2, (lor_ind (lor_ind SC SA) SD) =>
    loop_cad
      (dub_neg_sub_formula C E SC)
      A
      (dub_neg_sub_formula D E SD)
      n d1 d2 alpha1 alpha2
      (dub_neg_sub_ptree_fit P1 E (lor_ind SC (non_target A)))
      (dub_neg_sub_ptree_fit P2 E (lor_ind (non_target A) SD))

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

Definition dub_neg_sub_ptree (P : ptree) (E : formula) (S : subst_ind) : ptree :=
match subst_ind_fit (ptree_formula P) S with
| false => P
| true => dub_neg_sub_ptree_fit P E S
end.

Lemma dub_neg_ptree_formula_true :
    forall (P : ptree) (E : formula) (S : subst_ind),
        subst_ind_fit (ptree_formula P) S = true ->
            dub_neg_sub_ptree_fit P E S = dub_neg_sub_ptree P E S.
Proof. intros. unfold dub_neg_sub_ptree. destruct P; rewrite H; auto. Qed.

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

Lemma dub_neg_ptree_formula_struct : forall (P : ptree) (E : formula),
  struct_valid P ->
      forall (S : subst_ind),
          subst_ind_fit (ptree_formula P) S = true ->
              (forall A : formula, In A (node_extract P) /\ (PA_cyclic_axiom A = false) -> ~ In A (target_check (ptree_formula P) S)) ->
                ptree_formula (dub_neg_sub_ptree P E S) =
                    dub_neg_sub_formula (ptree_formula P) E S.
Proof.
intros P E PSV.
induction P.

3 : { induction a;
      try intros S FS NonTar;
      unfold dub_neg_sub_ptree;
      rewrite FS;
      unfold ptree_formula, node_extract in *; fold ptree_formula node_extract in *;
      unfold dub_neg_sub_ptree_fit; fold dub_neg_sub_ptree_fit;
      try case PA_cyclic_axiom eqn:AX;
      unfold dub_neg_sub_formula, formula_sub_ind;
      rewrite FS;
      unfold formula_sub_ind_fit;
      fold formula_sub_ind_fit;
      unfold form_eqb, ptree_formula;
      fold form_eqb;
      try reflexivity;
      destruct S;
      inversion FS as [FS'];
      try case form_eqb eqn:EQ;
      try reflexivity.
      - specialize (NonTar (neg a)).
        case (PA_cyclic_axiom (neg a)) eqn:AX.
        + apply form_eqb_eq in EQ.
          rewrite EQ in AX.
          inversion AX.
        + pose proof (target_check_not_mem_idem (neg a) (neg a) E (1) (NonTar (conj (or_introl eq_refl) eq_refl))) as FAL.
          unfold formula_sub_ind, subst_ind_fit, formula_sub_ind_fit in FAL.
          rewrite form_eqb_refl in FAL.
          rewrite FAL.
          reflexivity.
      - specialize (NonTar (lor a1 a2)).
        case (PA_cyclic_axiom (lor a1 a2)) eqn:AX.
        + inversion AX.
        + apply and_bool_prop in FS' as [FS1 FS2].
          specialize (IHa1 eq_refl _ FS1).
          specialize (IHa2 eq_refl _ FS2).
          case (PA_cyclic_axiom a1) eqn:AX1;
          case (PA_cyclic_axiom a2) eqn:AX2;
          unfold formula_sub_ind_fit;
          fold formula_sub_ind_fit;
          try pose proof (dub_neg_axiom_id _ E S1 AX1) as EQ1;
          try pose proof (dub_neg_axiom_id _ E S2 AX2) as EQ2;
          unfold dub_neg_sub_formula, formula_sub_ind in *;
          rewrite FS1 in *;
          rewrite FS2 in *;
          try rewrite EQ1;
          try rewrite EQ2;
          try reflexivity.
          pose proof target_check_not_mem_idem.
          pose proof (IHa2 _ (conj (or_introl eq_refl) AX2)).
          
  
 unfold dub_neg_sub_formula, ptree_formula.
  symmetry.
  apply target_check_not_mem_idem.
  unfold target_check; fold target_check.
  apply (check_not_mem_nil _ _ FS (NonTar (conj (or_introl eq_refl) eq_refl))). *) }

all : try intros S FS NonTar;
      unfold dub_neg_sub_ptree;
      rewrite FS;
      unfold ptree_formula, node_extract in *; fold ptree_formula node_extract in *;
      unfold dub_neg_sub_ptree_fit; fold dub_neg_sub_ptree_fit.
  
1 : destruct PSV as [ID PSV].
2 : destruct PSV as [[IO PSV] NO].
12-13 : destruct PSV as [[[PF PSV] PD] PO].

1-2 : rewrite (dub_neg_ptree_formula_true _ _ _ FS);
      unfold ptree_formula; fold ptree_formula;
      apply (IHP PSV _ FS NonTar).

5 : reflexivity.

all : destruct S;
      inversion FS as [FS'];
      try reflexivity;
      try apply and_bool_prop in FS' as [FS' FS1];
      unfold ptree_formula, dub_neg_sub_formula, formula_sub_ind, formula_sub_ind_fit, subst_ind_fit, form_eqb;
      fold form_eqb formula_sub_ind_fit ptree_formula subst_ind_fit.

8-10 :  case (form_eqb a E) eqn:FEQ;
        try reflexivity;
        try apply form_eqb_eq in FEQ;
        try destruct FEQ;
        try apply PF.

2-4,7-10,12,13 :  destruct S1;
                  inversion FS' as [FS''];
                  try apply and_bool_prop in FS' as [FS' FS2].

4 : destruct S1_1;
    inversion FS'' as [FS'''];
    apply and_bool_prop in FS' as [FS' FS3].

16 :  destruct S1_2;
      inversion FS2 as [FS'''];
      apply and_bool_prop in FS'' as [FS'' FS3].

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

2,3,5 : rewrite non_target_fit, FS1;
        reflexivity.

1 : unfold formula_sub_ind.
    rewrite FS1.
    reflexivity.

1 : intros A [IN AXn] FAL.
    unfold target_check in *;
    fold target_check in *.
    rewrite target_check_non_target, app_nil_l in FAL.
    rewrite <- app_comm_cons in NonTar.
    destruct (target_check d S2).
    - inversion FAL.
    - rewrite app_nil_l in NonTar.
      apply (NonTar _ (conj IN AXn) (or_intror FAL)).
Qed.

Lemma dub_neg_ptree_formula' : forall (P : ptree) (E : formula),
  valid P ->
      forall (S : subst_ind),
          subst_ind_fit (ptree_formula P) S = true ->
              ptree_formula (dub_neg_sub_ptree P E S) =
                  dub_neg_sub_formula (ptree_formula P) E S.
Proof.
intros P E [PSV PAX].
induction P; try intros S FS;
unfold dub_neg_sub_ptree;
rewrite FS;
unfold ptree_formula, node_extract in *; fold ptree_formula node_extract in *;
unfold dub_neg_sub_ptree_fit; fold dub_neg_sub_ptree_fit.
  
1 : destruct PSV as [ID PSV].
2 : destruct PSV as [[IO PSV] NO].
13-14 : destruct PSV as [[[PF PSV] PD] PO].

1-2 : rewrite (dub_neg_ptree_formula_true _ _ _ FS);
      unfold ptree_formula; fold ptree_formula;
      apply (IHP PSV PAX _ FS).

1 : { specialize (PAX _ (or_introl eq_refl)). 
      unfold PA_cyclic_axiom in PAX.
      unfold dub_neg_sub_formula, formula_sub_ind, formula_sub_ind_fit.
      destruct a;
      inversion PAX as [AX'];
      destruct S;
      unfold subst_ind_fit, form_eqb;
      fold form_eqb;
      try apply IN;
      destruct a;
      inversion PAX as [AX''];
      unfold form_eqb;
      reflexivity. }

5 : reflexivity.

all : destruct S;
      inversion FS as [FS'];
      try reflexivity;
      try apply and_bool_prop in FS' as [FS' FS1];
      unfold ptree_formula, dub_neg_sub_formula, formula_sub_ind, formula_sub_ind_fit, subst_ind_fit, form_eqb;
      fold form_eqb formula_sub_ind_fit ptree_formula subst_ind_fit.

8-10 :  case (form_eqb a E) eqn:FEQ;
        try reflexivity;
        try apply form_eqb_eq in FEQ;
        try destruct FEQ;
        try apply PF.

2-4,7-10,12,13 :  destruct S1;
                  inversion FS' as [FS''];
                  try apply and_bool_prop in FS' as [FS' FS2].

4 : destruct S1_1;
    inversion FS'' as [FS'''];
    apply and_bool_prop in FS' as [FS' FS3].

16 :  destruct S1_2;
      inversion FS2 as [FS'''];
      apply and_bool_prop in FS'' as [FS'' FS3].

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

1 : rewrite dub_neg_ptree_formula_true, (IHP PSV PAX);
    try rewrite PF;
    unfold dub_neg_sub_formula, subst_ind_fit;
    fold subst_ind_fit.
    rewrite formula_sub_ind_lor, non_target_sub.

2-4 : rewrite non_target_fit, FS1;
      reflexivity.

1 : unfold formula_sub_ind.
    rewrite FS1.
    reflexivity.
Qed.

Lemma dub_neg_ptree_formula :
    forall (P : ptree) (E : formula),
        valid P ->
            forall (S : subst_ind),
                ptree_formula (dub_neg_sub_ptree P E S) =
                    dub_neg_sub_formula (ptree_formula P) E S.
Proof.
intros P E [PSV PAX] S.
destruct (subst_ind_fit (ptree_formula P) S) eqn:FS.
- apply (dub_neg_ptree_formula' _ _ (PSV,PAX) _ FS).
- unfold dub_neg_sub_ptree, dub_neg_sub_formula, formula_sub_ind.
  rewrite FS.
  reflexivity.
Qed.

Lemma dub_neg_ptree_deg :
    forall (P : ptree) (E : formula),
        valid P ->
            forall (S : subst_ind),
                ptree_deg (dub_neg_sub_ptree P E S) = ptree_deg P.
Proof.
intros P E [PSV PAX].
unfold dub_neg_sub_ptree.
pose (ptree_formula P) as A.
induction P; intros S;
case (subst_ind_fit A S) eqn:FS;
unfold A in FS;
try rewrite FS;
unfold dub_neg_sub_ptree_fit; fold dub_neg_sub_ptree_fit;
unfold ptree_deg in *; fold ptree_deg in *;
try reflexivity.

1 : destruct PSV as [[IO PSV] NO].

9,10 : destruct PSV as [[[PF PSV] PD] PO].

1 : unfold ptree_formula in FS; fold ptree_formula in FS.
    pose proof (IHP PSV PAX S) as IHPS.
    rewrite FS in IHPS.
    apply IHPS.

all : destruct S; inversion FS as [FS'];
      try reflexivity.

4-6 : case (form_eqb a E) eqn:EQ;
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
  pose proof (IHP PSV PAX (lor_ind (non_target a) S2)) as IHPS.
  rewrite FSP in IHPS.
  apply IHPS.
Qed.

Lemma dub_neg_ptree_deg_struct :
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

1 : destruct PSV as [[IO PSV] NO].

9,10 : destruct PSV as [[[PF PSV] PD] PO].

1 : unfold ptree_formula in FS; fold ptree_formula in FS.
    pose proof (IHP PSV S) as IHPS.
    rewrite FS in IHPS.
    apply IHPS.

all : destruct S; inversion FS as [FS'];
      try reflexivity.

4-6 : case (form_eqb a E) eqn:EQ;
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
        valid P ->
            forall (S : subst_ind),
                (ptree_ord (dub_neg_sub_ptree P E S)) = (ptree_ord P).
Proof.
intros P E [PSV PAX].
unfold dub_neg_sub_ptree.
pose (ptree_formula P) as A.
induction P; intros S;
case (subst_ind_fit A S) eqn:FS;
unfold A in FS;
try rewrite FS;
unfold dub_neg_sub_ptree_fit; fold dub_neg_sub_ptree_fit;
unfold ptree_ord in *; fold ptree_ord in *;
try reflexivity.

1 : destruct PSV as [ID PSV].

9,10 : destruct PSV as [[[PF PSV] PD] PO].

1 : unfold ptree_formula in FS; fold ptree_formula in FS.
    pose proof (IHP PSV PAX S) as IHPS.
    rewrite FS in IHPS.
    apply IHPS.

all : destruct S; inversion FS as [FS'];
      try reflexivity.

4-6 : case (form_eqb a E) eqn:EQ;
      unfold ptree_deg; fold ptree_deg;
      try rewrite PD;
      try reflexivity.

all : destruct S1; inversion FS' as [FS''].

3 : destruct S1_1; inversion FS'' as [FS'''].

all : unfold ptree_deg; fold ptree_deg;
      try reflexivity.
Qed.

Lemma dub_neg_ptree_ord_struct :
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

1 : destruct PSV as [ID PSV].

9,10 : destruct PSV as [[[PF PSV] PD] PO].

1 : unfold ptree_formula in FS; fold ptree_formula in FS.
    pose proof (IHP PSV S) as IHPS.
    rewrite FS in IHPS.
    apply IHPS.

all : destruct S; inversion FS as [FS'];
      try reflexivity.

4-6 : case (form_eqb a E) eqn:EQ;
      unfold ptree_deg; fold ptree_deg;
      try rewrite PD;
      try reflexivity.

all : destruct S1; inversion FS' as [FS''].

3 : destruct S1_1; inversion FS'' as [FS'''].

all : unfold ptree_deg; fold ptree_deg;
      try reflexivity.
Qed.

(*
Lemma dub_neg_sub_free : 
    forall (A E : formula) (S : subst_ind),
        incl (free_list A) (free_list (dub_neg_sub_formula A E S)).
Proof.
induction A;
intros E S m IN;
unfold dub_neg_sub_formula, formula_sub_ind in *;
case subst_ind_fit eqn:FS;
try apply IN.
- unfold formula_sub_ind_fit.
  case form_eqb eqn:EQ;
  destruct S;
  try apply IN.
  apply form_eqb_eq in EQ.
  rewrite EQ in IN.
  apply IN.
- destruct S;
  inversion FS as [FS'].
  apply and_bool_prop in FS' as [FS1 FS2].
  unfold formula_sub_ind_fit;
  fold formula_sub_ind_fit.
  pose proof (IHA1 E S1) as IH1.
  rewrite FS1 in IH1.
  pose proof (IHA2 E S2) as IH2.
  rewrite FS2 in IH2.
  apply nodup_In,in_app_iff in IN as [IN1 | IN2].
  + apply nodup_In, in_app_iff, or_introl, IH1, IN1.
  + apply nodup_In, in_app_iff, or_intror, IH2, IN2.
Qed.
*)

Lemma dub_neg_node_eq_aux :
    forall (alpha : ord),
        nf alpha ->
            (forall (P : ptree) (E : formula) (S : subst_ind),
                alpha = ptree_ord P ->
                    struct_valid P ->
                        subst_ind_fit (ptree_formula P) S = true ->
                            node_extract P = node_extract (dub_neg_sub_ptree P E S)).
Proof.
apply (transfinite_induction (fun (alpha : ord) => (forall (P : ptree) (E : formula) (S : subst_ind), alpha = ptree_ord P -> struct_valid P -> subst_ind_fit (ptree_formula P) S = true -> node_extract P = node_extract (dub_neg_sub_ptree P E S)))).
intros alpha NA IND.
induction P;
intros E S EQ PSV FS;
unfold dub_neg_sub_ptree;
unfold node_extract, dub_neg_sub_ptree_fit, ptree_formula, ptree_ord in *;
fold ptree_formula ptree_ord dub_neg_sub_ptree_fit in *;
rewrite FS in *;
fold node_extract in *;
try rewrite (dub_neg_ptree_formula_true _ _ _ FS).

1 : destruct PSV as [LT PSV]. (*deg up*)
2 : destruct PSV as [[LT PSV] NO]. (*ord up*)
3 : destruct PSV as []. (*node*)
4-9,13-16 :  destruct PSV as [[[PF PSV] PD] PO]. (*single hyp*)
14 : destruct PSV as [[[[PF CPF] PSV] PD] PO]. (*weakening*)
15-23 : destruct PSV as [[[[[[[P1F P1SV] P2F] P2SV] P1D] P2D] P1O] P2O]. (*double hyp*)

1 : apply (IHP _ _ EQ PSV FS).

1 : destruct EQ;
    apply (IND _ (ptree_ord_nf_struct _ PSV) LT _ _ _ eq_refl PSV FS).

all : try reflexivity;
      destruct S;
      inversion FS as [FS'];
      try apply and_bool_prop in FS' as [FS1 FS2];
      rewrite EQ in *.

2-4,11,12,14,16,17 : destruct S1;
            inversion FS as [FS'];
            try apply and_bool_prop in FS1 as [FS1 FS3].

4 : destruct S1_1;
    inversion FS as [FS''];
    try apply and_bool_prop in FS1 as [FS1 FS4].

6,19 : case form_eqb eqn:EQ'.

16 :  destruct S1_2;
      inversion FS as [FS''];
      try apply and_bool_prop in FS3 as [FS3 FS4].

all : unfold node_extract;
      fold node_extract;
      repeat rewrite dub_neg_ptree_formula_true;
      try apply (IHP _ _ PO);
      try refine (IND _ (ptree_ord_nf_struct_hyp _ _ PO PSV) (ord_succ_monot _) _ _ _ PO PSV _);
      try rewrite <- (IND _ (ptree_ord_nf_struct_hyp _ _ P1O P1SV) (ord_lt_max_succ_l _ _) _ _ (lor_ind _ (non_target a)) P1O P1SV);
      try rewrite <- (IND _ (ptree_ord_nf_struct_hyp _ _ P1O P1SV) (ord_lt_max_succ_l _ _) _ _ (lor_ind (0) S2) P1O P1SV);
      try rewrite <- (IND _ (ptree_ord_nf_struct_hyp _ _ P2O P2SV) (ord_lt_max_succ_r _ _) _ _ (lor_ind (0) _) P2O P2SV);
      try rewrite <- (IND _ (ptree_ord_nf_struct_hyp _ _ P2O P2SV) (ord_lt_trans _ _ _ (ord_lt_max_succ_r _ _) (ord_succ_monot _)) _ _ _ P2O P2SV);
      try rewrite PF;
      try rewrite P1F;
      try rewrite P2F;
      unfold subst_ind_fit;
      fold subst_ind_fit;
      try apply andb_true_intro;
      repeat rewrite andb_true_intro;
      try rewrite non_target_fit;
      try rewrite non_target_sub_fit;
      auto.

all : repeat rewrite <- dub_neg_sub_formula_closed;
      try case (closed c) eqn:CC;
      try case (closed d) eqn:CD;
      destruct (free_list a);
      try destruct l;
      try case nat_eqb eqn:EQ';
      try rewrite <- (IND _ (ptree_ord_nf_struct_hyp _ _ P1O P1SV) (lt_succ_mult_add_r _ _) _ _ _ P1O P1SV);
      try rewrite <- (IND _ (ptree_ord_nf_struct_hyp _ _ P2O P2SV) (lt_succ_mult_add_l _ _) _ _ _ P2O P2SV);
      try reflexivity;
      try rewrite P1F;
      try rewrite P2F;
      unfold subst_ind_fit;
      fold subst_ind_fit;
      try apply andb_true_intro;
      repeat rewrite andb_true_intro;
      try rewrite non_target_fit;
      try rewrite non_target_sub_fit;
      auto.
Qed.

Lemma dub_neg_node_eq :
    (forall (P : ptree) (E : formula) (S : subst_ind),
        struct_valid P ->
                node_extract P = node_extract (dub_neg_sub_ptree P E S)).
Proof.
intros P E S PSV.
unfold dub_neg_sub_ptree.
case subst_ind_fit eqn:FS.
- rewrite (dub_neg_ptree_formula_true _ _ _ FS).
  apply (dub_neg_node_eq_aux (ptree_ord P) (ptree_ord_nf_struct _ PSV) _ _ _ eq_refl PSV FS).
- reflexivity.
Qed.

(*Lemma problem : 
ptree_formula P = lor a d
subst_ind_fit d S = true
closed d = true
struct_valid (dub_neg_sub_ptree P E (lor_ind (non_target a) S))*)

Lemma dub_neg_valid :
    forall (P : ptree) (E : formula),
        struct_valid P ->
            forall (S : subst_ind),
                subst_ind_fit (ptree_formula P) S = true ->
                    (forall A : formula, In A (node_extract P) /\ (PA_cyclic_axiom A = false) -> ~ In A (target_check (ptree_formula P) S)) ->
                        struct_valid (dub_neg_sub_ptree P E S).
Proof.
intros P E PSV.
induction P; try intros S FS NonTar;
unfold dub_neg_sub_ptree;
rewrite FS;
unfold ptree_formula in *; fold ptree_formula in *;
unfold dub_neg_sub_ptree_fit; fold dub_neg_sub_ptree_fit;
unfold node_extract in NonTar;
fold node_extract in NonTar.

all : try apply PSV.

1 : destruct PSV as [ID PSV].
2 : destruct PSV as [[IO PSV] NO].
3-8 : destruct PSV as [[[PF PSV] PD] PO].
9 : destruct PSV as [[[[PF FC] PSV] PD] PO].
11-13 : destruct PSV as [[[PF PSV] PD] PO].
10,14-19: destruct PSV as [[[[[[[P1F P1SV] P2F] P2SV] P1D] P2D] P1O] P2O].

3-6,8-19 :  destruct S; inversion FS as [FS'];
            try destruct (and_bool_prop _ _ FS') as [FS1 FS2].

4-6,12,22 : destruct S1; inversion FS' as [FS''];
            try destruct (and_bool_prop _ _ FS1) as [FS1_1 FS1_2].

6 : destruct S1_1; inversion FS'' as [FS'''];
    destruct (and_bool_prop _ _ FS1_1) as [FS1_1_1 FS1_1_2].

10 :  assert (closed (neg (neg E)) = true -> closed E = true) as CIMP.
10 :  { unfold closed; fold closed;
        intros CE;
        apply CE. }

9,23 : case (form_eqb a E) eqn:EQ.

17 :  { repeat split;
        try rewrite dub_neg_ptree_formula_true;
        try rewrite P2F;
        try rewrite dub_neg_ptree_formula_struct;
        try rewrite P2F;
        unfold dub_neg_sub_formula, formula_sub_ind;
        unfold subst_ind_fit, formula_sub_ind_fit;
        fold subst_ind_fit formula_sub_ind_fit;
        try rewrite non_target_sub_fit;
        try rewrite non_target_sub_term';
        try rewrite FS2;
        unfold "&&";
        try rewrite dub_neg_ptree_deg_struct;
        try rewrite dub_neg_ptree_ord_struct;
        auto.

        2 : apply (IHP2 P2SV);
            rewrite P2F.

        2 : { unfold subst_ind_fit;
              fold subst_ind_fit.
              rewrite non_target_sub_fit.
              apply FS2. }

        1 : 
        
        admit. }
16 : { admit. }
7 : { admit. }

all : try apply form_eqb_eq in EQ;
      try destruct EQ;
      repeat rewrite dub_neg_ptree_formula_true;
      repeat split;
      try apply IHP;
      try apply IHP1;
      try apply IHP2;
      try rewrite dub_neg_ptree_deg_struct;
      try rewrite dub_neg_ptree_ord_struct;
      try rewrite dub_neg_ptree_formula_struct;
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
      try apply ID;
      try apply IO;
      try apply NO;
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
      try apply (formula_sub_ind_closed _ _ _ FC CIMP);
      try case (form_eqb f (neg E));
      try case (form_eqb f0 (neg E));
      try case (form_eqb (substitution f n (projT1 c)) (neg E));
      try reflexivity;
      try apply PSV;
      try apply NonTar.
  
1,3 : apply ord_succ_monot.

all : try apply nf_nf_succ;
      try apply ptree_ord_nf_struct;
      try apply PSV.

1 : { try rewrite <- (dub_neg_node_eq _ _ _ PSV).
      unfold formula_sub_ind.
      rewrite FS1.
      rewrite formula_sub_ind_free_list.
      apply FC.
      reflexivity. }

all : try case form_eqb eqn:EQ;
      try reflexivity;
      try rewrite <- (dub_neg_node_eq _ _ _ P1SV);
      try rewrite <- (dub_neg_node_eq _ _ _ P2SV);
      apply PAX.
Admitted.

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

1 : destruct PSV as [ID PSV].
2 : destruct PSV as [[IO PSV] NO].
3-8 : destruct PSV as [[[PF PSV] PD] PO].
9 : destruct PSV as [[[[PF FC] PSV] PD] PO].
11-13 : destruct PSV as [[[PF PSV] PD] PO].
10,14-19: destruct PSV as [[[[[[[P1F P1SV] P2F] P2SV] P1D] P2D] P1O] P2O].

3-6,8-19 :  destruct S; inversion FS as [FS'];
            try destruct (and_bool_prop _ _ FS') as [FS1 FS2].

4-6,12,22 : destruct S1; inversion FS' as [FS''];
            try destruct (and_bool_prop _ _ FS1) as [FS1_1 FS1_2].

6 : destruct S1_1; inversion FS'' as [FS'''];
    destruct (and_bool_prop _ _ FS1_1) as [FS1_1_1 FS1_1_2].

10 :  assert (closed (neg (neg E)) = true -> closed E = true) as CIMP.
10 :  { unfold closed; fold closed;
        intros CE;
        apply CE. }

9,23 : case (form_eqb a E) eqn:EQ.

17 :  { pose proof PAX as PAX2.
        unfold node_extract in PAX;
        fold node_extract in PAX.
        case (closed d) eqn:CD;
        case (free_list a) eqn:FREE;
        try destruct l;
        try case nat_eqb eqn:EQ;
        try pose proof (PAX _ (or_introl eq_refl)) as FAL;
        try inversion FAL.
        

        repeat split;
        try rewrite dub_neg_ptree_formula_true;
        try rewrite P2F;
        try rewrite dub_neg_ptree_formula;
        try rewrite P2F;
        unfold dub_neg_sub_formula, formula_sub_ind;
        unfold subst_ind_fit, formula_sub_ind_fit;
        fold subst_ind_fit formula_sub_ind_fit;
        try rewrite non_target_sub_fit;
        try rewrite non_target_sub_term';
        try rewrite FS2;
        unfold "&&";
        try rewrite dub_neg_ptree_deg_struct;
        try rewrite dub_neg_ptree_ord_struct;
        auto.

        3 : { assert ((loop_ad a (formula_sub_ind_fit d (neg (neg E)) E S2) n d1 d2 alpha1 alpha2 P1 (dub_neg_sub_ptree P2 E (lor_ind (non_target a) S2))) = (dub_neg_sub_ptree (loop_ad a d n d1 d2 alpha1 alpha2 P1 P2) E (lor_ind (0) S2))) as EQ.
              { unfold dub_neg_sub_ptree, ptree_formula, dub_neg_sub_ptree_fit;
                fold ptree_formula dub_neg_sub_ptree_fit.
                rewrite P2F.
                unfold dub_neg_sub_formula, formula_sub_ind.
                unfold subst_ind_fit;
                fold subst_ind_fit.
                rewrite non_target_sub_fit, FS2.
                reflexivity. }
              rewrite EQ, <- dub_neg_node_eq.
              apply PAX2.
              repeat split; auto. }

        2 : { admit. 


         }

         4 : admit.

        all : split; try apply P2SV.
            
            
              
              }
16 : { admit. }
7 : { admit. }

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
      try apply ID;
      try apply IO;
      try apply NO;
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
      try apply (formula_sub_ind_closed _ _ _ FC CIMP);
      try case (form_eqb f (neg E));
      try case (form_eqb f0 (neg E));
      try case (form_eqb (substitution f n (projT1 c)) (neg E));
      try reflexivity.

1,3 : apply ord_succ_monot.

all : try apply nf_nf_succ;
      try apply ptree_ord_nf_struct;
      try apply PSV.

1 : { try rewrite <- (dub_neg_node_eq _ _ _ PSV).
      unfold formula_sub_ind.
      rewrite FS1.
      rewrite formula_sub_ind_free_list.
      apply FC.
      reflexivity. }

all : try case form_eqb eqn:EQ;
      try reflexivity;
      try rewrite <- (dub_neg_node_eq _ _ _ P1SV);
      try rewrite <- (dub_neg_node_eq _ _ _ P2SV);
      apply PAX.
Admitted.

Lemma dub_neg_struct_valid :
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

1 : destruct PSV as [ID PSV].
2 : destruct PSV as [[IO PSV] NO].
3-8 : destruct PSV as [[[PF PSV] PD] PO].
9 : destruct PSV as [[[[PF FC] PSV] PD] PO].
11-13 : destruct PSV as [[[PF PSV] PD] PO].
10,14-19: destruct PSV as [[[[[[[P1F P1SV] P2F] P2SV] P1D] P2D] P1O] P2O].

3-6,8-19 :  destruct S; inversion FS as [FS'];
            try destruct (and_bool_prop _ _ FS') as [FS1 FS2].

4-6,12,22 : destruct S1; inversion FS' as [FS''];
            try destruct (and_bool_prop _ _ FS1) as [FS1_1 FS1_2].

6 : destruct S1_1; inversion FS'' as [FS'''];
    destruct (and_bool_prop _ _ FS1_1) as [FS1_1_1 FS1_1_2].

10 :  assert (closed (neg (neg E)) = true -> closed E = true) as CIMP.
10 :  { unfold closed; fold closed;
        intros CE;
        apply CE. }

9,23 : case (form_eqb a E) eqn:EQ.

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
      try apply ID;
      try apply IO;
      try apply NO;
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
      unfold "&&";
      unfold formula_sub_ind_fit; fold formula_sub_ind_fit;
      unfold form_eqb; fold form_eqb;
      try rewrite non_target_sub_term';
      try rewrite non_target_sub';
      try rewrite <- (sub_fit_true _ _ _ _ FS1);
      try apply (formula_sub_ind_closed _ _ _ FC CIMP);
      try case (form_eqb f (neg E));
      try case (form_eqb f0 (neg E));
      try case (form_eqb (substitution f n (projT1 c)) (neg E));
      try reflexivity.

1,3 : apply ord_succ_monot.

all : try apply nf_nf_succ;
      try apply ptree_ord_nf_struct;
      try apply PSV.

1 : { unfold formula_sub_ind.
      rewrite FS1.
      rewrite formula_sub_ind_free_list.
      + apply (incl_tran FC), dub_neg_ptree_node_free, PSV.
      + reflexivity. }

all : case form_eqb;
      try reflexivity.
Qed.

Lemma dub_neg_valid :
    forall (P : ptree) (E : formula),
        valid P ->
            forall (S : subst_ind),
                subst_ind_fit (ptree_formula P) S = true ->
                    valid (dub_neg_sub_ptree P E S).
Proof.
intros P E [PSV PAX] S FS.
split.
- apply (dub_neg_struct_valid _ _ PSV _ FS).
- intros A INA.
  apply PAX.
Admitted.