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
      P2

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

Lemma dub_neg_ptree_formula_struct' : forall (P : ptree) (E : formula),
  struct_valid P ->
      forall (S : subst_ind),
          subst_ind_fit (ptree_formula P) S = true ->
              ptree_formula (dub_neg_sub_ptree P E S) =
                  dub_neg_sub_formula (ptree_formula P) E S.
Proof.
intros P E PSV.
induction P.

3 : { try intros S FS;
      unfold dub_neg_sub_ptree;
      rewrite FS;
      reflexivity. }

all : try intros S FS;
      unfold dub_neg_sub_ptree;
      rewrite FS;
      unfold ptree_formula, node_extract in *; fold ptree_formula node_extract in *;
      unfold dub_neg_sub_ptree_fit; fold dub_neg_sub_ptree_fit.
  
1 : destruct PSV as [ID PSV].
2 : destruct PSV as [[IO PSV] NO].
12-13 : destruct PSV as [[[PF PSV] PD] PO].

1-2 : rewrite (dub_neg_ptree_formula_true _ _ _ FS);
      unfold ptree_formula; fold ptree_formula;
      apply (IHP PSV _ FS).

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

2-4,7-10 :  destruct S1;
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

Lemma dub_neg_ptree_formula_struct : forall (P : ptree) (E : formula),
  struct_valid P ->
      forall (S : subst_ind),
          ptree_formula (dub_neg_sub_ptree P E S) =
              dub_neg_sub_formula (ptree_formula P) E S.
Proof.
intros P E PSV S.
case (subst_ind_fit (ptree_formula P) S) eqn:FS.
- apply (dub_neg_ptree_formula_struct' _ _ PSV), FS.
- unfold dub_neg_sub_formula, formula_sub_ind, dub_neg_sub_ptree.
  rewrite FS.
  reflexivity.
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

2-4,7-10 :  destruct S1;
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

(*
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
*)

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

4,5 : case (form_eqb a E) eqn:EQ;
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

4,5 : case (form_eqb a E) eqn:EQ;
      unfold ptree_deg; fold ptree_deg;
      try rewrite PD;
      try reflexivity.

all : destruct S1; inversion FS' as [FS''].

3 : destruct S1_1; inversion FS'' as [FS'''].

all : unfold ptree_deg; fold ptree_deg;
      try reflexivity.
Qed.

Lemma dub_neg_free_sub :
    forall (P : ptree) (E : formula) (S : subst_ind),
        struct_valid P ->
            subst_ind_fit (ptree_formula P) S = true ->
                incl (flat_map free_list (node_extract P)) (flat_map free_list (node_extract (dub_neg_sub_ptree P E S))).
Proof.
  intros P E.
  induction P;
  intros S PSV FS.
  
  1 : destruct PSV as [ID PSV].
  2 : destruct PSV as [[IO PSV] NO].
  3 : destruct PSV.
  4-9 : destruct PSV as [[[PF PSV] PD] PO].
  10 : destruct PSV as [[[[PF FC] PSV] PD] PO].
  13-16 : destruct PSV as [[[PF PSV] PD] PO].
  11,12,17-21: destruct PSV as [[[[[[[P1F P1SV] P2F] P2SV] P1D] P2D] P1O] P2O].
  
  3 : { intros A INA.
        unfold dub_neg_sub_ptree.
        rewrite FS.
        unfold dub_neg_sub_ptree_fit.
        unfold node_extract, flat_map in *.
        rewrite app_nil_r in *.
        rewrite dub_neg_formula_free.
        apply INA. }
  
  3-6,8-13,16-20 : 
      destruct S;
      inversion FS as [FS'];
      try rewrite FS';
      try destruct (and_bool_prop _ _ FS') as [FS1 FS2].
  
  4-6,11,18,21 :
      destruct S1;
      inversion FS' as [FS''];
      try rewrite FS'';
      try destruct (and_bool_prop _ _ FS1) as [FS1_1 FS1_2].
  
  6 : destruct S1_1;
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
        repeat rewrite flat_map_app;
        try apply incl_app_app;
        try apply incl_refl;
        try apply (fun FSUB => IHP _ PSV FSUB);
        try apply (fun FSUB => IHP1 _ P1SV FSUB);
        try apply (fun FSUB => IHP2 _ P2SV FSUB);
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

  1 : repeat rewrite <- dub_neg_sub_formula_closed.
      case (closed c) eqn:CC.
      destruct (free_list a);
      try destruct l;
      try case nat_eqb eqn:EQ.


  all : unfold flat_map;
        fold (flat_map free_list);
        repeat rewrite flat_map_app;
        repeat apply incl_app_app;
        try apply incl_refl;
        try apply (fun FSUB => IHP1 _ P1SV FSUB);
        try rewrite P1F;
        unfold ptree_formula in FS;
        fold ptree_formula in FS;
        unfold subst_ind_fit;
        fold subst_ind_fit;
        try rewrite FS;
        try rewrite FS';
        try rewrite FS1;
        try rewrite FS2;
        try rewrite non_target_sub_fit;
        try reflexivity.
Qed.

Lemma dub_neg_not_ax_not_ax :
    forall (P : ptree) (E : formula) (S : subst_ind),
        struct_valid P ->
            subst_ind_fit (ptree_formula P) S = true ->
                (forall (A : formula), In A (node_extract (dub_neg_sub_ptree P E S)) -> PA_cyclic_axiom A = false -> (exists (B : formula), In B (node_extract P) /\ PA_cyclic_axiom B = false)).
Proof.
  intros P E.
  induction P;
  intros S PSV FS A IN NAX.
  
  1 : destruct PSV as [ID PSV].
  2 : destruct PSV as [[IO PSV] NO].
  3 : destruct PSV.
  4-9 : destruct PSV as [[[PF PSV] PD] PO].
  10 : destruct PSV as [[[[PF FC] PSV] PD] PO].
  13-16 : destruct PSV as [[[PF PSV] PD] PO].
  11,12,17-21: destruct PSV as [[[[[[[P1F P1SV] P2F] P2SV] P1D] P2D] P1O] P2O].
  
  3 : { unfold dub_neg_sub_ptree in IN.
        rewrite FS in IN.
        unfold dub_neg_sub_ptree_fit in IN.
        destruct IN as [EQ | FAL];
        try inversion FAL.
        destruct EQ.
        exists a.
        unfold node_extract.
        split.
        - left.
          reflexivity.
        - unfold dub_neg_sub_formula, formula_sub_ind in NAX.
          unfold ptree_formula in FS.
          rewrite FS in NAX.
          destruct a;
          unfold formula_sub_ind_fit, form_eqb in NAX;
          fold formula_sub_ind_fit form_eqb in NAX;
          try apply NAX;
          try reflexivity.
          case form_eqb eqn:EQ.
          + apply form_eqb_eq in EQ.
            rewrite EQ.
            reflexivity.
          + apply NAX. }
  
  3-6,8-13,16-20 : 
      destruct S;
      inversion FS as [FS'];
      try rewrite FS';
      try destruct (and_bool_prop _ _ FS') as [FS1 FS2].
  
  4-6,11,18,21 :
      destruct S1;
      inversion FS' as [FS''];
      try rewrite FS'';
      try destruct (and_bool_prop _ _ FS1) as [FS1_1 FS1_2].
  
  6 : destruct S1_1;
      inversion FS'' as [FS'''];
      try rewrite FS''';
      destruct (and_bool_prop _ _ FS1_1) as [FS1_1_1 FS1_1_2].
  
  all : unfold dub_neg_sub_ptree in IN;
        rewrite FS in IN;
        unfold dub_neg_sub_ptree_fit in IN;
        fold dub_neg_sub_ptree_fit in IN;
        unfold node_extract in *;
        fold node_extract in *;
        try rewrite dub_neg_ptree_formula_true in IN;
        try rewrite dub_neg_ptree_formula_true in IN;
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
        try apply (fun FSUB => IHP _ PSV FSUB _ IN NAX);
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

  3-4,9-13 :
      exists A;
      split;
      auto.

  1,2,6-8 :
      try apply in_app_or in IN as [IN1 | IN2];
      try destruct (fun FSUB => IHP1 _ P1SV FSUB A IN1 NAX) as [B1 [INB1 BAX1]];
      try destruct (fun FSUB => IHP2 _ P2SV FSUB A IN2 NAX) as [B2 [INB2 BAX2]];
      try exists B1;
      try exists B2;
      try exists A;
      try split;
      try apply NAX;
      try apply BAX1;
      try apply BAX2;
      try apply (in_or_app _ _ _ (or_introl IN1));
      try apply (in_or_app _ _ _ (or_intror IN2));
      try apply (in_or_app _ _ _ (or_introl INB1));
      try apply (in_or_app _ _ _ (or_intror INB2));
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

  3 : rewrite <- dub_neg_sub_formula_closed in *;
      case (closed c) eqn:CC.

  1-3 : destruct (free_list a) eqn:FREE;
        try destruct l;
        try case nat_eqb eqn:EQ'.

  3,4,7,8,11-13 : 
      exists (univ n a);
      exact (conj (or_introl eq_refl) eq_refl).

  1-4 : exists A;
        exact (conj IN NAX).

  all : apply in_app_or in IN as [IN1 | IN2].

  1,3 : exists A;
        exact (conj (in_or_app _ _ _ (or_introl IN1)) NAX).

  all : destruct (fun FSUB => IHP1 _ P1SV FSUB A IN2 NAX) as [B1 [INB1 BAX1]];
        try exists B1;
        try split;
        try apply (in_or_app _ _ _ (or_intror INB1));
        try apply BAX1;
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
        try rewrite non_target_fit;
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
intros P E S PSV FS PAX A INA.
case (PA_cyclic_axiom A) eqn:AX.
- reflexivity.
- destruct (dub_neg_not_ax_not_ax _ _ _ PSV FS _ INA AX) as [B [INB NAX]].
  rewrite (PAX _ INB) in NAX.
  inversion NAX.
Qed.

Lemma dub_neg_struct_valid :
    forall (P : ptree) (E : formula),
        struct_valid P ->
            forall (S : subst_ind),
                subst_ind_fit (ptree_formula P) S = true ->
                    struct_valid (dub_neg_sub_ptree P E S).
Proof.
induction P;
intros E PSV S FS;
unfold dub_neg_sub_ptree;
rewrite FS;
unfold ptree_ord, ptree_formula in *;
fold ptree_ord ptree_formula in *;
unfold dub_neg_sub_ptree_fit;
fold dub_neg_sub_ptree_fit.

1 : destruct PSV as [ID PSV].
2 : destruct PSV as [[IO PSV] NO].
3 : destruct PSV.
4-9 : destruct PSV as [[[PF PSV] PD] PO].
10 : destruct PSV as [[[[PF FC] PSV] PD] PO].
13-16 : destruct PSV as [[[PF PSV] PD] PO].
11,12,17-21: destruct PSV as [[[[[[[P1F P1SV] P2F] P2SV] P1D] P2D] P1O] P2O].

4-7,9-14,17-21 : 
      destruct S;
      inversion FS as [FS'];
      try rewrite FS';
      try destruct (and_bool_prop _ _ FS') as [FS1 FS2].
  
5-7,12,19,22 :
      destruct S1;
      inversion FS' as [FS''];
      try rewrite FS'';
      try destruct (and_bool_prop _ _ FS1) as [FS1_1 FS1_2].
  
7 : destruct S1_1;
    inversion FS'' as [FS'''];
    try rewrite FS''';
    destruct (and_bool_prop _ _ FS1_1) as [FS1_1_1 FS1_1_2].

11,23 : case (form_eqb a E) eqn:FEQ.

all : repeat rewrite dub_neg_ptree_formula_true;
      repeat split;
      repeat rewrite dub_neg_ptree_formula_struct;
      try rewrite PF;
      try rewrite P1F;
      try rewrite P2F;
      try rewrite FEQ;
      unfold dub_neg_sub_formula;
      repeat rewrite formula_sub_ind_lor;
      try rewrite formula_sub_ind_0;
      try rewrite non_target_sub;
      try rewrite non_target_sub_term;
      unfold subst_ind_fit;
      fold subst_ind_fit;
      repeat rewrite non_target_fit;
      repeat rewrite non_target_sub_fit;
      repeat rewrite FS;
      try rewrite FS1;
      try rewrite FS2;
      try rewrite FS1_1;
      try rewrite FS1_2;
      try rewrite FS1_1_1;
      try rewrite FS1_1_2;
      try reflexivity;
      repeat rewrite dub_neg_ptree_deg_struct;
      repeat rewrite dub_neg_ptree_ord_struct;
      try apply ID;
      try apply IO;
      try apply NO;
      try apply PSV;
      try apply P1SV;
      try apply P2SV;
      try apply PD;
      try apply P1D;
      try apply P2D;
      try apply PO;
      try apply P1O;
      try apply P2O;
      try apply PF;
      try apply P1F;
      try apply P2F;
      try rewrite PO in *;
      try apply ord_succ_monot;
      try apply nf_nf_succ;
      try apply ptree_ord_nf_struct;
      try apply PSV;
      try reflexivity.

17 :  { unfold formula_sub_ind.
        rewrite FS1.
        rewrite formula_sub_ind_free_list.
        apply (incl_tran FC), dub_neg_free_sub.
        apply PSV.
        rewrite PF.
        apply FS2.
        reflexivity. }

all : try apply (IHP _ PSV);
      try apply (IHP1 _ P1SV);
      try apply (IHP2 _ P2SV);
      try rewrite PF;
      try rewrite P1F;
      try rewrite P2F;
      try rewrite FEQ;
      unfold subst_ind_fit;
      fold subst_ind_fit;
      repeat rewrite non_target_fit;
      repeat rewrite non_target_sub_fit;
      repeat rewrite FS;
      try rewrite FS1;
      try rewrite FS2;
      try rewrite FS1_1;
      try rewrite FS1_2;
      try rewrite FS1_1_1;
      try rewrite FS1_1_2;
      try reflexivity.
Qed.

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

3 : { repeat split.
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

1 : destruct PSV as [ID PSV].
2 : destruct PSV as [[IO PSV] NO].
3-8 : destruct PSV as [[[PF PSV] PD] PO].
9 : destruct PSV as [[[[PF FC] PSV] PD] PO].
11-13 : destruct PSV as [[[PF PSV] PD] PO].
10,14-17: destruct PSV as [[[[[[[P1F P1SV] P2F] P2SV] P1D] P2D] P1O] P2O].

3-6,8-11,14-17 : 
    destruct S; inversion FS as [FS'];
    try destruct (and_bool_prop _ _ FS') as [FS1 FS2].

4-6,14 :  destruct S1; inversion FS' as [FS''];
          try destruct (and_bool_prop _ _ FS1) as [FS1_1 FS1_2].

6 : destruct S1_1; inversion FS'' as [FS'''];
    destruct (and_bool_prop _ _ FS1_1) as [FS1_1_1 FS1_1_2].

10 :  assert (closed (neg (neg E)) = true -> closed E = true) as CIMP.
10 :  { unfold closed; fold closed;
        intros CE;
        apply CE. }

8,15 : case (form_eqb a E) eqn:EQ.

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
      try reflexivity.

1,3 : apply ord_succ_monot.

all : try apply nf_nf_succ;
      try apply ptree_ord_nf_struct;
      try apply PSV.

1 : { try rewrite <- (dub_neg_node_eq _ _ _ PSV).
      unfold formula_sub_ind.
      rewrite FS1.
      rewrite formula_sub_ind_free_list.
      apply (incl_tran FC), dub_neg_free_sub.
      apply PSV.
      rewrite PF.
      apply FS2.
      reflexivity. }

all : try case form_eqb eqn:EQ;
      try reflexivity;
      intros A IN;
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
      try reflexivity.

3,4 : try apply PAX;
      try apply in_or_app;
      try apply (or_introl IN1);
      try apply (or_intror IN2).

all : unfold node_extract in *; fold node_extract in *;
      fold (dub_neg_sub_formula c E S1) in IN;
      try rewrite <- dub_neg_sub_formula_closed in IN;
      case (closed c) eqn:CC;
      destruct (free_list a);
      try destruct l;
      try case nat_eqb eqn:EQ;
      try pose proof (PAX _ (or_introl eq_refl)) as FAL;
      try inversion FAL;
      try apply (PAX _ (in_or_app _ _ _ (or_intror IN)));
      try apply in_app_or in IN as [IN1 | IN2];
      try apply (PAX _ (in_or_app _ _ _ (or_introl IN1)));
      apply (fun FSUB => dub_neg_all_ax_trans _ _ _ P1SV FSUB (fun B INB => PAX B (in_or_app _ _ _ (or_intror INB))) _ IN2);
      rewrite P1F;
      unfold subst_ind_fit;
      fold subst_ind_fit;
      rewrite FS1, non_target_sub_fit;
      reflexivity.
Qed.