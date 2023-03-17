From Cyclic_PA.Maths Require Import naturals.
From Cyclic_PA.Maths Require Import lists.
From Cyclic_PA.Maths Require Import ordinals.

From Cyclic_PA.Logic Require Import definitions.
From Cyclic_PA.Logic Require Import fol.
From Cyclic_PA.Logic Require Import PA_cyclic.
From Cyclic_PA.Logic Require Import proof_trees.
From Cyclic_PA.Logic Require Import substitute.
From Cyclic_PA.Logic Require Import string_trees.

Require Import Lia.

Definition loop_sub_formula
  (A E : formula) (n m : nat) (S : subst_ind) : formula :=
  formula_sub_ind A (univ n E) (substitution E n (represent m)) S.

Lemma loop_sub_formula_closed :
    forall (A : formula),
        closed A = true ->
            forall (E : formula) (n m : nat) (S : subst_ind),
                closed (loop_sub_formula A E n m S) = true.
Proof.
intros A CA E n m S.
unfold loop_sub_formula.
apply (formula_sub_ind_closed _ _ _ CA).
intros CuE.
apply (closed_univ_sub E n CuE (represent m)).
apply represent_closed.
Qed.

Fixpoint unlooper 
(P1 P2 : ptree) (n m : nat) : ptree :=
match m with
| 0 => P1
| S m' => string_tree (substitute P2 (represent S m)) (unloop P1 P2 n m')
end.

Fixpoint loop_sub_ptree_fit
  (P : ptree) (E : formula) (n m : nat) (S : subst_ind) : ptree :=
match P, S with
| deg_up d P', _ => deg_up d (loop_sub_ptree_fit P' E n m S)

| ord_up alpha P', _ => ord_up alpha (loop_sub_ptree_fit P' E n m S)

| node A, _ => P

| exchange_ab A B d alpha P', lor_ind S_B S_A =>
    exchange_ab
      (loop_sub_formula A E n m S_A)
      (loop_sub_formula B E n m S_B)
      d alpha
      (loop_sub_ptree_fit P' E n m (lor_ind S_A S_B))

| exchange_cab C A B d alpha P', lor_ind (lor_ind S_C S_B) S_A =>
    exchange_cab
      (loop_sub_formula C E n m S_C)
      (loop_sub_formula A E n m S_A)
      (loop_sub_formula B E n m S_B)
      d alpha
      (loop_sub_ptree_fit P' E n m (lor_ind (lor_ind S_C S_A) S_B))

| exchange_abd A B D d alpha P', lor_ind (lor_ind S_B S_A) S_D =>
    exchange_abd
      (loop_sub_formula A E n m S_A)
      (loop_sub_formula B E n m S_B)
      (loop_sub_formula D E n m S_D)
      d alpha
      (loop_sub_ptree_fit P' E n m (lor_ind (lor_ind S_A S_B) S_D))

| exchange_cabd C A B D d alpha P', lor_ind (lor_ind (lor_ind S_C S_B) S_A) S_D =>
    exchange_cabd
      (loop_sub_formula C E n m S_C)
      (loop_sub_formula A E n m S_A)
      (loop_sub_formula B E n m S_B)
      (loop_sub_formula D E n m S_D)
      d alpha
      (loop_sub_ptree_fit
        P' E n m
        (lor_ind (lor_ind (lor_ind S_C S_A) S_B) S_D))

| contraction_a A d alpha P', _ =>
    contraction_a
      (loop_sub_formula A E n m S)
      d alpha
      (loop_sub_ptree_fit P' E n m (lor_ind S S))

| contraction_ad A D d alpha P', lor_ind S_A S_D =>
    contraction_ad
      (loop_sub_formula A E n m S_A)
      (loop_sub_formula D E n m S_D)
      d alpha
      (loop_sub_ptree_fit P' E n m (lor_ind (lor_ind S_A S_A) S_D))

| weakening_ad A D d alpha P', lor_ind S_A S_D =>
    weakening_ad
      (loop_sub_formula A E n m S_A)
      (loop_sub_formula D E n m S_D)
      d alpha
      (loop_sub_ptree_fit P' E n m S_D)

| demorgan_ab A B d1 d2 alpha1 alpha2 P1 P2, _ => P

| demorgan_abd A B D d1 d2 alpha1 alpha2 P1 P2, lor_ind S_AB S_D =>
    demorgan_abd
      A B
      (loop_sub_formula D E n m S_D)
      d1 d2 alpha1 alpha2
      (loop_sub_ptree_fit P1 E n m (lor_ind (0) S_D))
      (loop_sub_ptree_fit P2 E n m (lor_ind (0) S_D))

| negation_a A d alpha P', _ => P

| negation_ad A D d alpha P', lor_ind S_A S_D =>
    negation_ad
      A
      (loop_sub_formula D E n m S_D)
      d alpha
      (loop_sub_ptree_fit P' E n m (lor_ind (non_target A) S_D))

| quantification_a A k t d alpha P', _ => P

| quantification_ad A D k t d alpha P', lor_ind S_A S_D =>
    quantification_ad
      A
      (loop_sub_formula D E n m S_D)
      k t d alpha
      (loop_sub_ptree_fit P' E n m (lor_ind (0) S_D))

| loop_a A k d1 d2 alpha1 alpha2 P1 P2, _ =>
    match m with
    | 0 => P1
    | S m => unlooper
    end

| loop_ad A D k d alpha g, lor_ind S_A S_D =>
    (match form_eqb A E, nat_eqb d (ptree_deg (g c)), nat_eqb k n, S_A with
    | true, true, true, (1) =>
        ord_up (ord_succ alpha) (loop_sub_ptree_fit (g c) E n m (lor_ind (non_target A) S_D))
    | true, false, true, (1) =>
        deg_up d (ord_up (ord_succ alpha) (loop_sub_ptree_fit (g c) E n m (lor_ind (non_target A) S_D)))
    
    | _, _, _, _ => 
        loop_ad
          A
          (loop_sub_formula D E n m S_D)
          k d alpha
          (fun (t : c_term) =>
            loop_sub_ptree_fit (g t) E n m (lor_ind (non_target A) S_D))
    end)

| cut_ca C A d1 d2 alpha1 alpha2 P1 P2, _ =>
    cut_ca
      (loop_sub_formula C E n m S)
      A d1 d2 alpha1 alpha2
      (loop_sub_ptree_fit P1 E n m (lor_ind S (non_target A)))
      P2

| cut_ad A D d1 d2 alpha1 alpha2 P1 P2, _ =>
    cut_ad
      A
      (loop_sub_formula D E n m S)
      d1 d2 alpha1 alpha2
      P1
      (loop_sub_ptree_fit P2 E n m (lor_ind (0) S))

| cut_cad C A D d1 d2 alpha1 alpha2 P1 P2, lor_ind S_C S_D =>
    cut_cad
      (loop_sub_formula C E n m S_C)
      A
      (loop_sub_formula D E n m S_D)
      d1 d2 alpha1 alpha2
      (loop_sub_ptree_fit P1 E n m (lor_ind S_C (non_target A)))
      (loop_sub_ptree_fit P2 E n m (lor_ind (0) S_D))

| _, _ => P
end.

Definition loop_sub_ptree
  (P : ptree) (E : formula) (n : nat) (c : c_term) (S : subst_ind) : ptree :=
match subst_ind_fit (ptree_formula P) S with
| false => P
| true => loop_sub_ptree_fit P E n m S
end.

Lemma loop_ptree_formula_true :
    forall (P : ptree) (E : formula) (n : nat) (c : c_term) (S : subst_ind),
        subst_ind_fit (ptree_formula P) S = true ->
            loop_sub_ptree_fit P E n m S = loop_sub_ptree P E n m S.
Proof.
intros P E n m S FS.
unfold loop_sub_ptree.
rewrite FS.
reflexivity.
Qed.

Lemma loop_ptree_formula' :
    forall (P : ptree) (E : formula) (n : nat) (c : c_term),
        valid P ->
            forall (S : subst_ind),
                subst_ind_fit (ptree_formula P) S = true ->
                    ptree_formula (loop_sub_ptree P E n m S) =
                        loop_sub_formula (ptree_formula P) E n m S.
Proof.
intros P E n c.
induction P; try intros PV S FS;
unfold loop_sub_ptree;
rewrite FS;
unfold ptree_formula in *; fold ptree_formula in *;
unfold loop_sub_ptree_fit; fold loop_sub_ptree_fit.
  
1 : destruct PV as [ID PV].
2 : destruct PV as [[IO PV] NO].

1-2 : rewrite (loop_ptree_formula_true _ _ _ _ _ FS);
      unfold ptree_formula; fold ptree_formula;
      apply (IHP PV _ FS).

1 : { inversion PV as [PX].
      unfold loop_sub_ptree, loop_sub_formula, formula_sub_ind.
      rewrite FS.
      unfold ptree_formula; fold ptree_formula.
      destruct (axiom_atomic _ PX) as [[a fa] | [a fa]];
      rewrite fa;
      unfold formula_sub_ind_fit; fold formula_sub_ind_fit;
      unfold form_eqb;
      reflexivity. }

all : destruct S; inversion FS as [FS'];
      try reflexivity.

1,5,6,13 :  apply and_bool_prop in FS';
            destruct FS' as [FS1 FS2];
            unfold ptree_formula, loop_sub_formula, formula_sub_ind, formula_sub_ind_fit;
            fold formula_sub_ind_fit;
            rewrite FS,FS1,FS2;
            reflexivity.

9 : destruct (PV c) as [[[PF PCV ] PD] PO];
    assert (subst_ind_fit (ptree_formula (p c)) (lor_ind (non_target f) S2) = true) as FSP.
9 : { rewrite PF.
      unfold subst_ind_fit; fold subst_ind_fit.
      rewrite non_target_sub_fit.
      unfold "&&".
      destruct S1;
      try inversion FS' as [FS''];
      reflexivity. }


8 : { destruct (PV c) as [[[PF PCV ] PD] PO].
      case (form_eqb f E) eqn:EQ1;
      case (nat_eqb n0 n) eqn:EQ2;
      case (nat_eqb n1 (ptree_deg (p c))) eqn:E3;
      unfold ptree_formula, loop_sub_formula;
      fold ptree_formula;
      try rewrite PF;
      try apply form_eqb_eq in EQ1;
      try rewrite EQ1;
      try apply nat_eqb_eq in EQ2;
      try rewrite EQ2;
      try rewrite (formula_sub_ind_1 _ _ FS);
      unfold formula_sub_ind, subst_ind_fit, formula_sub_ind_fit, form_eqb;
      fold form_eqb;
      try rewrite nat_eqb_refl;
      try rewrite form_eqb_refl;
      try rewrite EQ1;
      try rewrite EQ2;
      unfold "&&";
      try reflexivity. }

7 : { case (form_eqb f E) eqn:EQ1;
      case (nat_eqb n0 n) eqn:EQ2;
      case (nat_eqb n1 (ptree_deg (p c))) eqn:E3;
      unfold ptree_formula, loop_sub_formula;
      fold ptree_formula;
      try rewrite formula_sub_ind_0;
      try reflexivity. }

all : destruct S1; inversion FS' as [FS''].

1-3 : apply and_bool_prop in FS';
      destruct FS' as [FS1 FS2];
      apply and_bool_prop in FS1;
      destruct FS1 as [FS1_1 FS1_2].

3 : destruct S1_1; inversion FS'' as [FS'''];
    apply and_bool_prop in FS1_1;
    destruct FS1_1 as [FS1_1_1 FS1_1_2].
  

10,11 : case (form_eqb f E) eqn:EQ1;
        case (nat_eqb n0 n) eqn:EQ2;
        case (nat_eqb n1 (ptree_deg (p c))) eqn:E3.

all : unfold ptree_formula, loop_sub_formula, formula_sub_ind, formula_sub_ind_fit, form_eqb;
      fold ptree_formula form_eqb formula_sub_ind_fit;
      try rewrite FS;
      try rewrite FS'';
      try rewrite EQ1;
      try rewrite EQ2;
      try rewrite FS1_1,FS1_2,FS2;
      try rewrite FS1_1_1,FS1_1_2,FS1_2,FS2;      
      unfold "&&";
      try reflexivity.

all : apply form_eqb_eq in EQ1;
      destruct EQ1;
      apply nat_eqb_eq in EQ2;
      destruct EQ2;
      rewrite (loop_ptree_formula_true _ _ _ _ _ FSP);
      rewrite (H _ PCV _ FSP);
      rewrite PF in *;
      unfold loop_sub_formula, formula_sub_ind, formula_sub_ind_fit;
      fold formula_sub_ind_fit;
      rewrite FSP;
      rewrite (non_target_term_sub _ n0 (projT1 c));
      rewrite non_target_sub';
      reflexivity.
Qed.

Lemma loop_ptree_formula :
    forall (P : ptree) (E : formula) (n : nat) (c : c_term),
        valid P ->
            forall (S : subst_ind),
                ptree_formula (loop_sub_ptree P E n m S) =
                    loop_sub_formula (ptree_formula P) E n m S.
Proof.
intros P E n m VP S.
destruct (subst_ind_fit (ptree_formula P) S) eqn:FS.
- apply (loop_ptree_formula' _ _ _ _ VP _ FS).
- unfold loop_sub_ptree, loop_sub_formula, formula_sub_ind.
  rewrite FS.
  reflexivity.
Qed.

Lemma loop_ptree_deg :
    forall (P : ptree) (E : formula) (n : nat) (c : c_term),
        valid P ->
            forall (S : subst_ind),
                ptree_deg (loop_sub_ptree P E n m S) = ptree_deg P.
Proof.
intros P E n m PV.
unfold loop_sub_ptree.
pose (ptree_formula P) as A.
induction P; intros S;
case (subst_ind_fit A S) eqn:FS;
unfold A in FS;
try rewrite FS;
unfold loop_sub_ptree_fit; fold loop_sub_ptree_fit;
unfold ptree_deg in *; fold ptree_deg in *;
try reflexivity.

1 : destruct PV as [[IO PV] NO].

11,12 : destruct (PV c) as [[[PF PCV] PD] PO].

1 : unfold ptree_formula in FS; fold ptree_formula in FS.
    pose proof (IHP PV S) as IHPS.
    rewrite FS in IHPS.
    apply IHPS.

all : destruct S; inversion FS as [FS'];
      try reflexivity.

4-6 : case (form_eqb f E) eqn:EQ1;
      case (nat_eqb n0 n) eqn:EQ2;
      case (nat_eqb n1 (ptree_deg (p c))) eqn:EQ3;
      unfold ptree_deg; fold ptree_deg;
      try apply form_eqb_eq in EQ1;
      try destruct EQ1;
      try apply nat_eqb_eq in EQ2,EQ3;
      try rewrite EQ3;
      try reflexivity.

all : destruct S1; inversion FS' as [FS''].

3 : destruct S1_1; inversion FS'' as [FS'''].

all : unfold ptree_deg; fold ptree_deg;
      try reflexivity.

- assert (subst_ind_fit (ptree_formula (p c)) (lor_ind (non_target f) S2) = true) as FSP.
  { rewrite PF.
    unfold subst_ind_fit; fold subst_ind_fit.
    rewrite non_target_sub_fit.
    unfold "&&".
    apply FS''. }
  pose proof (H _ PCV (lor_ind (non_target f) S2)) as IHPS.
  rewrite FSP in IHPS.
  apply IHPS.
Qed.

Lemma loop_ptree_ord :
    forall (P : ptree) (E : formula) (n : nat) (c : c_term),
        valid P ->
            forall (S : subst_ind),
                ptree_ord (loop_sub_ptree P E n m S) = ptree_ord P.
Proof.
intros P E n m PV.
unfold loop_sub_ptree.
pose (ptree_formula P) as A.
induction P; intros S;
case (subst_ind_fit A S) eqn:FS;
unfold A in FS;
try rewrite FS;
unfold loop_sub_ptree_fit; fold loop_sub_ptree_fit;
unfold ptree_ord in *; fold ptree_ord in *;
try reflexivity.

1 : destruct PV as [ID PV].

11,12 : destruct (PV c) as [[[PF PCV] PD] PO].

1 : unfold ptree_formula in FS; fold ptree_formula in FS.
    pose proof (IHP PV S) as IHPS.
    rewrite FS in IHPS.
    apply IHPS.

all : destruct S; inversion FS as [FS'];
      try reflexivity.

4-6 : case (form_eqb f E) eqn:EQ1;
      case (nat_eqb n0 n) eqn:EQ2;
      case (nat_eqb n1 (ptree_deg (p c))) eqn:EQ3;
      unfold ptree_deg; fold ptree_deg;
      try apply form_eqb_eq in EQ1;
      try destruct EQ1;
      try apply nat_eqb_eq in EQ2,EQ3;
      try apply EQ3;
      try reflexivity.

all : destruct S1; inversion FS' as [FS''].

3 : destruct S1_1; inversion FS'' as [FS'''].

all : unfold ptree_deg; fold ptree_deg;
      try reflexivity.
Qed.

Lemma loop_valid :
    forall (P : ptree) (E : formula) (n : nat) (c : c_term),
        valid P ->
            forall (S : subst_ind),
                subst_ind_fit (ptree_formula P) S = true ->
                    valid (loop_sub_ptree P E n m S).
Proof.
intros P E n m PV.
induction P; try intros S FS;
unfold loop_sub_ptree;
rewrite FS;
unfold ptree_formula in *; fold ptree_formula in *;
unfold loop_sub_ptree_fit; fold loop_sub_ptree_fit.

all : try apply PV.

1 : destruct PV as [ID PV].
2 : destruct PV as [[IO PV] NO].
3-8 : destruct PV as [[[PF PV] PD] PO].
9 : destruct PV as [[[[PF FC] PV] PD] PO].
11-12 : destruct PV as [[[PF PV] PD] PO].
10,15,16,17: destruct PV as [[[[[[[P1F P1V] P2F] P2V] P1D] P2D] P1O] P2O].

3,4,5,6,8,9,10,13,14,15,16,17 : destruct S; inversion FS as [FS'];
                                try destruct (and_bool_prop _ _ FS') as [FS1 FS2].

15 :  assert (valid (loop_ad f (loop_sub_formula f0 E n m S2) n0 n1 o (fun t : c_term => loop_sub_ptree_fit (p t) E n m (lor_ind (non_target f) S2)))) as VSC.
15 :  { assert (forall t, subst_ind_fit (ptree_formula (p t)) (lor_ind (non_target f) S2) = true) as FSt.
        { intros t.
          destruct (PV t) as [[[PF PTV] PD] PO].
          rewrite PF.
          unfold subst_ind_fit; fold subst_ind_fit.
          rewrite non_target_sub_fit.
          unfold "&&".
          apply FS2. }
        repeat split;
        destruct (PV t) as [[[PF PTV] PD] PO];
        rewrite (loop_ptree_formula_true _ _ _ _ _ (FSt t)).
        - rewrite (loop_ptree_formula _ _ _ _ PTV).
          rewrite PF.
          unfold loop_sub_formula.
          rewrite (non_target_term_sub _ n0 (projT1 t)).
          rewrite non_target_sub_lor.
          reflexivity.
        - apply (X _ PTV _ (FSt t)).
        - rewrite (loop_ptree_deg _ _ _ _ PTV).
          apply PD.
        - rewrite (loop_ptree_ord _ _ _ _ PTV).
          apply PO. }

4,5,6,15 :  destruct S1; inversion FS' as [FS''];
            try destruct (and_bool_prop _ _ FS1) as [FS1_1 FS1_2].

6 : destruct S1_1; inversion FS'' as [FS'''];
    destruct (and_bool_prop _ _ FS1_1) as [FS1_1_1 FS1_1_2].

10 :  assert (closed (univ n E) = true -> closed (substitution E n (projT1 c)) = true) as CIMP.
10 :  { intros CE.
        apply (closed_univ_sub _ _ CE).
        destruct m as [t Ct].
        apply Ct. }

7,8,15,16 : destruct (PV c) as [[[PF PCV] PD] PO].

9,10 :  case (form_eqb f E) eqn:EQ1;
        case (nat_eqb n0 n) eqn:EQ2;
        case (nat_eqb n1 (ptree_deg (p c))) eqn:EQ3;
        try apply PV;
        repeat split;
        try rewrite PO;
        unfold ptree_deg;fold ptree_deg;
        try apply ord_succ_monot;
        try apply ord_succ_nf;
        try apply ptree_ord_nf;
        try apply PCV;
        inversion PD as [EQ4 | ];
        try destruct EQ4;
        try rewrite nat_eqb_refl in EQ3;
        inversion EQ3;
        try lia.

7,8 : case (form_eqb f E) eqn:EQ1;
      case (nat_eqb n0 n) eqn:EQ2;
      case (nat_eqb n1 (ptree_deg (p c))) eqn:EQ3;
      try apply VSC.

all : try apply form_eqb_eq in EQ1;
      try destruct EQ1;
      repeat rewrite loop_ptree_formula_true;
      repeat split;
      try apply IHP;
      try apply IHP1;
      try apply IHP2;
      unfold ptree_deg; fold ptree_deg;
      try rewrite loop_ptree_deg;
      try rewrite loop_ptree_ord;
      try rewrite loop_ptree_formula;
      try rewrite PF;
      try rewrite P1F;
      try rewrite P2F;
      unfold loop_sub_formula, formula_sub_ind;
      try apply PV;
      try rewrite PD;
      try rewrite PO;
      try apply P1V;
      try rewrite P1D;
      try rewrite P1O;
      try apply P2V;
      try rewrite P2D;
      try rewrite P2O;
      try apply ID;
      try apply IO;
      try apply NO;
      try apply (X _ PCV);
      try rewrite PF;
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
      try rewrite non_target_sub';
      try rewrite <- (sub_fit_true _ _ _ _ FS1);
      try apply (formula_sub_ind_closed _ _ _ FC CIMP);
      try apply ord_succ_monot;
      try apply nf_nf_succ;
      try apply ptree_ord_nf;
      try apply PCV;
      unfold subst_ind_fit; fold subst_ind_fit;
      try reflexivity.
      inversion PD as [EQ4 | ];
      try destruct EQ4;
      try rewrite nat_eqb_refl in EQ3;
      try lia.
Qed.