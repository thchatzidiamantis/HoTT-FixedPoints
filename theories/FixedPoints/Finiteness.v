(** * Strictly finite groups *)

From HoTT Require Import Basics Types.
Require Import Truncations.Core Truncations.Connectedness Truncations.SeparatedTrunc.
Require Import Spaces.Finite.
Require Import Universes.HProp HSet.
Require Import Homotopy.ClassifyingSpace HomotopyGroup WhiteheadsPrinciple.
Require Import Misc.BoundedSearch CompactTypes.
Require Import Algebra.Groups.Group Subgroup Algebra.AbGroups.Centralizer.
Require Import Colimits.Quotient.
Require Import Pointed WildCat.Core.
Require Export Classes.interfaces.canonical_names (SgOp, sg_op,
    MonUnit, mon_unit, LeftIdentity, left_identity, RightIdentity, right_identity,
    Negate, negate, Associative, simple_associativity, associativity,
    LeftInverse, left_inverse, RightInverse, right_inverse, Commutative, commutativity).
Export canonical_names.BinOpNotations.
Export Homotopy.ClassifyingSpace.Core.ClassifyingSpaceNotation.

Local Open Scope pointed_scope.
Local Open Scope trunc_scope.
Local Open Scope mc_mult_scope.
Local Open Scope path_scope.

(** ** Strictly finite types *)

Class StrictlyFinite (X : Type) :=
  { fcard : nat ;
    equiv_fin : X <~> Fin fcard }.

Definition issig_strictlyfinite X
  : { n : nat & (X <~> Fin n) } <~> StrictlyFinite X.
Proof.
  issig.
Defined.

Instance decidablepaths_strictlyfinite X `{StrictlyFinite X}
  : DecidablePaths X
  := decidablepaths_equiv _ equiv_fin^-1 _.

(* jdc: if the implication was reversed, then you wouldn't need to invert e.  And it looks like most users of this lemma apply it to an inverted function. *)
Definition strictlyfinite_equiv X {Y} (e : X -> Y) `{IsEquiv X Y e}
  : StrictlyFinite X -> StrictlyFinite Y
  := fun _ => Build_StrictlyFinite Y fcard
              (equiv_fin oE (Build_Equiv _ _ e _)^-1%equiv).

Definition strictlyfinite_equiv' X {Y} (e : X <~> Y)
  : StrictlyFinite X -> StrictlyFinite Y
  := fun _ => strictlyfinite_equiv X e _.

(** Canonical finite sets are strictly finite *)
Instance strictlyfinite_fin n : StrictlyFinite (Fin n)
  := Build_StrictlyFinite _ n (equiv_idmap _).

(** This includes the empty set. *)
Instance strictlyfinite_empty : StrictlyFinite Empty
  := strictlyfinite_fin 0.

(** The unit type is strictly finite, since it's equivalent to [Fin 1]. *)
Instance strictlyfinite_unit : StrictlyFinite Unit.
Proof.
  srapply (Build_StrictlyFinite _ (1 : nat)).
  symmetry; apply sum_empty_l.
Defined.

(** Thus, any contractible type is strictly finite. *)
Instance strictlyfinite_contr X `{Contr X} : StrictlyFinite X
  := strictlyfinite_equiv' Unit equiv_contr_unit^-1 _.

Local Instance finite_strictlyfinite {X} `{StrictlyFinite X} : Finite X
  := Build_Finite _ fcard (tr equiv_fin).

Definition issigmacompact_strictlyfinite {A : Type} `{StrictlyFinite A}
  : IsSigmaCompact A
  := issigmacompact_equiv equiv_fin (issigmacompact_fin _).

(* Why do we not have this in Quotient.v? Is it obvious? *)
Lemma in_class_of_path `{Univalence}
      {A : Type} (R : Relation A) `{is_mere_relation _ R}
      `{Transitive _ R} `{Symmetric _ R} `{Reflexive _ R}
  : forall x a, x = class_of R a -> in_class _ x a.
Proof.
  intros x a p.
  destruct p^.
  cbv; reflexivity.
Defined.

Definition strictlyfinite_decidable_hprop X `{IsHProp X} `{Decidable X}
  : StrictlyFinite X.
Proof.
  destruct (dec X) as [x|nx].
  - apply strictlyfinite_contr.
    by apply contr_inhabited_hprop.
  - refine (strictlyfinite_equiv Empty nx^-1 _).
Defined.

Instance strictlyfinite_succ X `{StrictlyFinite X} : StrictlyFinite (X + Unit).
Proof.
  refine (Build_StrictlyFinite _ (@fcard X _).+1 _).
  pose proof (@equiv_fin X _).
  refine (_ +E 1); assumption.
Defined.

Instance strictlyfinite_sum X Y `{StrictlyFinite X} {sfY : StrictlyFinite Y}
  : StrictlyFinite (X + Y).
Proof.
  assert (e := @equiv_fin Y sfY).
  refine (strictlyfinite_equiv _ (functor_sum idmap e^-1) _).
  generalize (@fcard Y sfY); intros n; clear Y sfY e.
  induction n as [|n IH].
  - exact (strictlyfinite_equiv _ (sum_empty_r X)^-1 _).
  - exact (strictlyfinite_equiv _ (equiv_sum_assoc X _ Unit) _).
Defined.

Instance strictlyfinite_sigma {X} (Y : X -> Type)
       {sfX : StrictlyFinite X} `{forall x, StrictlyFinite (Y x)}
  : StrictlyFinite { x:X & Y x }.
Proof.
  assert (e := @equiv_fin X sfX).
  rapply (strictlyfinite_equiv' _
            (equiv_functor_sigma (equiv_inverse e)
                                 (fun x (y:Y (e^-1 x)) => y))).
  set (Y' := fun x => Y (e^-1 x)).
  assert (forall x, StrictlyFinite (Y' x)) by exact _; clearbody Y'; clear e Y H.
  generalize dependent (@fcard X sfX); intros n Y' H; clear X sfX.
  induction n as [|n IH].
  - exact (strictlyfinite_equiv Empty pr1^-1 _).
  - refine (strictlyfinite_equiv _ (equiv_sigma_sum (Fin n) Unit Y')^-1 _).
    apply strictlyfinite_sum.
    + apply IH; exact _.
    + refine (strictlyfinite_equiv' _ (equiv_contr_sigma _)^-1 _).
Defined.

(* jdc: Since this is found by typeclass search, it might not be needed to make it an instance. *)
Instance strictlyfinite_detachable_subset {X} `{StrictlyFinite X} (P : X -> Type)
       `{forall x, IsHProp (P x)} `{forall x, Decidable (P x)}
  : StrictlyFinite { x:X & P x }.
Proof.
  srapply strictlyfinite_sigma.
  intro x; rapply strictlyfinite_decidable_hprop.
Defined.

Instance strictlyfinite_prod X Y `{StrictlyFinite X} `{StrictlyFinite Y}
  : StrictlyFinite (X * Y).
Proof.
  assert (e := @equiv_fin Y _).
  refine (strictlyfinite_equiv _ (functor_prod idmap e^-1) _).
  generalize (@fcard Y _); intros n.
  induction n as [|n IH].
  - refine (strictlyfinite_equiv _ (prod_empty_r X)^-1 _).
  - refine (strictlyfinite_equiv _ (sum_distrib_l X _ Unit)^-1
             (strictlyfinite_sum _ _)).
    refine (strictlyfinite_equiv _ (prod_unit_r X)^-1 _).
Defined.

Instance strictlyfinite_forall `{Funext} {X} (Y : X -> Type)
       `{StrictlyFinite X} `{forall x, StrictlyFinite (Y x)}
: StrictlyFinite (forall x:X, Y x).
Proof.
  assert (e := @equiv_fin X _).
  simple refine (strictlyfinite_equiv' _
            (equiv_functor_forall' (P := fun x => Y (e^-1 x)) e _) _); try exact _.
  { intros x; refine (equiv_transport _ (eissect e x)). }
  set (Y' := Y o e^-1); change (StrictlyFinite (forall x, Y' x)).
  assert (forall x, StrictlyFinite (Y' x)) by exact _; clearbody Y'; clear e.
  generalize dependent (@fcard X _); intros n Y' ?.
  induction n as [|n IH].
  - exact _.
  - refine (strictlyfinite_equiv _ (equiv_sum_ind Y') _).
    apply strictlyfinite_prod.
    + apply IH; exact _.
    + refine (strictlyfinite_equiv _ (@Unit_ind (fun u => Y' (inr u))) _).
      refine (isequiv_unit_ind (Y' o inr)).
Defined.

#[export] Instance strictlyfinite_quotient `{Univalence} {X} `{StrictlyFinite X}
          (R : Relation X) `{is_mere_relation X R}
          `{Reflexive _ R} `{Transitive _ R} `{Symmetric _ R}
          {Rd : forall x y, Decidable (R x y)}
  : StrictlyFinite (Quotient R).
Proof.
  assert (e := @equiv_fin X H0).
  pose (R' x y := R (e^-1 x) (e^-1 y)).
  assert (is_mere_relation _ R') by exact _.
  assert (Reflexive R') by (intros ?; unfold R'; apply reflexivity).
  assert (Symmetric R') by (intros ? ?; unfold R'; apply symmetry).
  assert (Transitive R') by (intros ? ? ?; unfold R'; exact transitivity).
  assert (R'd : forall x y, Decidable (R' x y))
    by (intros ? ?; unfold R'; apply Rd).
  srefine (strictlyfinite_equiv' _ (equiv_quotient_functor R' R e^-1 _) _).
  1: by try (intros; split).
  clearbody R'; clear e.
  generalize dependent (@fcard X H0);
    intros n. induction n as [|n IH]; intros R' ? ? ? ? ?.
  - refine (strictlyfinite_equiv Empty _^-1 _).
    exact (Quotient_rec R' _ Empty_rec (fun x _ _ => match x with end)).
  - pose (R'' x y := R' (inl x) (inl y)).
    assert (is_mere_relation _ R'') by exact _.
    assert (Reflexive R'') by (intros ?; unfold R''; apply reflexivity).
    assert (Symmetric R'') by (intros ? ?; unfold R''; apply symmetry).
    assert (Transitive R'') by (intros ? ? ?; unfold R''; exact transitivity).
    assert (forall x y, Decidable (R'' x y)) by (intros ? ?; unfold R''; apply R'd).
    assert (inlresp := (fun x y => idmap)
                        : forall x y, R'' x y -> R' (inl x) (inl y)).
    destruct (@dec {x:Fin n & R' (inl x) (inr tt)} (issigmacompact_fin _ _ _)) as [p|np].
    { destruct p as [x r].
      refine (strictlyfinite_equiv' (Quotient R'') _ _).
      refine (Build_Equiv _ _ (Quotient_functor R'' R' inl inlresp) _).
      apply isequiv_surj_emb.
      - apply BuildIsSurjection.
        refine (Quotient_ind_hprop R' _ _).
        intros [y|[]]; apply tr.
        + exists (class_of R'' y); reflexivity.
        + exists (class_of R'' x); simpl.
          apply qglue, r.
      - apply isembedding_isinj_hset; intros u.
        refine (Quotient_ind_hprop R'' _ _); intros v.
        revert u; refine (Quotient_ind_hprop R'' _ _); intros u.
        simpl; intros q.
        apply qglue; unfold R''.
        exact (related_quotient_paths R' (inl u) (inl v) q). }
    { refine (strictlyfinite_equiv' (Quotient R'' + Unit) _ _).
      refine (Build_Equiv _ _ (sum_ind (fun _ => Quotient R')
                                      (Quotient_functor R'' R' inl inlresp)
                                      (fun _ => class_of R' (inr tt))) _).
      apply isequiv_surj_emb.
      - apply BuildIsSurjection.
        refine (Quotient_ind_hprop R' _ _).
        intros [y|[]]; apply tr.
        + exists (inl (class_of R'' y)); reflexivity.
        + exists (inr tt); reflexivity.
      - apply isembedding_isinj_hset; intros u.
        refine (sum_ind _ _ _).
        + refine (Quotient_ind_hprop R'' _ _); intros v.
          revert u; refine (sum_ind _ _ _).
          * refine (Quotient_ind_hprop R'' _ _); intros u.
            simpl; intros q.
            apply ap, qglue; unfold R''.
            exact (related_quotient_paths R' (inl u) (inl v) q).
          * intros []; simpl.
            intros q.
            apply related_quotient_paths in q; try exact _.
            apply symmetry in q.
            elim (np (v ; q)).
        + intros []; simpl.
          destruct u as [u|[]]; simpl.
          * revert u; refine (Quotient_ind_hprop R'' _ _); intros u; simpl.
            intros q.
            apply related_quotient_paths in q; try exact _.
            elim (np (u;q)).
          * intros; reflexivity. }
Defined.

Definition decidable_issemigrouppreserving `{ua : Univalence}
  {G H : Group} (cG : IsPiCompact G)
  (dpH : DecidablePaths H) (f : G -> H)
  : Decidable (IsSemiGroupPreserving f).
Proof.
  apply cG.
  intro g; apply cG.
  intro h.
  by apply dpH.
Defined.

Definition IsHExistsCompact (A : Type)
  := forall P : A -> Type, (forall a : A, Decidable (P a)) -> Decidable (hexists P).

Definition ishprop_ishexistscompact `{Funext} (A : Type)
  : IsHProp (IsHExistsCompact A) := _.

Definition ishexistscompact_issigmacompact `{Funext} {A}
  (c : merely (IsSigmaCompact A))
  : IsHExistsCompact A.
Proof.
  strip_truncations.
  intros P dP.
  destruct (c P dP) as [l|r].
  - left; exact (tr l).
  - right; intros u; by strip_truncations.
Defined.

(* Weaker assumption: [G $-> H] has decidable paths? *)
Definition group_hom_groupreps `{ua : Univalence}
  {G H : Group} (cG' : merely (IsPiCompact G)) (cH : IsHExistsCompact H)
  (cGH : IsSigmaCompact (G $-> H))
  (dpH : DecidablePaths H) (r : groupreps G H)
  : {f : G $-> H & in_class _ r f}.
Proof.
  srapply (fst merely_inhabited_iff_inhabited_stable).
  - rapply stable_decidable.
    apply cGH. intro a.
    apply decidable_in_class.
    intros b c.
    unfold conj_grp_homo.
    strip_truncations.
    apply cH; intro h.
    apply cG'; intro g.
    apply dpH.
  - pose proof (l := @center _ (issurj_class_of _ r)).
    strip_truncations; apply tr.
    exists l.1.
    srapply in_class_of_path.
    exact l.2^.
Defined.

Definition group_hom_groupreps_strictlyfinite `{ua : Univalence} {G H : Group}
  `{StrictlyFinite G} `{StrictlyFinite H} (r : groupreps G H)
  : {f : G $-> H & in_class _ r f}.
Proof.
  rapply group_hom_groupreps.
  - strip_truncations; apply tr.
    apply ispicompact_issigmacompact.
    apply issigmacompact_strictlyfinite.
  - strip_truncations.
    apply ishexistscompact_issigmacompact, tr, issigmacompact_strictlyfinite.
  - napply issigmacompact_strictlyfinite.
    apply (strictlyfinite_equiv' _ (issig_GroupHomomorphism _ _)).
    rapply strictlyfinite_detachable_subset.
    rapply decidable_issemigrouppreserving.
    exact (ispicompact_issigmacompact (issigmacompact_strictlyfinite)).
Defined.

Definition pointed_lift_map_bg `{ua : Univalence}
  {G H : Group} (cG' : merely (IsPiCompact G)) (cH : IsHExistsCompact H)
  (cGH : IsSigmaCompact (G $-> H))
  (dpH : DecidablePaths H) (f : B G -> B H)
  (* note: [B H] is contractible if we get rid of the [merely]. *)
  : {v : G $-> H & merely (f = fmap B v)}.
Proof.
  pose (u := group_hom_groupreps cG' cH cGH _
              ((equiv_groupreps_to_pi0_map_bg _ _)^-1 (tr f))).
  exists u.1.
  apply equiv_path_Tr.
  change (tr f = groupreps_to_pi0_map_bg G H (class_of _ u.1)).
  lhs_V exact (@eisretr _ _ _ (isequiv_groupreps_to_pi0_map_bg G H) (tr f)).
  apply (ap (groupreps_to_pi0_map_bg G H)).
  rapply path_in_class_of.
  exact u.2.
Defined.

Definition pointed_lift_map_bg_strictlyfinite `{ua : Univalence} {G H : Group}
  `{StrictlyFinite G} `{StrictlyFinite H} (f : B G -> B H)
  : {v : G $-> H & merely (f = fmap B v)}.
Proof.
  pose (u := group_hom_groupreps_strictlyfinite
              ((equiv_groupreps_to_pi0_map_bg _ _)^-1 (tr f))).
  exists u.1.
  apply equiv_path_Tr.
  change (tr f = pi0_map_bg_groupreps G H (class_of _ u.1)).
  lhs_V exact (@eisretr _ _ _ (isequiv_pi0_map_bg_groupreps G H) (tr f)).
  apply (ap (pi0_map_bg_groupreps G H)).
  rapply path_in_class_of.
  exact u.2.
Defined.
