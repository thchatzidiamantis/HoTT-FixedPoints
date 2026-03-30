(** * Strictly finite groups *)

From HoTT Require Import Basics Types.
Require Import Truncations.Core Truncations.Connectedness Truncations.SeparatedTrunc.
Require Import Spaces.Finite.
Require Import Universes.HProp.
Require Import Homotopy.ClassifyingSpace HomotopyGroup WhiteheadsPrinciple.
Require Import Misc.BoundedSearch CompactTypes.
Require Import Algebra.Groups.Group Subgroup Algebra.AbGroups.Centralizer.
Require Import Colimits.Quotient.
Require Import Pointed WildCat.Core.
Require Import FixedPoints.Groups ClassifyingSpaces.
Require Export Classes.interfaces.canonical_names (SgOp, sg_op,
    MonUnit, mon_unit, LeftIdentity, left_identity, RightIdentity, right_identity,
    Negate, negate, Associative, simple_associativity, associativity,
    LeftInverse, left_inverse, RightInverse, right_inverse, Commutative, commutativity).
Export canonical_names.BinOpNotations.
Export Homotopy.ClassifyingSpace.ClassifyingSpaceNotation.

Local Open Scope pointed_scope.
Local Open Scope trunc_scope.
Local Open Scope mc_mult_scope.
Local Open Scope path_scope.

(** ** More on Compact Types *)

(* jdc: maybe best to state this for contractible types?  And make it an Instance? *)
Definition issigmacompact_contr {A : Type} `{Contr A} : IsSigmaCompact A.
Proof.
  intros P dP.
  rapply (decidable_equiv _ (equiv_contr_sigma _)^-1).
Defined.

(* jdc: should we just use issearchable_bool and the implications? *)
(* jdc: should we decide on a linear order of the various implications between variants of compactness and make one direction of each an instance?  Probably lots in the CompactTypes file should be instances. *)
Definition issigmacompact_bool : IsSigmaCompact Bool.
Proof.
  intros P dP.
  destruct (dP true) as [a | na].
  1: left; exact (true; a).
  destruct (dP false) as [b | nb].
  1: left; exact (false; b).
  right; intros [x px].
  destruct x.
  1: exact (na px).
  exact (nb px).
Defined.

(* tcc: this exists for the other (equivalent) definition of [IsCompact]. I think I need to restructure that file and make it focus on [IsSigmaCompact] and [IsPiCompact]. *)
Definition issigmacompact_retract {A R : Type} {f : A -> R} {g : R -> A}
  (s : f o g == idmap) (c : IsSigmaCompact A)
  : IsSigmaCompact R.
Proof.
  intros P dP; destruct (c (P o f) _) as [u|v].
  1: left; exact (f u.1; u.2).
  right; intros [r pr].
  apply v.
  exists (g r).
  exact ((s r)^ # pr).
Defined.

Definition issigmacompact_equiv {A B : Type} (f : A -> B) `{!IsEquiv f}
  (c : IsSigmaCompact B)
  : IsSigmaCompact A
  := issigmacompact_retract (eissect f) c.

Definition issigmacompact_sigma {A : Type} {P : A -> Type}
  (cA : IsSigmaCompact A) (cP : forall (a : A), IsSigmaCompact (P a))
  : IsSigmaCompact (sig P).
Proof.
  intros Q dQ.
  apply (decidable_equiv _ (equiv_sigma_assoc P Q)).
  apply cA; intro a.
  by apply cP; intro p.
Defined.

Definition issigmacompact_detachable_subset {A : Type} {P : A -> HProp}
  (cA : IsSigmaCompact A) (dP : forall (a : A), Decidable (P a))
  : IsSigmaCompact (sig P).
Proof.
  srapply (issigmacompact_sigma cA); cbn beta.
  intro a.
  destruct (equiv_decidable_hprop (P a)) as [e1|e2].
  - rapply (issigmacompact_equiv e1).
    exact issigmacompact_contr.
  - rapply (issigmacompact_equiv e2).
    exact (fun P dP => inr proj1).
Defined.

Definition issigmacompact_sum {A B : Type}
  (cA : IsSigmaCompact A) (cB : IsSigmaCompact B)
  : IsSigmaCompact (A + B).
Proof.
  apply (issigmacompact_equiv (sig_of_sum A B)).
  apply issigmacompact_sigma.
  - exact issigmacompact_bool.
  - by destruct a.
Defined.

(* See if this follows from BoundedSearch and give a comment. *)
Definition issigmacompact_fin {n : nat}
  : IsSigmaCompact (Fin n).
Proof.
  induction n.
  - exact (fun P dP => inr proj1).
  - apply (issigmacompact_sum IHn).
    exact issigmacompact_contr.
Defined.

(** ** Strictly finite types *)

Class StrictlyFinite (X : Type) :=
  { fcard : nat ;
    equiv_fin : X <~> Fin fcard }.

Definition issig_strictlyfinite X
  : { n : nat & (X <~> Fin n) } <~> StrictlyFinite X.
Proof.
  issig.
Defined.

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
  := issigmacompact_equiv equiv_fin issigmacompact_fin.

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

Instance strictlyfinite_decidable_hprop X `{IsHProp X} `{Decidable X}
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
  exact _.
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

(* Weaker assumption: [G $-> H] has decidable paths? *)
Definition group_hom_groupreps `{ua : Univalence}
  {G H : Group} (cG' : IsPiCompact G) (cH : IsSigmaCompact H)
  (cGH : IsSigmaCompact (G $-> H))
  (dpH : DecidablePaths H) (r : groupreps G H)
  : {f : G $-> H & in_class _ r f}.
Proof.
  srapply (fst merely_inhabited_iff_inhabited_stable).
  - rapply stable_decidable.
    (* tcc: [srapply] freezes the whole thing here. *)
    apply cGH. intro a.
    apply decidable_in_class.
    intros b c.
    unfold conj_grp_homo.
    apply decidable_trunc_decidable.
    apply cH; intro h.
    apply cG'; intro g.
    apply dpH.
  - pose proof (l := @center _ (issurj_class_of _ r)).
    strip_truncations; apply tr.
    exists l.1.
    srapply in_class_of_path.
    exact l.2^.
Time Defined.

Definition group_hom_groupreps_strictlyfinite `{ua : Univalence} {G H : Group}
  `{StrictlyFinite G} `{StrictlyFinite H} (r : groupreps G H)
  : {f : G $-> H & in_class _ r f}.
Proof.
  apply group_hom_groupreps.
  - apply ispicompact_issigmacompact.
    rapply issigmacompact_strictlyfinite.
  - rapply issigmacompact_strictlyfinite.
  - rapply issigmacompact_strictlyfinite.
    apply (strictlyfinite_equiv' _ (issig_GroupHomomorphism _ _)).
    apply strictlyfinite_detachable_subset.
    + exact _.
    + Set Typeclasses Debug.
      Fail Timeout 1 exact _.
      (* You introduced a typeclass search loop above, for hprops:

         Goal:  Decidable foo (where foo is IsSemiGroupPreserving x).
         Tries: decidable_finite_hprop.  Solves hprop part.
         Goal:  Finite foo.
         Tries: finite_strictlyfinite.
         Goal:  StrictlyFinite foo.
         Tries: strictly_finite_decidable_hprop.  Solves hprop part.
         Goal:  Decidable foo.
      *)
      apply decidable_issemigrouppreserving.
      1: apply (ispicompact_issigmacompact (issigmacompact_strictlyfinite)).
      exact (decidablepaths_equiv _ (equiv_fin)^-1 _).
  - exact (decidablepaths_equiv _ (equiv_fin)^-1 _).
Defined.

Definition pointed_lift_map_bg `{ua : Univalence}
  {G H : Group} (cG' : IsPiCompact G) (cH : IsSigmaCompact H)
  (cGH : IsSigmaCompact (G $-> H))
  (dpH : DecidablePaths H) (f : B G -> B H)
  (* note: [B H] is contractible if we get rid of the [merely]. *)
  : {v : G $-> H & merely (f = fmap B v)}.
Proof.
  pose (u := group_hom_groupreps cG' cH cGH _
              ((equiv_groupreps_pi0_map_bg _ _)^-1 (tr f))).
  exists u.1.
  apply equiv_path_Tr.
  change (tr f = pi0_map_bg_groupreps G H (class_of _ u.1)).
  lhs_V exact (@eisretr _ _ _ (isequiv_pi0_map_bg_groupreps G H) (tr f)).
  apply (ap (pi0_map_bg_groupreps G H)).
  rapply path_in_class_of.
  exact u.2.
Defined.

Definition pointed_lift_map_bg_strictlyfinite `{ua : Univalence} {G H : Group}
  `{StrictlyFinite G} `{StrictlyFinite H} (f : B G -> B H)
  : {v : G $-> H & merely (f = fmap B v)}.
Proof.
  pose (u := group_hom_groupreps_strictlyfinite
              ((equiv_groupreps_pi0_map_bg _ _)^-1 (tr f))).
  exists u.1.
  apply equiv_path_Tr.
  change (tr f = pi0_map_bg_groupreps G H (class_of _ u.1)).
  lhs_V exact (@eisretr _ _ _ (isequiv_pi0_map_bg_groupreps G H) (tr f)).
  apply (ap (pi0_map_bg_groupreps G H)).
  rapply path_in_class_of.
  exact u.2.
Defined.
