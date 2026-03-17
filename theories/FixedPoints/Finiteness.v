(** * Strictly finite groups *)

From HoTT Require Import Basics Types.
(* Require Import Truncations.Core Truncations.Connectedness Truncations.Constant. *)
Require Import Spaces.Finite.
Require Import Universes.HProp.
Require Import Misc.BoundedSearch CompactTypes.
Require Import Algebra.Groups.Group Subgroup Algebra.AbGroups.Centralizer.
Require Import Colimits.Quotient.
Require Import Pointed WildCat WildCat.Core.
(* Require Import FixedPoints.Groups FixedPointProperty ClassifyingSpaces. *)
Require Export Classes.interfaces.canonical_names (SgOp, sg_op,
    MonUnit, mon_unit, LeftIdentity, left_identity, RightIdentity, right_identity,
    Negate, negate, Associative, simple_associativity, associativity,
    LeftInverse, left_inverse, RightInverse, right_inverse, Commutative, commutativity).
Export canonical_names.BinOpNotations.

Local Open Scope pointed_scope.
Local Open Scope trunc_scope.
Local Open Scope mc_mult_scope.
Local Open Scope path_scope.

(** ** More on Compact Types *)

Definition sigmacompact_unit : IsSigmaCompact Unit.
Proof.
  intros P dP.
  rapply (decidable_equiv _ (equiv_contr_sigma _)^-1).
Defined.

Definition sigmacompact_bool : IsSigmaCompact Bool.
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
Definition sigmacompact_retract {A R : Type} {f : A -> R} {g : R -> A}
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

Definition sigmacompact_sigma {A : Type} {P : A -> Type}
  (cA : IsSigmaCompact A) (cP : forall (a : A), IsSigmaCompact (P a))
  : IsSigmaCompact (sig P).
Proof.
  intros Q dQ.
  pose (R := fun a => {x : P a & Q (a; x)}).
  assert (dR : forall a, Decidable (R a)).
  { intros; apply cP.
    intros; apply dQ. }
  destruct (cA R dR) as [u|v].
  1: left; exact ((u.1; u.2.1); u.2.2).
  right; intros x.
  exact (v (x.1.1; (x.1.2; x.2))).
Defined.

Definition sigmacompact_detachable_subset {A : Type} {P : A -> HProp}
  (cA : IsSigmaCompact A) (dP : forall (a : A), Decidable (P a))
  : IsSigmaCompact (sig P).
Proof.
  srapply (sigmacompact_sigma cA).
  intro a.
  destruct (equiv_decidable_hprop (P a)) as [e1|e2].
  - rapply (sigmacompact_retract (eissect e1)).
    exact sigmacompact_unit.
  - rapply (sigmacompact_retract (eissect e2)).
    exact (fun P dP => inr proj1).
Defined.

Definition sigmacompact_detachable_subset' {A : Type} {P : A -> Type}
  (cA : IsSigmaCompact A) (dP : forall (a : A), Decidable (P a))
  : IsSigmaCompact (sig P).
Proof.
  intros Q dQ.
  pose (R := fun a => match (dP a) with
                      | inl p => Q (a; p)
                      | inr _ => Empty
                    end).
  assert (dR : forall a, Decidable (R a)).
  { intro a.
    remember (dP a) as k eqn:e.
    destruct k as [p|].
    - unfold R; rewrite e.
      apply dQ.
    - unfold R; rewrite e.
      exact _. }
  destruct (cA R dR) as [[a u]|v].
  { left.
    unfold R in u.
    remember (dP a) as k eqn:e.
    destruct k as [p|].
    - exact ((a; p); u).
    - exact (Empty_rec u). }
  { right; intros [[a p] q].
    apply v; unfold R.
    exists a.
    remember (dP a) as r eqn:e.
    destruct r as [l|].
    (* tcc: I think the proof fails here. We can't know if [p = l], so we can't transport [q] unless [P a] is an [HProp]. *)
    - admit.
    - admit. }
Abort.

Definition sigmacompact_sum {A B : Type}
  (cA : IsSigmaCompact A) (cB : IsSigmaCompact B)
  : IsSigmaCompact (A + B).
Proof.
  rapply (sigmacompact_retract (@eissect _ _ _ (isequiv_sig_of_sum A B))).
  rapply sigmacompact_sigma.
  - exact sigmacompact_bool.
  - by destruct a.
Defined.

Definition sigmacompact_fin {n : nat}
  : IsSigmaCompact (Fin n).
Proof.
  induction n.
  - exact (fun P dP => inr proj1).
  - apply (sigmacompact_sum IHn).
    exact sigmacompact_unit.
Defined.

(** ** Strictly finite types *)

Class StrictlyFinite (X : Type) :=
  { fcard : nat ;
    equiv_fin : X <~> Fin fcard }.

Definition sigmacompact_strictlyfinite {A : Type} `{StrictlyFinite A}
  : IsSigmaCompact A.
Proof.
  srapply (sigmacompact_retract (eissect equiv_fin)).
  exact sigmacompact_fin.
Defined.
