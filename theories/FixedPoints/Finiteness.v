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

(* jdc: the name should be "issigmacompact_unit", matching the spelling in the goal.  Same for many results below. *)
(* jdc: maybe best to state this for contractible types?  And make it an Instance? *)
Definition sigmacompact_unit : IsSigmaCompact Unit.
Proof.
  intros P dP.
  rapply (decidable_equiv _ (equiv_contr_sigma _)^-1).
Defined.

(* jdc: should we just use issearchable_bool and the implications? *)
(* jdc: should we decide on a linear order of the various implications between variants of compactness and make one direction of each an instance?  Probably lots in the CompactTypes file should be instances. *)
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

Definition issigmacompact_equiv {A B : Type} (f : A -> B) `{!IsEquiv f}
  (c : IsSigmaCompact B)
  : IsSigmaCompact A
  := sigmacompact_retract (eissect f) c.

Definition sigmacompact_sigma {A : Type} {P : A -> Type}
  (cA : IsSigmaCompact A) (cP : forall (a : A), IsSigmaCompact (P a))
  : IsSigmaCompact (sig P).
Proof.
  intros Q dQ.
  apply (decidable_equiv _ (equiv_sigma_assoc P Q)).
  apply cA; intro a.
  by apply cP; intro p.
Defined.

Definition sigmacompact_detachable_subset {A : Type} {P : A -> HProp}
  (cA : IsSigmaCompact A) (dP : forall (a : A), Decidable (P a))
  : IsSigmaCompact (sig P).
Proof.
  srapply (sigmacompact_sigma cA); cbn beta.
  intro a.
  destruct (equiv_decidable_hprop (P a)) as [e1|e2].
  - rapply (issigmacompact_equiv e1).
    exact sigmacompact_unit.
  - rapply (issigmacompact_equiv e2).
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
  apply (issigmacompact_equiv (sig_of_sum A B)).
  apply sigmacompact_sigma.
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
