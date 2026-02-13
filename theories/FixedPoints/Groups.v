(** * Group-theoretic requirements for the fixed points project *)

From HoTT Require Import Basics Types.
Require Import Circle.
Require Import Suspension.
Require Import Truncations.Core Truncations.Connectedness Truncations.Constant.
(* Results from Truncations.Constant might be useful as this progresses. *)
Require Import HSpace.Core.
Require Import Homotopy.ClassifyingSpace.
Require Import Algebra.Groups.Group Subgroup Algebra.AbGroups.Centralizer.
Require Import Colimits.Quotient.
Require Import Pointed WildCat WildCat.Core.
Require Import Cubical.DPath PathSquare.
Require Export Classes.interfaces.canonical_names (SgOp, sg_op,
    MonUnit, mon_unit, LeftIdentity, left_identity, RightIdentity, right_identity,
    Negate, negate, Associative, simple_associativity, associativity,
    LeftInverse, left_inverse, RightInverse, right_inverse, Commutative, commutativity).
Export canonical_names.BinOpNotations.

Local Open Scope pointed_scope.
Local Open Scope trunc_scope.
Local Open Scope mc_mult_scope.
Local Open Scope path_scope.

(** ** Centralizers of general subtypes *)

Definition subtype_centralizer {G : Group} (H : G -> Type)
  : G -> Type
  (* Note the order of operations here, we do this to match the original proofs for the centraliser of an element. *)
  := fun g => merely (forall h : G, H h -> centralizer h g).

(* Need Funext to prove that this [subtype_centralizer] is [HProp]-valued. *)
Instance issubgroup_subtype_centralizer
  {G : Group} (H : G -> Type)
  : IsSubgroup (subtype_centralizer H).
Proof.
  srapply Build_IsSubgroup.
  - apply tr.
    intros h Hh.
    exact (centralizer_unit h).
  - intros x y cx cy.
    strip_truncations; apply tr.
    intros h Hh.
    exact (centralizer_sgop _ _ _ (cx h Hh) (cy h Hh)).
  - intros x Hx.
    strip_truncations; apply tr.
    intros h Hh.
    exact (centralizer_inverse h x (Hx h Hh)).
Defined.

Definition subtype_centralizer_subgroup
  {G : Group} (H : G -> Type)
  := Build_Subgroup G (subtype_centralizer H) _.

(* remove this later *)
Definition b_subtype_centralizer {G : Group} (H : G -> Type)
  : Type.
Proof.
  apply ClassifyingSpace.
  apply (subgroup_group (G:=G)).
  exists (subtype_centralizer H); exact _.
Defined.

Definition grp_hom_centralizer_image_grp_hom
  {G H : Group} (f : G $-> H)
  : grp_prod (subtype_centralizer_subgroup (grp_image f)) G
    $-> H.
Proof.
  snapply Build_GroupHomomorphism.
  1,2: intros [[x Cx] y].
  - exact (x * f y).
  - intros [[z Cz] w]; cbn.
    strip_truncations.
    refine (grp_assoc _ (f y) (f w) @ _ # ap _ (grp_homo_op _ _ _)).
    lhs_V exact (ap (.* f w) (grp_assoc x z (f y))).
    lhs_V exact (ap (fun r => x * r * (f w)) (Cz (f y) (tr (y; 1)))).
    lhs exact (ap (.* f w) (grp_assoc x (f y) z)).
    exact (grp_assoc (x * (f y)) z (f w))^.
Defined.

Definition grp_image_factorization {G H K : Group} (u : G $-> H) (v : H $-> K)
  : (v $o u) $== (grp_homo_restr v _) $o grp_homo_image_in u
  := fun x => idpath.

Definition grp_image_homotopic_grp_homo
  {G H : Group} {u v : G $-> H} (p : u $== v)
  : subgroup_group (grp_image u) $-> subgroup_group (grp_image v).
Proof.
  srapply subgroup_corec.
  + snapply Build_GroupHomomorphism.
    - exact pr1.
    - intros x y; reflexivity.
  + intros [h uh].
    strip_truncations; apply tr.
    exact (uh.1; (p _)^ @ uh.2).
Defined.

Definition inv_grp_image_homotopic_grp_homo
  {G H : Group} {u v : G $-> H} (p : u $== v) (q : v $== u)
  : (grp_image_homotopic_grp_homo p) o (grp_image_homotopic_grp_homo q) == idmap.
Proof.
  intro x.
  apply path_sigma_hprop.
  reflexivity.
Defined.

Definition grp_iso_grp_image_homotopic_grp_homo
  {G H : Group} {u v : G $-> H} (p : u $== v)
  : subgroup_group (grp_image u) $<~> subgroup_group (grp_image v).
Proof.
  srapply Build_GroupIsomorphism.
  1: exact (grp_image_homotopic_grp_homo p).
  srapply isequiv_adjointify.
  1: exact (grp_image_homotopic_grp_homo (fun x => (p x)^)).
  1,2: by apply inv_grp_image_homotopic_grp_homo.
Defined.

Definition conj_grp_homo {G H : Group} (u v : G $-> H)
  := merely {h : H & forall g : G, u g = grp_conj h (v g)}.

(* I guess I can do these on the level of elements first *)

Instance reflexive_conj_grp_homo {G H : Group}
  : Reflexive (conj_grp_homo (G:=G) (H:=H)).
Proof.
  intro u.
  apply tr.
  exists group_unit.
  intro g; by rhs exact (grp_conj_unit (u g)).
Defined.

Instance symmetric_conj_grp_homo {G H : Group}
  : Symmetric (conj_grp_homo (G:=G) (H:=H)).
Proof.
  intros u v cuv.
  strip_truncations; apply tr.
  destruct cuv as [h ch].
  exists (inv h).
  intro g.
  unfold grp_conj; cbn.
  rewrite grp_inv_inv.
  refine (grp_moveL_gM _).
  refine (grp_moveL_Vg _).
  lhs apply (grp_assoc h (v g) (inv h)).
  exact (ch g)^.
Defined.

(* get rid of rewrites here *)
Instance transitive_conj_grp_homo {G H : Group}
  : Transitive (conj_grp_homo (G:=G) (H:=H)).
Proof.
  intros u v w cuv cvw.
  strip_truncations; apply tr.
  destruct cuv as [h1 ch1]; destruct cvw as [h2 ch2].
  exists (h1 * h2).
  intro g.
  specialize (ch1 g); specialize (ch2 g).
  rewrite ch2 in ch1.
  unfold grp_conj in ch1; cbn in ch1.
  repeat rewrite (grp_assoc h1 _) in ch1.
  rewrite <- (grp_assoc _ (inv h1)) in ch1.
  rewrite <- grp_inv_op in ch1.
  exact ch1.
Defined.

Definition groupreps (G H : Group) : Type
  := (@Quotient (G $-> H) (conj_grp_homo)).
