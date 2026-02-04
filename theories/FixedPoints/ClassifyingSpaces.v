(** * Mapping spaces between classifying spaces *)

From HoTT Require Import Basics Types.
(* Results from Truncations.Constant might be useful as this progresses. *)
Require Import Truncations.Core Truncations.Connectedness Truncations.Constant.
Require Import Algebra.Groups.Group Subgroup Algebra.AbGroups.Centralizer.
Require Import Pointed WildCat WildCat.Core.
Require Import Homotopy.ClassifyingSpace.
Require Import Colimits.Quotient.
Require Import Cubical.DPath PathSquare.
Require Export Classes.interfaces.canonical_names (SgOp, sg_op,
    MonUnit, mon_unit, LeftIdentity, left_identity, RightIdentity, right_identity,
    Negate, negate, Associative, simple_associativity, associativity,
    LeftInverse, left_inverse, RightInverse, right_inverse, Commutative, commutativity).
Require Import FixedPoints.Groups.
Export canonical_names.BinOpNotations.
Export Homotopy.ClassifyingSpace.ClassifyingSpaceNotation.

Local Open Scope pointed_scope.
Local Open Scope trunc_scope.
Local Open Scope mc_mult_scope.
Local Open Scope path_scope.

Definition idmap_fmap_grp_conj {G : Group} (g : G)
  : fmap B (grp_conj g) == idmap.
Proof.
  srapply ClassifyingSpace_ind_hset.
  - exact (bloop g).
  - intro x.
    rapply equiv_sq_dp^-1.
    snapply equiv_sq_path.
    rewrite ClassifyingSpace_rec_beta_bloop.
    rhs_V rapply bloop_pp.
    rewrite ap_idmap.
    lhs_V rapply bloop_pp.
    by rhs rapply (ap bloop (grp_inv_gV_g _ g)).
Defined.

(* This map should be an equivalence on [pi 0]. *)
Definition rep_bg_to_bh `{U : Univalence} (G H : Group)
  : groupreps G H -> Trunc 0 (B G -> B H).
Proof.
  unshelve refine (Quotient_rec _ _ _ _).
  - intro f.
    apply tr.
    exact (fmap B (a := G) (b := H) f).
  - intros a b [h r].
    apply ap.
    apply path_forall.
    lhs' exact (fmap2 (g:=grp_conj h $o b) B r).
    lhs' exact (fmap_comp B b (grp_conj h)).
    (* Define an unpointed B functor by composing with [pType -> Type]. *)
    intro x.
    exact (idmap_fmap_grp_conj h _).
Defined.

(* tr being equal means that the maps are merely equal. *)
Definition inj_rep_bg_to_bh `{U : Univalence} {G H : Group} (u v : G $-> H)
  (p : tr (n:=0) (pointed_fun (fmap B (a := G) (b := H) u)) = tr (pointed_fun (fmap B (a := G) (b := H) v)))
  : merely {h : H & u == grp_conj h $o v}.
Proof.
Admitted.

Definition isequiv_rep_bg_to_bh `{U : Univalence} (G H : Group)
  : IsEquiv (rep_bg_to_bh G H).
Proof.
  apply equiv_contr_map_isequiv.
  intro f.
  strip_truncations.
  generalize (merely_path_is0connected (B H) (f bbase) bbase).
  intro q.
  strip_truncations.
  srapply Build_Contr.
  - unshelve econstructor.
    { unfold groupreps.
      apply class_of.
      apply equiv_grp_homo_pmap_bg.
      srapply Build_pMap.
      1: exact f.
      exact q. }
    { unfold rep_bg_to_bh.
      admit. }
  - 
  (* Do this in a separate lemma, generalising the first map (any two maps that are sent to the same thing are conjugate). *)
    intros [u p].
    srapply path_sigma_hprop.
    unfold ".1".
    snapply (path_in_class_of _ _ _ _)^.
    1,2,3,4: admit.
Admitted.
