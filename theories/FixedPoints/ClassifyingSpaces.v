(** * Mapping spaces between classifying spaces *)

From HoTT Require Import Basics Types.
Require Import Universes.HProp.
Require Import Truncations.Core Truncations.Connectedness Truncations.Constant SeparatedTrunc.
Require Import Algebra.Groups.Group Subgroup Algebra.AbGroups.Centralizer.
Require Import Pointed WildCat WildCat.Core.
Require Import Homotopy.ClassifyingSpace.
Require Import Colimits.Quotient GraphQuotient.
Require Import Cubical.DPath PathSquare.
Require Export Classes.interfaces.canonical_names (SgOp, sg_op,
    MonUnit, mon_unit, LeftIdentity, left_identity, RightIdentity, right_identity,
    Negate, negate, Associative, simple_associativity, associativity,
    LeftInverse, left_inverse, RightInverse, right_inverse, Commutative, commutativity).
Require Import FixedPoints.Groups.
Require Import Homotopy.HomotopyGroup.
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

(* This map will be an equivalence on [Pi 0]. *)
Definition pi0_map_bg_groupreps `{U : Univalence} (G H : Group)
  : groupreps G H -> Trunc 0 (B G -> B H).
Proof.
  unshelve refine (Quotient_rec _ _ _ _).
  - intro f.
    apply tr.
    exact (fmap B (a := G) (b := H) f).
  - intros a b h.
    strip_truncations; destruct h as [h r].
    apply ap.
    apply path_forall.
    lhs' exact (fmap2 (g:=grp_conj h $o b) B r).
    lhs' exact (fmap_comp B b (grp_conj h)).

    (* TODO: define an unpointed B functor by composing with [pType -> Type]. *)

    intro x.
    exact (idmap_fmap_grp_conj h _).
Defined.

Definition ap_fmap_b `{U : Univalence} {G H : Group} (u : G $-> H) (g : G)
  : ap (fmap B u) (bloop g) = bloop (u g)
  := ClassifyingSpace_rec_beta_bloop _ _ _ _ _.

Definition isinjective_pi0_map_bg_groupreps `{U : Univalence}
  {G H : Group} (u v : G $-> H)
  (p : pi0_map_bg_groupreps G H (class_of _ u) = pi0_map_bg_groupreps G H (class_of _ v))
  : merely {h : H & u == grp_conj h $o v}.
Proof.
  apply (equiv_path_Tr _ _)^-1 in p.
  strip_truncations; apply tr.
  pose (h := equiv_g_loops_bg^-1 (ap10 p bbase)).
  exists h.
  intro x.
  simpl.
  rewrite (eissect equiv_g_loops_bg _)^.
  rewrite (eissect equiv_g_loops_bg (h * v x * inv h))^.
  apply ap; simpl.
  repeat rewrite bloop_pp.
  rewrite bloop_inv.
  rewrite eisretr.
  repeat rewrite <- ap_fmap_b.
  exact  (ap_homotopic (ap10 p) (bloop x)).
Defined.

Definition isemb_pi0_map_bg_groupreps `{U : Univalence} {G H : Group}
  : IsEmbedding (pi0_map_bg_groupreps G H).
Proof.
  intro x.
  apply hprop_allpath.
  intros [u pu] [v pv].
  srapply path_sigma_hprop; unfold ".1".
  pose proof (p := pu @ pv^); clear pu pv.

  (* tcc: in the next five lines I use surjectivity of [class_of] to lift [u] and [v] to representatives in [G $-> H]. Can this be made faster? I tried to use [conn_map_elim], but that changed only one of the terms. *)

  pose proof (s := issurj_class_of conj_grp_homo (A:=G$->H)).
  pose proof (a := center _ (H:=(s u))); pose proof (b := center _ (H:=(s v))).
  strip_truncations.
  destruct a as [a pa]; destruct b as [b pb].
  rewrite <- pa, <- pb in *.
  srapply path_quotient.
  exact (isinjective_pi0_map_bg_groupreps _ _ p).
Defined.

Definition issurj_pi0_map_bg_groupreps `{U : Univalence} {G H : Group}
  : IsSurjection (pi0_map_bg_groupreps G H).
Proof.
  apply BuildIsSurjection.
  intro f.
  strip_truncations.
  (* Since [B H] is connected and our goal is a proposition, we can assume that [f] is pointed. *)
  pose proof (q:=merely_path_is0connected (B H) (f bbase) bbase).
  strip_truncations.
  (* The next four lines replace [f] by [pointed_fun fp] for a general pointed map [fp]. *)
  pose (fp:=Build_pMap f q).
  change f with (pointed_fun fp).
  clearbody fp; clear q f.

  (* The previous six lines can be replaced by the following, which is just using that the forgetful map [pointed_fun] is surjective. This last fact is proved as the subgoal, but could be made into a lemma.  So even though this is a bit longer, it is more conceptual, so I think it's better. *)
  (*
  revert f.
  rapply (conn_map_elim (-1) (pointed_fun : (B G ->* B H) -> _)).
  { intro f.
    rapply contr_inhabited_hprop.
    pose proof (q:=merely_path_is0connected (B H) (f bbase) bbase).
    strip_truncations; apply tr.
    exists (Build_pMap f q).
    reflexivity. }
  intro fp.
  *)

  apply tr.
  exists (class_of _ ((equiv_grp_homo_pmap_bg _ _)^-1 fp)).
  unfold pi0_map_bg_groupreps.
  unfold Quotient_rec, class_of.
  unfold Trunc_rec, Trunc_ind.
  unfold GraphQuotient_rec, GraphQuotient_ind.
  apply ap.
  (* Reveal [pointed_fun], to make things more clear to the reader. *)
  Set Printing Coercions.
  (* Our goal is an equality of *unpointed* maps.  Let's upgrade it to an equality of pointed maps. *)
  apply ap.
  Unset Printing Coercions.
  apply eisretr.

(* tcc: no errors in this proof until the `Defined` line, where I get "Case analysis on private inductive Trunc". *)

Defined.

Definition isequiv_pi0_map_bg_groupreps `{U : Univalence} (G H : Group)
  : IsEquiv (pi0_map_bg_groupreps G H).
Proof.
  apply isequiv_surj_emb.
  - exact issurj_pi0_map_bg_groupreps.
  - exact isemb_pi0_map_bg_groupreps.
Defined.

Definition equiv_groupreps_pi0_map_bg `{U : Univalence} (G H : Group)
  : (groupreps G H) <~> Pi 0 [(B G -> B H), (fun x => bbase)]
  := Build_Equiv _ _ _ (isequiv_pi0_map_bg_groupreps G H).
