(** * Mapping spaces between classifying spaces *)

From HoTT Require Import Basics Types.
Require Import Universes.HProp Universes.HSet.
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

(** ** Connected components of [B G -> B H] *)

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

Definition ap_fmap_b {G H : Group} (u : G $-> H) (g : G)
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
  apply (equiv_inj equiv_g_loops_bg).
  simpl.
  rewrite 2 bloop_pp.
  rewrite bloop_inv.
  (* [h] is defined by applying [equiv_g_loops_bg^-1] and [bloop] is the inverse of that function. *)
  rewrite eisretr.
  rewrite <- 2 ap_fmap_b.
  exact (ap_homotopic (ap10 p) (bloop x)).
Defined.

Definition isemb_pi0_map_bg_groupreps `{U : Univalence} {G H : Group}
  : IsEmbedding (pi0_map_bg_groupreps G H).
Proof.
  apply isembedding_isinj_hset.
  (* jdc: juggling the intros here gets rid of one use of Funext per call to [conn_map_elim] (but we still need it once for each call). Minor point, but good practice. *)
  intros u.
  rapply (conn_map_elim (-1) (class_of _)).
  intro v; revert u.
  rapply (conn_map_elim (-1) (class_of _)).
  intros u p.
  rapply path_quotient.
  exact (isinjective_pi0_map_bg_groupreps _ _ p).
Defined.

Definition isemb_pi0_map_bg_groupreps' `{U : Univalence} {G H : Group}
  : IsEmbedding (pi0_map_bg_groupreps G H).
Proof.
  apply isembedding_isinj_hset.
  rapply Quotient_ind2_hprop.
  intros u v p.
  srapply path_quotient.
  exact (isinjective_pi0_map_bg_groupreps _ _ p).
Defined.

(** TODO: The above argument generalizes.  This can go at the end of Universes/HSet.v and be used above. *)
(** TODO: Can [Funext] be avoided? *)
Definition cancelR_isinjective_surj `{Funext} {A B C : Type} `{IsHSet B}
  (f : A -> B) (g : B -> C)
  (inj_gf : IsInjective (g o f)) (surj_f : IsSurjection f)
  : IsInjective g.
Proof.
  intros u.
  rapply (conn_map_elim (-1) f).
  intro v; revert u.
  rapply (conn_map_elim (-1) f).
  intros u p.
  apply ap, inj_gf, p.
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
  (* The next three lines replace [f] by [pointed_fun fp] for a general pointed map [fp]. *)
  pose (fp:=Build_pMap f q).
  change f with (pointed_fun fp).
  clearbody fp; clear q f.

  (* The previous five lines can be replaced by the following, which is just using that the forgetful map [pointed_fun] is surjective. This last fact is proved as the subgoal, but could be made into a lemma.  So even though this is a bit longer, it is more conceptual, so I think it's better. *)
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
  change (_ = ?R) with (tr (pointed_fun (fmap B ((equiv_grp_homo_pmap_bg G H)^-1 fp))) = R).
  apply ap.
  (* Reveal [pointed_fun], to make things more clear to the reader. *)
  Set Printing Coercions.
  (* Our goal is an equality of *unpointed* maps.  Let's upgrade it to an equality of pointed maps. *)
  apply ap.
  Unset Printing Coercions.
  apply eisretr.
  (* jdc: I'm not sure what was going on, but it was the [unfold Trunc_ind] that was causing it.  Doing the unfolding all at once to get to the goal we expect made the problem go away. *)
Defined.

(* jdc: while investigating the above, I came up with a shorter, more conceptual proof, which I have included below.  It actually had the same private inductive error, which was also fixed by using a [change] tactic.  I think we should delete the proof above.  (Feel free to delete comments like this when no longer needed.) *)

(** When [Y] is connected, every function [X -> Y] is merely pointed, so [pointed_fun] is a surjection. *)
Instance issurj_pointed_fun_conn `{Univalence} {X Y : pType} `{IsConnected 0 Y}
  : IsSurjection (pointed_fun : (X ->* Y) -> (X -> Y)).
Proof.
  apply (cancelR_issurjection (issig_pmap X Y)); cbn.
  rapply conn_map_pr1.
Defined.

(** It follows that [pi0_map_bg_groupreps] is surjective.  By definition, we have a commutative diagram
<<
         fmap B             pointed_fun
  G $-> H   <~>   (BG ->* BH)  ---------->  (BG -> BH)
     |                                      |
  gq |                                      | tr
     v                                      v
  groupreps G H ------------------> Tr 0 (BG -> BH)
                pi0_map_bg_groupreps
>>
    To show that [pi0_map_bg_groupreps] is surjective, it suffices to show that this is true after precomposition with [gq], and so we just need to show that the other three maps are surjective.  Rocq can prove these by typeclass search, with one hint for [tr]. *)
Definition issurj_pi0_map_bg_groupreps' `{U : Univalence} {G H : Group}
  : IsSurjection (pi0_map_bg_groupreps G H).
Proof.
  apply (cancelR_issurjection (class_of _)).
  change (IsConnMap (Tr (-1)) (tr (n:=0) o pointed_fun o fmap (a:=G) (b:=H) B)).
  pose (@isconnmap_pred' 0). (* [tr] is in fact 0-connected, so we give this hint. *)
  exact _.
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

(** ** The fundamental group of [B G -> B H] *)

Definition map_bg_b_centralizer_grp_image
  {G H : Group} (f : G $-> H)
  : B (subtype_centralizer_subgroup (grp_image f)) -> (B G -> B H).
Proof.
  napply (fmap11_B (subgroup_incl _) f).
  intros [h ch] g; cbn.
  symmetry.
  strip_truncations.
  exact (ch (f g) (tr (g; idpath))).
Defined.

Definition map_bg_b_centralizer_grp_image' `{F : Funext}
  {G H : Group} (f : G $-> H)
  : B (subtype_centralizer_subgroup (grp_image f)) -> (B G -> B H).
Proof.
  srapply ClassifyingSpace_rec.
  { exact (pointed_fun (fmap B f)). }
  { intros [h ch].
    unfold subtype_centralizer_subgroup, subtype_centralizer, centralizer in ch; cbn in ch.
    apply path_forall.
    srapply ClassifyingSpace_ind_hset; cbn beta.
    - simpl.
      exact (bloop h).
    - intro g.
      rapply equiv_sq_dp^-1.
      apply equiv_sq_path.
      lhs apply (ap (fun y => (bloop h) @ y) (ap_fmap_b f g)).
      rhs apply (ap (fun y => y @ (bloop h)) (ap_fmap_b f g)).
      lhs apply (bloop_pp h (f g))^.
      rhs apply (bloop_pp (f g) h)^.
      apply ap.
      strip_truncations.
      exact (ch _ (grp_image_in f g))^. }
    { cbn beta.
      intros x y.
      rewrite <- path_forall_pp.
      apply ap.
      apply path_forall.
      srapply ClassifyingSpace_ind_hprop.
      exact (bloop_pp x.1 y.1). }
Defined.


(** ** Products of classifying spaces *)

Definition prod_bg_b_grp_prod (G H : Group)
  : B (grp_prod G H) -> B G * B H.
Proof.
  srapply ClassifyingSpace_rec.
  { exact (bbase, bbase). }
  { intros [g h].
    exact (path_prod' (bloop g) (bloop h)). }
  { intros [g1 h1] [g2 h2]; cbn.
    by rewrite <- path_prod_pp, 2 bloop_pp. }
Defined.

Definition b_grp_prod_prod_bg (G H : Group)
  : B G * B H -> B (grp_prod G H).
Proof.
  apply uncurry.
  apply (fmap11_B grp_prod_inl grp_prod_inr).
  intros g h; cbn.
  by rewrite 2 grp_unit_l, 2 grp_unit_r.
Defined.

Definition equiv1 (G H : Group)
  : (b_grp_prod_prod_bg G H) o (prod_bg_b_grp_prod G H) == idmap.
Proof.
  srapply ClassifyingSpace_ind_hset.
  - reflexivity.
  - intros [g h].
    unfold DPath.
    transport_paths FFlr.
    apply equiv_p1_1q.
    rewrite ClassifyingSpace_rec_beta_bloop.
    unfold b_grp_prod_prod_bg.
    lhs napply (ap_uncurry _ (bloop g) (bloop h)).
    rewrite ap011_is_ap. (* Try lhs? *)
    rewrite 2 ClassifyingSpace_rec_beta_bloop.
    cbn.
    lhs_V napply bloop_pp.
    apply ap.
    exact (path_prod' (grp_unit_r _) (grp_unit_l _)).
Defined.

Definition equiv2 (G H : Group)
  : (prod_bg_b_grp_prod G H) o (b_grp_prod_prod_bg G H) == idmap.
Proof.
  intros [x y].
  revert x.
  srapply ClassifyingSpace_ind_hset.
  { revert y.
    cbn beta.
    srapply ClassifyingSpace_ind_hset.
    - reflexivity.
    - intro h.
      unfold DPath.
      transport_paths FFFlFr.
      apply equiv_p1_1q.
      admit. }
  { intro h.
    rapply equiv_sq_dp^-1.
    apply equiv_sq_path.
    admit. }
Admitted.
