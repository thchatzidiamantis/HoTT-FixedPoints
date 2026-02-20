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
Definition issurj_pi0_map_bg_groupreps `{U : Univalence} {G H : Group}
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

(* jdc: Note that [bloop1_pp] was unused, so I dropped it. *)
(* jdc: Also, [G] was not needed either, so I removed it and renamed the arguments. *)
(* jdc: Then I realized that this can be generalized to give a homotopy beween two functions, which gives a more natural statement. I have put this in the main ClassifyingSpace.v file as [ClassifyingSpace_rec_homotopy].  The [p] and [bloop_comm] there are exactly what you'd expect to give a path between the sigma type of the first two arguments (except that you give a homotopy);  the third "_pp" argument is in a proposition so doesn't need to be compared.  Compare this to results containing the string "_homotop" in Colimits/*, for example, where some slightly different design choices are made. So maybe we should drop the _rec_loop version below?  Or keep it, but with a one-liner proof? *)
(* jdc: With the further changes I made below, the _beta_bloop1 and _beta_bloop1' results aren't needed, and therefore _rec_loop is not needed either.  So not sure whether they are worth keeping around. *)
Definition ClassifyingSpace_rec_loop {G : Group}
  (P : Type) `{IsTrunc 1 P} (bbase' : P)
  (bloop' : G -> bbase' = bbase')
  (bloop_pp' : forall x y : G, bloop' (x * y) = bloop' x @ bloop' y)
  (p : bbase' = bbase')
  (bloop_comm : forall h, p @ bloop' h = bloop' h @ p)
  : ClassifyingSpace_rec P bbase' bloop' bloop_pp'
    == ClassifyingSpace_rec P bbase' bloop' bloop_pp'.
Proof.
  srapply ClassifyingSpace_ind_hset; cbn beta.
  - exact p.
  - intro h.
    unfold DPath.
    transport_paths FlFr.
    rewrite ClassifyingSpace_rec_beta_bloop.
    symmetry; apply bloop_comm.
  Restart.
  exact (ClassifyingSpace_rec_homotopy _ _ _ _ _ _ _ p bloop_comm).
Defined.

Definition ClassifyingSpace_rec2_beta_bloop1_bbase {G H : Group}
  (P : Type) `{IsTrunc 1 P} (bbase' : P)
  (bloop1 : G -> bbase' = bbase')
  (bloop1_pp : forall x y : G, bloop1 (x * y) = bloop1 x @ bloop1 y)
  (bloop2 : H -> bbase' = bbase')
  (bloop2_pp : forall x y : H, bloop2 (x * y) = bloop2 x @ bloop2 y)
  (bloop_comm : forall g h, bloop1 g @ bloop2 h = bloop2 h @ bloop1 g)
  (g : G)
  : ap10 (ap (ClassifyingSpace_rec2 P bbase' bloop1 bloop1_pp bloop2 bloop2_pp bloop_comm)
          (bloop g))
      bbase = bloop1 g.
Proof.
  lhs_V napply ap_apply_Fl.
  unfold ClassifyingSpace_rec2, ClassifyingSpace_rec_forall; cbn.
  rapply ClassifyingSpace_rec_beta_bloop.
Defined.

(* jdc: Even though this is no longer needed, I wonder if it's still worth keeping?  Maybe just keep the conclusion in a comment, for future reference? *)
Definition ClassifyingSpace_rec2_beta_bloop1 {G H : Group}
  (P : Type) `{IsTrunc 1 P} (bbase' : P)
  (bloop1 : G -> bbase' = bbase')
  (bloop1_pp : forall x y : G, bloop1 (x * y) = bloop1 x @ bloop1 y)
  (bloop2 : H -> bbase' = bbase')
  (bloop2_pp : forall x y : H, bloop2 (x * y) = bloop2 x @ bloop2 y)
  (bloop_comm : forall g h, bloop1 g @ bloop2 h = bloop2 h @ bloop1 g)
  (g : G)
  : ap10 (ap (ClassifyingSpace_rec2 P bbase' bloop1 bloop1_pp bloop2 bloop2_pp bloop_comm)
          (bloop g))
    == ClassifyingSpace_rec_loop P bbase' bloop2 bloop2_pp (bloop1 g) (bloop_comm g).
Proof.
  rapply ClassifyingSpace_ind_hprop.
  napply ClassifyingSpace_rec2_beta_bloop1_bbase.
Defined.

Definition ClassifyingSpace_rec2_beta_bloop1' `{F : Funext} {G H : Group}
  (P : Type) `{IsTrunc 1 P} (bbase' : P)
  (bloop1 : G -> bbase' = bbase')
  (bloop1_pp : forall x y : G, bloop1 (x * y) = bloop1 x @ bloop1 y)
  (bloop2 : H -> bbase' = bbase')
  (bloop2_pp : forall x y : H, bloop2 (x * y) = bloop2 x @ bloop2 y)
  (bloop_comm : forall g h, bloop1 g @ bloop2 h = bloop2 h @ bloop1 g)
  (g : G)
  : ap (ClassifyingSpace_rec2 P bbase' bloop1 bloop1_pp bloop2 bloop2_pp bloop_comm)
      (bloop g)
    = path_forall _ _
        (ClassifyingSpace_rec_loop P bbase' bloop2 bloop2_pp (bloop1 g) (bloop_comm g)).
Proof.
  apply (moveL_equiv_V (f:=ap10)).
  apply path_forall, ClassifyingSpace_rec2_beta_bloop1.
Defined.

Definition map_bg_b_centralizer_grp_image {G H : Group} (f : G $-> H)
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

Definition loops_map_bg_centralizer_grp_image {G H : Group} (f : G $-> H)
  : subtype_centralizer_subgroup (grp_image f)
      -> loops [B G -> B H, fmap B f]
  := fun x => ap (map_bg_b_centralizer_grp_image f) (bloop x).

Definition pi1_map_bg_centralizer_grp_image {G H : Group} (f : G $-> H)
  : subtype_centralizer_subgroup (grp_image f)
      -> Pi 1 [B G -> B H, fmap B f]
  := tr o (loops_map_bg_centralizer_grp_image f).

Definition ap11_is_ap01_ap10 {A B} {f g : A -> B} (h : g = f) {x y : A} (p : x = y)
  : ap11 h p = ap g p @ ap10 h y.
Proof.
  by path_induction.
Defined.

Definition centralizer_grp_image_pi1_map_bg `{U : Univalence}
  {G H : Group} (f : G $-> H)
  : Pi 1 [B G -> B H, fmap B f]
    -> subtype_centralizer_subgroup (grp_image f).
Proof.
  intro p.
  strip_truncations; change (pointed_fun (fmap B f) = (fmap B f)) in p.
  exists (bloop^-1 (ap10 p bbase)).
  unfold subtype_centralizer_subgroup, subgroup_pred, subtype_centralizer.
  apply tr.
  intros h sh.
  strip_truncations.
  unfold centralizer.
  apply (equiv_inj bloop).
  rewrite 2 bloop_pp.
  rewrite (eisretr bloop (ap10 p bbase)).
  destruct sh as [g []]; clear h.
  rewrite <- ap_fmap_b.
  rhs_V napply (ap11_is_ap10_ap01 p (bloop g)).
  symmetry; napply ap11_is_ap01_ap10.
Defined.

Definition centralizer_grp_image_pi1_map_bg_pi1_map_bg_centralizer_grp_image
  `{U : Univalence} {G H : Group} (f : G $-> H)
  : centralizer_grp_image_pi1_map_bg f o pi1_map_bg_centralizer_grp_image f == idmap.
Proof.
  intros [h ch]; strip_truncations.
  apply path_sigma_hprop; unfold ".1".
  (* The goal is secretly of the form "bloop^-1 foo = h". *)
  apply (moveR_equiv_V (f:=bloop)).
  Time napply ClassifyingSpace_rec2_beta_bloop1_bbase. (* Around 0.1s *)
(* I tried unfolding things and filling in most arguments to ClassifyingSpace_rec2_beta_bloop1, but couldn't figure out a way to make it faster.  0.1s is not that bad, but I thought it would be easy to fix.  I'll leave my attempts here for now, but they can be deleted.
  unfold loops_map_bg_centralizer_grp_image.
  unfold map_bg_b_centralizer_grp_image.
  simpl.
  unfold subgroup_incl.
  simpl.
  unfold fmap11_B.
  simpl.
  Time exact (ClassifyingSpace_rec2_beta_bloop1
                (G:=subtype_centralizer_subgroup (grp_image f))
                (ClassifyingSpace H)
                bbase
                (fun k => bloop k.1)
                (fun g1 g2 : {x : _ &
                                    subtype_centralizer
                                      (fun y : H => Tr (-1) {x0 : G & f x0 = y}) x} =>
                   1 @ bloop_pp g1.1 g2.1)
                (bloop o f)
                (fun x0 y : G => ap bloop (grp_homo_op f x0 y) @ bloop_pp (f x0) (f y))
                (fun
                    (g : {x : _ &
                                subtype_centralizer
                                  (fun y : H => Tr (-1) {x0 : G & f x0 = y}) x})
                    (h0 : G) =>
                    ((bloop_pp g.1 (f h0))^ @ ap bloop
                                              (Trunc_ind
                                                 (fun _ : Trunc (-1) (forall h1 : H, _ -> _) =>
                                                    f h0 * g.1 = g.1 * f h0)
                                                 (fun ch1 : forall h1 : H,
                                                      Tr (-1) {x0 : G & _} ->
                                                      centralizer h1 g.1 =>
                                                    ch1 (f h0) (tr (h0; 1)))
                                                 g.2)^) @ bloop_pp (f h0) g.1)
                (h; tr ch)).
*)
Defined.

Definition pi1_map_bg_centralizer_grp_image_centralizer_grp_image_pi1_map_bg
  `{U : Univalence} {G H : Group} (f : G $-> H)
  : pi1_map_bg_centralizer_grp_image f o centralizer_grp_image_pi1_map_bg f == idmap.
Proof.
  intro u.
  strip_truncations.
  change (pointed_fun (fmap B f) = (fmap B f)) in u.
  unfold pi1_map_bg_centralizer_grp_image.
  apply ap.
  unfold loops_map_bg_centralizer_grp_image.
  apply (equiv_inj ap10).
  apply path_forall.
  rapply ClassifyingSpace_ind_hprop.
  lhs napply ClassifyingSpace_rec2_beta_bloop1_bbase.
  cbn -[isequiv_bloop].
  apply eisretr.
Defined.

Definition isequiv_centralizer_grp_image_pi1_map_bg `{U : Univalence}
  {G H : Group} (f : G $-> H)
  : IsEquiv (centralizer_grp_image_pi1_map_bg f).
Proof.
  srapply isequiv_adjointify.
  - exact (pi1_map_bg_centralizer_grp_image f).
  - exact (centralizer_grp_image_pi1_map_bg_pi1_map_bg_centralizer_grp_image f).
  - exact (pi1_map_bg_centralizer_grp_image_centralizer_grp_image_pi1_map_bg f).
Defined.

Definition equiv_pi1_map_bg_centralizer_grp_image `{U : Univalence}
  {G H : Group} (f : G $-> H)
  : Pi 1 [B G -> B H, fmap B f] <~> subtype_centralizer_subgroup (grp_image f)
  := Build_Equiv _ _ _ (isequiv_centralizer_grp_image_pi1_map_bg f).

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

(* TODO: Write a ClassifyingSpace_ind2_hset and computation rules for ClassifyingSpace_rec2. *)
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
