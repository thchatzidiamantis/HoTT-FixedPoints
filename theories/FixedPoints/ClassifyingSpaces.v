(** * Mapping spaces between classifying spaces *)

From HoTT Require Import Basics Types.
Require Import Universes.HProp Universes.HSet.
Require Import Truncations.Core Truncations.Connectedness Truncations.Constant SeparatedTrunc.
Require Import Algebra.Groups.Group Subgroup Algebra.AbGroups.Centralizer.
Require Import Pointed WildCat WildCat.Core.
Require Import Homotopy.ClassifyingSpace.
Require Import Colimits.Quotient GraphQuotient.
Require Import Cubical.DPath PathSquare.
Require Import FixedPoints.Groups.
Require Import Homotopy.HomotopyGroup.
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

Definition ClassifyingSpace_rec_loop {G : Group}
  (P : Type) `{IsTrunc 1 P} (bbase' : P)
  (bloop' : G -> bbase' = bbase')
  (bloop_pp' : forall x y : G, bloop' (x * y) = bloop' x @ bloop' y)
  (p : bbase' = bbase')
  (bloop_comm : forall h, p @ bloop' h = bloop' h @ p)
  : ClassifyingSpace_rec P bbase' bloop' bloop_pp'
    == ClassifyingSpace_rec P bbase' bloop' bloop_pp'
  := ClassifyingSpace_rec_homotopy _ _ _ _ _ _ _ p bloop_comm.

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

Definition map_bg_b_centralizer_grp_image {G H : Group} (f : G $-> H)
  : B (subtype_centralizer_subgroup (grp_image f)) -> (B G -> B H).
Proof.
  napply (fmap11_B (subgroup_incl _) f).
  intros [h ch] g; cbn.
  symmetry.
  strip_truncations.
  exact (ch (f g) (tr (g; idpath))).
Defined.

Definition loops_map_bg_centralizer_grp_image {G H : Group} (f : G $-> H)
  : subtype_centralizer_subgroup (grp_image f)
      -> loops [B G -> B H, fmap B f]
  := fun x => ap (map_bg_b_centralizer_grp_image f) (bloop x).

Definition pi1_map_bg_centralizer_grp_image {G H : Group} (f : G $-> H)
  : subtype_centralizer_subgroup (grp_image f)
      -> Pi 1 [B G -> B H, fmap B f]
  := tr o (loops_map_bg_centralizer_grp_image f).

Definition encode_test `{ua : Univalence} {G : Group}
  {p q : bbase = bbase}
  : ClassifyingSpace.encode bbase (p @ q)
      = (ClassifyingSpace.encode (G:=G) bbase p)
        * (ClassifyingSpace.encode bbase q).
Proof.
  revert p q.
  equiv_intro (bloop (G:=G)) g1; equiv_intro (bloop (G:=G)) g2.
  unfold ClassifyingSpace.encode.
  rewrite transport_pp.
  rewrite 3 ClassifyingSpace.codes_transport.
  by rewrite 2 grp_unit_l.
Defined.

Definition centralizer_grp_image_pi1_map_bg `{ua : Univalence}
  {G H : Group} (f : G $-> H)
  : Pi 1 [B G -> B H, fmap B f]
    $-> subtype_centralizer_subgroup (grp_image f).
Proof.
  unshelve napply Build_GroupHomomorphism.
  { intro p.
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
    symmetry; napply ap11_is_ap01_ap10. }
  { intros p q; srapply path_sigma_hprop.
    strip_truncations; simpl.
    change (pointed_fun (fmap B f) = fmap B f) in p, q.
    rewrite ap10_pp.
    srapply encode_test. }
Defined.

Definition centralizer_grp_image_pi1_map_bg_pi1_map_bg_centralizer_grp_image
  `{ua : Univalence} {G H : Group} (f : G $-> H)
  : centralizer_grp_image_pi1_map_bg f o pi1_map_bg_centralizer_grp_image f == idmap.
Proof.
  intros [h ch]; strip_truncations.
  apply path_sigma_hprop.
  cbn -[isequiv_bloop].
  apply (moveR_equiv_V (f:=bloop)).
  napply ClassifyingSpace_rec2_beta_bloop1_bbase.
Defined.

Definition pi1_map_bg_centralizer_grp_image_centralizer_grp_image_pi1_map_bg
  `{ua : Univalence} {G H : Group} (f : G $-> H)
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

Definition isequiv_centralizer_grp_image_pi1_map_bg `{ua : Univalence}
  {G H : Group} (f : G $-> H)
  : IsEquiv (centralizer_grp_image_pi1_map_bg f).
Proof.
  srapply isequiv_adjointify.
  - exact (pi1_map_bg_centralizer_grp_image f).
  - exact (centralizer_grp_image_pi1_map_bg_pi1_map_bg_centralizer_grp_image f).
  - exact (pi1_map_bg_centralizer_grp_image_centralizer_grp_image_pi1_map_bg f).
Defined.

Definition iso_pi1_map_bg_centralizer_grp_image `{ua : Univalence}
  {G H : Group} (f : G $-> H)
  : GroupIsomorphism
    (Pi 1 [B G -> B H, fmap B f])
    (subtype_centralizer_subgroup (grp_image f))
  := Build_GroupIsomorphism _ _ _ (isequiv_centralizer_grp_image_pi1_map_bg f).

Definition natequiv_bg_pi1_adjoint' `{Univalence} (X : pType) `{IsConnected 0 X}
  : NatEquiv (opyon (Pi1 X)) (opyon X o B).
Proof.
  refine (natequiv_compose _ (natequiv_grp_homo_pmap_bg _)).
  refine (natequiv_compose (G := opyon (pTr 1 X) o B) _ _).
  { snapply Build_NatEquiv.
    1: intro; exact pequiv_ptr_rec.
    exact (is1natural_prewhisker (G:=opyon X) B (opyoneda _ _ _)). }
  { refine (natequiv_prewhisker _ _).
    refine (natequiv_opyon_equiv _^-1$).
    refine (pequiv_pclassifyingspace_pi1 (pTr 1 X) o*E (emap B _)).
    exact (grp_iso_pi_Tr 0 X). }
Defined.

Definition equiv_bg_pi1_adjoint' `{Univalence}
  (X : pType) `{IsConnected 0 X} (G : Group)
  : (Pi 1 X $-> G) <~> (X ->* B G).
Proof.
  rapply natequiv_bg_pi1_adjoint'.
Defined.

Definition natequiv_map_bg `{Univalence}
  (X : pType) `{IsConnected 0 X}
  : NatEquiv (opyon (A:=Type) (B (Pi 1 X)) o B) (opyon (A:=Type) X o B).
Proof.
  unfold opyon.
  refine (natequiv_compose (G := opyon (Tr 1 X) o B) _ _).
  { snapply Build_NatEquiv.
    1: intro; rapply (equiv_o_to_O (Tr 1) X).
    by srapply Build_Is1Natural. }
  { refine (natequiv_prewhisker _ _).
    refine (natequiv_opyon_equiv _^-1$).
    refine (pequiv_pclassifyingspace_pi1 (pTr 1 X) o*E (emap B _)).
    exact (grp_iso_pi_Tr 0 X). }
Defined.

Definition equiv_map_bg `{Univalence}
  (X : pType) `{IsConnected 0 X} (G : Group)
  : (B (Pi 1 X) -> B G) <~> (X -> B G).
Proof.
  rapply natequiv_map_bg.
Defined.

(* tcc: this takes almost 5 seconds. If I change it to 
Proof.
  reflexivity.
Defined.
it takes less than 0.2 seconds (still a bit longer than most other proofs in this file). What is the difference? *)
Time Definition equiv_map_bg_pointed `{Univalence}
  (X : pType) `{IsConnected 0 X} (G : Group) (f : Pi 1 X $-> G)
  : equiv_map_bg X G (fmap B f) = equiv_bg_pi1_adjoint' X G f
  := @idpath (X -> B G) (equiv_bg_pi1_adjoint' X G f). (* 0.09s on my system *)
(*
  := @idpath (X -> B G) (equiv_map_bg X G (fmap B f)). (* 4.2s *)
  := idpath _.  (* 3.7s *)
*)

Time Definition equiv_map_bg_pointed' `{Univalence}
  (X : pType) `{IsConnected 0 X} (G : Group) (f : Pi 1 X $-> G)
  : (equiv_map_bg X G (fmap B f)) = (equiv_bg_pi1_adjoint' X G f).
Proof.
(*
  Time apply idpath. (* 0.1s, but then Defined takes 0.9s. *)
  Time exact idpath. (* 2.7s plus 0.9s for Defined, roughly matching the := idpath approach. *)
*)
  Time reflexivity. (* 0.1s, and Defined is only 0.07s. Quite fast, but not as fast as first := method. *)
Time Defined. (* Varies, depending on body of proof. *)
Set Printing Implicit.
Unset Printing Notations.
Print equiv_map_bg_pointed'. (* This is how I generated the fast := line. *)
(* I don't understand why these various methods are so different.  I would just keep the fast := version, and add a comment that the speed for this is sensitive to the exact form of the proof, and that this form was chosen because it is fast. *)

(* TODO: make sure it computes well on pointed maps. *)
Definition pi0_map_bg_groupreps_pi1 `{Univalence}
  (X : pType) (G : Group) `{IsConnected 0 X}
  : groupreps (Pi 1 X) G <~> Tr 0 (X -> B G).
Proof.
  refine (Trunc_functor_equiv 0 (equiv_map_bg X G) oE _).
  srapply equiv_groupreps_pi0_map_bg.
Defined.

Definition pi1_map_bg_groupreps_pi1 `{Univalence}
  (X : pType) (G : Group) `{IsConnected 0 X} (f : Pi 1 X $-> G)
  : GroupIsomorphism
      (Pi 1 [(X -> B G), equiv_bg_pi1_adjoint' X G f])
      (subtype_centralizer_subgroup (grp_image f)).
Proof.
  refine (grp_iso_compose (iso_pi1_map_bg_centralizer_grp_image f) _).
  srapply groupiso_pi_functor.
  symmetry.
  srapply Build_pEquiv'.
  - exact (equiv_map_bg X G).
  - unfold "pt".
    unfold ispointed_type.
    reflexivity.
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

(* TODO: Write a ClassifyingSpace_ind2_hset. *)
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
