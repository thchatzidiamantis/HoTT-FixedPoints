(** * Types for which self-maps have fixed points *)

From HoTT Require Import Basics Types.
Require Import Algebra.Groups.Group Subgroup Algebra.AbGroups.Centralizer.
Require Import Homotopy.ClassifyingSpace HomotopyGroup WhiteheadsPrinciple.
Require Import Pointed WildCat WildCat.Core.
Require Import Circle.
Require Import Suspension.
Require Import Truncations.Core Truncations.Connectedness Truncations.Constant.
Require Import Universes.TruncType.
(* Results from Truncations.Constant might be useful as this progresses. *)
Require Import HSpace.Core Pointed.Core.
Require Import Colimits.Pushout Quotient.
Require Import Cubical.DPath PathSquare.
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

(** ** Basic definitions *)

(* This is the strongest possible notion. *)
Definition HasFixedPoints (A : Type) := forall (f : A -> A), FixedBy f.

(* Should coincide with [HasMereIndexedFixedPoints] for idmap. *)
Definition HasMereFixedPoints (A : Type)
  := forall (f : A -> A), merely (FixedBy f).

Definition HasFamilyFixedPoints {X A : Type} (F : X -> A -> A)
  := forall x : X, FixedBy (F x).

Definition MerelyHasIndexedFixedPoints (X A : Type)
  := merely (forall (C : X -> A -> A), HasFamilyFixedPoints C).

(* Is this equivalent to also having a [merely] inside [HasFamilyFixedPoints]? *)
Definition HasMereIndexedFixedPoints (X A : Type)
  := forall C : X -> A -> A, merely (HasFamilyFixedPoints C).

Definition HasIndexedFixedPoints (X A : Type)
  := forall (C : X -> A -> A), HasFamilyFixedPoints C.

Definition hasindexedfixedpoints_hasfixedpoints {X A : Type}
  (fp_A : HasFixedPoints A)
  : HasIndexedFixedPoints X A
  := fun C x => (fp_A (C x)).

Definition hasfixedpoints_hasindexedfixedpoints_ptype {X : pType} {A : Type}
  (ifp : HasIndexedFixedPoints X A)
  : HasFixedPoints A
  := fun f => ifp (fun _ => f) (point X).

Definition test1 {X A : Type} (mX : merely X)
  (ifp : MerelyHasIndexedFixedPoints X A)
  : merely (HasFixedPoints A).
Proof.
  strip_truncations.
  apply tr.
  unshelve refine (hasfixedpoints_hasindexedfixedpoints_ptype _).
  - snapply Build_pType.
    + exact X.
    + exact mX.
  - exact ifp.
Defined.

Definition test2 {X A : Type} (mX : merely X)
  (mifp : HasMereIndexedFixedPoints X A)
  : HasMereFixedPoints A.
Proof.
  intro f.
  specialize (mifp (fun _ => f)).
  strip_truncations.
  apply tr.
  exact (mifp mX).
Defined.

Definition hasfixedpoints_hasfamilyfixedpoints_idmap {A : Type}
  (fp : HasFamilyFixedPoints (idmap : (A -> A) -> (A -> A)))
  : HasFixedPoints A
  := fun f => fp f.

(** ** Examples *)

Definition hasfixedpoints_contr {A : Type} (c : Contr A)
  : HasFixedPoints A
  := fun f => (center A; (contr (f (center A)))^).

Definition test {A : Type} (P : A -> Type) (s : {a : A & merely (P a)})
  : merely (sig P).
Proof.
  destruct s as [a p].
  strip_truncations.
  exact (tr (a; p)).
Defined.

Definition hasmerelyfixedpoints_connected `{Univalence} (A : pType)
  `{IsConnected 0 A}
  : forall f : A -> A, {a : A & merely (f a = a)}
  := fun f => (point A; merely_path_is0connected A (f (point A)) (point A)).

Definition hasmerelyfixedpoints_hasmerefixedpoints {A : Type}
  (fp : forall f : A -> A, {a : A & merely (f a = a)})
  : HasMereFixedPoints A
  := fun f => test _ (fp f).

Definition hasmerefixedpoints_connected `{Univalence} {A : Type}
  `{mA : merely A} `{IsConnected 0 A}
  : HasMereFixedPoints A.
Proof.
  intro f.
  strip_truncations.
  pose (r := merely_path_is0connected A (f mA) mA).
  (* There has got to be a simpler way to do this. *)
  exact (test _ (mA; r)).
Defined.

Definition pointed_hasfixedpoints {A : Type} (F : HasFixedPoints A) : A
  := (F idmap).1.

Definition nofixedpoints_bool : ~ (HasFixedPoints Bool).
Proof.
  intro F.
  destruct (F negb) as [a pa]; induction a.
  1,2: by apply false_ne_true.
Defined.

(** A homogeneous space with the fixed-point property must be contractible.  Since every left- or right-invertible H-space is homogeneous, this covers those situations as well. *)
Definition contr_hasfixedpoints_homogeneous {A : pType} `{IsHomogeneous A}
  (fp : HasFixedPoints A)
  : Contr A.
Proof.
  srapply (Build_Contr A (point A)).
  intro y.
  destruct (fp (fun z => ishomogeneous z y)) as [a pa].
  (* [ishomogeneous a] is a self-equivalence sending [pt] to [a]. *)
  apply (equiv_inj (ishomogeneous a)).
  rhs apply pa.
  apply (dpoint_eq (ishomogeneous a)).
Defined.

(** We shouldn't need to state either of the next two results explicitly, but due to the issue mentioned below with typeclass search, we have to do so. *)
Definition contr_hasfixedpoints_left_inv_hspace {A : pType} `{IsHSpace A}
  (linv : forall (a : A), IsEquiv (a *.))
  (fp : HasFixedPoints A)
  : Contr A.
Proof.
  rapply (contr_hasfixedpoints_homogeneous fp).
  (* For some reason, [linv] isn't found during typeclass search in the previous line, so we need the next line, which *does* find [linv] during typeclass search! *)
  rapply ishomogeneous_hspace_linv.
Defined.

Definition contr_hasfixedpoints_right_inv_hspace {A : pType} `{IsHSpace A}
  (rinv : forall (a : A), IsEquiv (.* a))
  (fp : HasFixedPoints A)
  : Contr A.
Proof.
  rapply (contr_hasfixedpoints_homogeneous fp).
  rapply ishomogeneous_hspace_rinv.
Defined.

Definition connected_ptype_merely_const `{ua : Univalence}
  (X : pType) `{IsConnected 0 X}
  : X -> {f : X -> X & merely (f = (fun _ => pt))}.
Proof.
  intro x.
  exists (fun _ => x).
  pose proof (p := merely_path_is0connected X x pt).
  strip_truncations; apply tr.
  exact (ap (fun k => (fun _ => k)) p).
Defined.

Definition component_retr `{ua : Univalence}
  {X : pType} `{IsConnected 0 X}
  : (fun F => F.1 pt) o (connected_ptype_merely_const X) == idmap
  := fun _ => idpath.

Definition help0 `{ua : Univalence}
  (X : pType) `{IsConnected 0 X}
  : (hfiber (connected_ptype_merely_const X) (fun _ => pt; tr idpath))
    <~> {x : X & (fun _ => x) = (fun _ : X => pt)}.
Proof.
  srapply equiv_functor_sigma_id.
  intro x; symmetry.
  exact (equiv_path_sigma_hprop (connected_ptype_merely_const X pt)
                                (fun _ => pt; tr idpath)).
Defined.

Definition help1 `{ua : Univalence}
  (X : pType) `{IsConnected 0 X}
  : (hfiber (connected_ptype_merely_const X) (fun _ => pt; tr idpath))
    <~> {x : X & X -> x = pt}.
Proof.
  refine (_ oE help0 X).
  srapply (equiv_functor_sigma' equiv_idmap).
  intro x; simpl.
  symmetry; apply equiv_path_forall.
Defined.

Definition help2 `{ua : Univalence}
  (X : pType) `{IsConnected 0 X}
  : (hfiber (connected_ptype_merely_const X) (fun _ => pt; tr idpath))
    <~> {u : {y : X & y = pt} & {h : X -> (u.1 = pt) & h pt = u.2}}.
Proof.
  refine (_ oE help1 X).
  make_equiv_contr_basedpaths.
Defined.

Definition help3 `{ua : Univalence}
  (X : pType) `{IsConnected 0 X}
  : (hfiber (connected_ptype_merely_const X) (fun _ => pt; tr idpath))
    <~> {h : X -> (point X = pt) & h pt = idpath}
  := equiv_contr_sigma _ oE help2 X.

Definition help4 `{ua : Univalence}
  (X : pType) `{IsConnected 0 X}
  : (hfiber (connected_ptype_merely_const X) (fun _ => pt; tr idpath))
    <~> (X ->* loops X).
Proof.
  refine (_ oE help3 X).
  issig.
Defined.

Instance isequiv_connected_ptype_merely_const `{ua : Univalence}
  {X : pType} `{IsConnected 0 X} (c : Contr (X ->* loops X))
  : IsEquiv (connected_ptype_merely_const X).
Proof.
  apply isequiv_contr_map.
  srapply (@conn_point_elim ua (-1) [_, (fun _ => pt; tr idpath)]).
  apply (contr_equiv' _ (help4 X)^-1).
Defined.

(* jdc: You can write [pconst] for [fun _ => pt].  Technically, this is the *pointed* function [fun _ => pt], so maybe it's better to write [const pt], so there is no confusion. *)
Definition fixedby_comp_constant_contr_pfun_loops `{ua : Univalence}
  {X : pType} `{IsConnected 0 X} (c : Contr (X ->* loops X)) {f : X -> X}
  (p : merely (f = const pt))
  : FixedBy f.
Proof.
  (* jdc: This illustrates how useful equiv_intro is. *)
  revert f p; apply equiv_sig_ind'.
  equiv_intro (connected_ptype_merely_const X) x; cbn.
  exact (x; idpath).
Defined.

Definition component_equiv_cor `{ua : Univalence}
  {X : pType} `{IsConnected 0 X} (c : Contr (X ->* loops X)) {f : X -> X}
  (p : merely (f = (fun _ => pt)))
  : f == (fun _ => f pt).
Proof.
  revert f p; apply equiv_sig_ind'.
  equiv_intro (connected_ptype_merely_const X) x; cbn.
  reflexivity.
Defined.

Definition component_equiv' `{ua : Univalence}
  {X : pType} `{IsConnected 0 X} (e : IsEquiv (connected_ptype_merely_const X))
  : Contr (X ->* loops X).
Proof.
  apply contr_map_isequiv in e.
  apply (contr_equiv' _ (help4 X)).
Defined.

Definition contr_trivial_pin {ua : Univalence} {A : pType}
  (n : trunc_index) {H0 : IsTrunc n A}
  (c : forall (x : A) (k : nat), Contr (Pi k [A, x]))
  : Contr A.
Proof.
  srapply (contr_equiv Unit (B:=A) (fun _ => ispointed_type A)).
  rapply (whiteheads_principle n).
  - admit.
  - rapply isequiv_contr_contr.
    exact (c pt (0 : nat)).
  - intros x k.
    rapply isequiv_contr_contr.
    + admit.
    + exact (c pt (k.+1 : nat)).
Admitted.

Definition pi1helper {A : Type} (a b : A) (p : merely (a = b))
  : merely (pointed_type (Pi 1 [A, a]) = Pi 1 [A, b]).
Proof.
  strip_truncations; apply tr.
  by rewrite p.
Defined.

(* Note that we can prove that [f] is merely pointed since the goal is an HProp. *)
Definition contr_pi1_merely_pointed_equiv_weird_group `{U : Univalence}
  {G : Group} (f : B G -> B G) (v : G $<~> G) (mfv : merely (f = fmap B v))
  (centr : forall u : G $-> G,
            IsEquiv u -> Contr (subtype_centralizer_subgroup (grp_image u)))
  : Contr (Pi 1 [B G -> B G, f]).
Proof.
  strip_truncations.
  rewrite mfv.
  exact (contr_equiv' _ (equiv_pi1_map_bg_to_centralizer_group_image v)^-1).
Defined.

Definition contr_componenet_merely_pointed_equiv_weird_group `{U : Univalence}
  {G : Group} (f : B G -> B G) (v : G $<~> G) (mfv : merely (f = fmap B v))
  (centr : forall u : G $-> G,
            IsEquiv u -> Contr (subtype_centralizer_subgroup (grp_image u)))
  : Contr {s : B G -> B G & merely (s = f)}.
Proof.
  pose proof (cpi1 := contr_pi1_merely_pointed_equiv_weird_group _ _ mfv centr).
  srapply (@contr_trivial_pin U [{s : B G -> B G & merely (s = f)}, (f; tr idpath)] 2).
  intros x k; cbn in x.
  (* admitted this for now but it's definitely true. *)
  (* TODO: use match with 0, 1 and [n.+1] *)
  admit.
Admitted.

Definition fixedby_merely_pointed_equiv_weird_group `{U : Univalence}
  (* The problem here is actually getting a representative for v. Should be fine if G is a finite group. *)
  {G : Group} (f : B G -> B G) (v : G $<~> G) (mfv : merely (f = fmap B v))
  (centr : forall u : G $-> G,
            IsEquiv u -> Contr (subtype_centralizer_subgroup (grp_image u)))
  : FixedBy f.
Proof.
  pose proof (c := contr_componenet_merely_pointed_equiv_weird_group _ _ mfv centr).
  assert (mfv' : merely (pointed_fun (fmap B v) = f)).
  { strip_truncations; exact (tr mfv^). }
  assert (p : f = fmap B v).
  { pose proof (t := path_contr (A:={s : B G -> B G & merely (s = f)})
                      (f; tr idpath)).
    specialize (t (pointed_fun (fmap B v); mfv')).
    exact (ap pr1 t). }
  rewrite p.
  exact (bbase; idpath).
Admitted.

(** ** Retracts *)

(** This maybe has a converse based on surjections? *)
Definition hasfamilyfixedpoints_comp {X A Y : Type} {C : X -> A -> A}
(* Order of assumptions here might not be optimal. *)
  (fp_C : HasFamilyFixedPoints C) (g : Y -> X)
  : HasFamilyFixedPoints (C o g)
  := fun x => (fp_C (g x)).

Definition hasfixedpoints_retract {A R : Type} {f : A -> R} {g : R -> A}
  (s : f o g == idmap) (fp_A : HasFixedPoints A)
  : HasFixedPoints R.
Proof.
  intro h.
  destruct (fp_A (g o h o f)) as [a p].
  exists (f a).
  exact ((s _)^ @ ap f p).
Defined.

Definition hasmereindexedfixedpoints_retract_1 {X A R : Type}
  {f : A -> R} {g : R -> A} (s : f o g == idmap)
  (fp_XA : HasMereIndexedFixedPoints X A)
  : HasMereIndexedFixedPoints X R.
Proof.
  intro C.
  specialize (fp_XA (fun x => g o (C x) o f)); strip_truncations.
  apply tr.
  intro x.
  exists (f (fp_XA x).1).
  exact ((s _)^ @ ap f (fp_XA x).2).
Defined.

Definition hasmereindexedfixedpoints_retract_2 {X Y A : Type}
  {f : X -> Y} {g : Y -> X} (s : f o g == idmap)
  (fp_XA : HasMereIndexedFixedPoints X A)
  : HasMereIndexedFixedPoints Y A.
Proof.
  intro C.
  specialize (fp_XA (fun x => C (f x))); strip_truncations.
  apply tr.
  intro y.
  exists  (fp_XA (g y)).1.
  refine ((apD10 (ap C (s _)) _)^ @ (fp_XA (g y)).2).
Defined.

Definition hasindexedmerefixedpoints_surjection {X Y A : Type}
  {f : X -> Y} (s : IsSurjection f)
  (fp_XA : HasMereIndexedFixedPoints X A)
  : forall C : Y -> A -> A, forall y : Y, merely (FixedBy (C y)).
Proof.
  intros C.
  apply (conn_map_elim (-1) f _).
  intro x.
  specialize (fp_XA (fun x => C (f x))); strip_truncations.
  exact (tr (fp_XA x)).
Defined.

(* Maybe use the thing above to prove this. *)
Definition hasmerefixedpoints_retract {A R : Type} {f : A -> R} {g : R -> A}
  (s : f o g == idmap) (fp_A : HasMereFixedPoints A)
  : HasMereFixedPoints R.
Proof.
  intro h.
  pose (fp := fp_A (g o h o f)); generalize fp.
  intro fp'; strip_truncations.
  apply test.
  exists (f fp'.1).
  exact (tr ((s _)^ @ ap f fp'.2)).
Defined.

(* Actually a logical equivalence by the work above. *)
Definition hasfamilyfixedpoints_section {X A R : Type}
(* Order of assumptions and naming here not optimal. *)
  {f : A -> R} {g : R -> A} {C : X -> R -> R}
  (s : f o g == idmap) (fp_C : HasFamilyFixedPoints C)
  : HasFamilyFixedPoints (fun x => g o (C x) o f).
Proof.
  intro x.
  destruct (fp_C x) as [a p].
  exists (g a).
  exact (ap g (ap (C x) (s a) @ p)).
Defined.

(** ** Products *)

Definition hasfixedpoints_hasfixedpoints_prod {A B : Type}
  (fp_AB : HasFixedPoints (A * B))
  : HasFixedPoints A.
Proof.
  by rapply (hasfixedpoints_retract
              (f:=fst) (g:=fun x => (x, snd (fp_AB idmap).1)) _ fp_AB).
Defined.

(* Can I also reproduce this as an instance of retracts? *)
Definition hasmerefixedpoints_hasmerefixedpoints_prod {A B : Type}
  (fp_AB : HasMereFixedPoints (A * B))
  : HasMereFixedPoints A.
Proof.
  intro f.
  specialize (fp_AB (fun ab => (f (fst ab), snd ab))).
  strip_truncations; apply tr.
  exists (fst (fp_AB).1).
  exact (ap fst (fp_AB.2)).
Defined.

Definition hasmereindexedfixedpoints_hasmereindexedfixedpoints_prod_1
  {X A B : Type} (fp_AB : HasMereIndexedFixedPoints X (A * B))
  : HasMereIndexedFixedPoints X A.
Proof.
  intro C.
  (* Is it worth recording this for a single family? *)
  specialize (fp_AB (fun x => fun ab => (C x (fst ab), snd ab))).
  strip_truncations; apply tr.
  intro x.
  exists (fst (fp_AB x).1).
  exact (ap fst (fp_AB x).2).
Defined.

Definition hasmereindexedfixedpoints_hasmereindexedfixedpoints_prod_2
  {X A Y : Type} {mY : merely Y} (fp_AB : HasMereIndexedFixedPoints (X * Y) A)
  : HasMereIndexedFixedPoints X A.
Proof.
  intro C.
  (* Is it worth recording this for a single family? *)
  specialize (fp_AB (fun xy => fun a => C (fst xy) a)).
  strip_truncations; apply tr.
  intro x.
  exact (fp_AB (x, mY)).
Defined.

Definition prod_help1 {A B : Type} (f : A * B -> A * B) (b : B)
  : A -> A
  := fun x => fst (f (x, b)).

Definition prod_help2 {A B : Type} (f : A * B -> A * B) (a : A)
  : B -> B
  := fun y => snd (f (a, y)).

Definition hasfixedpoints_prod_hasfixedpoints {A B : Type}
  (fp_A : HasFixedPoints A) (fp_B : HasFixedPoints B)
  : HasFixedPoints (A * B).
Proof.
  intro f.
  destruct (fp_A (fun x => prod_help1 f (fp_B (prod_help2 f x)).1 x)) as [a p].
  destruct (fp_B (prod_help2 f a)) as [b q]; cbn in p.
  exists (a, b).
  exact (path_prod (f (a, b)) (a, b) p q).
Defined.

(* I wonder if I could recreate a counterexample to this. Again, would be true with the [merely] inside the FixedBy (see below). Is that a sensible definition? *)
Definition prod_test_converse'2 {A B : Type}
  (fp_A : HasMereFixedPoints A) (fp_B : HasMereFixedPoints B)
  : HasMereFixedPoints (A * B).
Admitted.

Definition prod_test_converse' {A B : Type}
  (fp_A : forall f : A -> A, {a : A & merely (f a = a)})
  (fp_B : forall g : B -> B, {b : B & merely (g b = b)})
  : forall h : A * B -> A * B, {ab : A * B & merely (h ab = ab)}.
Proof.
  intro h.
  destruct (fp_A (fun x => prod_help1 h (fp_B (prod_help2 h x)).1 x)) as [a p].
  destruct (fp_B (prod_help2 h a)) as [b q]; cbn in p.
  exists (a, b).
  strip_truncations; apply tr.
  exact (path_prod (h (a, b)) (a, b) p q).
Defined.

(** ** The total space of all fixed points *)

Definition Fixpoints (A : Type) := {f : A -> A & FixedBy f}.

Definition fixpoints_base (A : Type) : A -> Fixpoints A
  := fun a => (idmap; (a; idpath)).

Definition isretr_base_fixpoints (A : Type)
  : (fun fp => fp.2.1) o fixpoints_base A == idmap
  := fun _ => idpath.

Definition what {A : Type} (fp_A : HasFixedPoints A)
  : (A -> A) -> Fixpoints A
  := fun f => (f; (fp_A f)).

Definition issect_what {A : Type} (fp_A : HasFixedPoints A)
  : pr1 o what fp_A == idmap
  := fun _ => idpath.

(** ** Lawvere's fixed point theorem *)

Definition lawvere_fp {A B : Type} (F : A -> (A -> B))
  (s : forall h : A -> B, {a : A & F a = h})
  : HasFixedPoints B.
Proof.
  intro g.
  pose (k := fun (x : A) => g (F x x)).
  exists (F (s k).1 (s k).1).
  exact (ap10 (s k).2 (s k).1)^.
Defined.

(** ** Consequences of the fixed point property *)

Definition helper_function {A : Type} (f : A -> Bool) (x y : A) : A -> A.
Proof.
  intro a.
    destruct (decidable_paths_bool (f a) (f y)) as [r | s].
    - exact x.
    - exact y.
Defined.

Definition constant_hasmerefixedpoints {A : Type}
  (fp_A : HasMereFixedPoints A) (f : A -> Bool)
  : forall x y, f x = f y.
Proof.
  intros x y.
  pose (g := helper_function f x y).
  specialize (fp_A g).
  strip_truncations.
  (* Since this term will come up later in the proof, we remember it. *)
  remember (decidable_paths_bool (f fp_A.1) (f y)) as d eqn:e.
  destruct d as [r | s].
  - refine (_ @ r).
    apply ap.
    rewrite fp_A.2^.
    unfold g, helper_function.
    by rewrite e.
  - contradiction s.
    apply ap.
    rewrite fp_A.2^.
    unfold g, helper_function.
    by rewrite e.
Defined.

Definition decpaths_helper_function {A : Type} (x y : A)
  (dx : forall a : A, Decidable (x = a))
  : A -> A.
Proof.
  intro a.
  exact (if (dx a) then y else x).
Defined.

Definition contr_hasfixedpoints_decpaths {A : Type}
  (fp : HasFixedPoints A) {x : A} (dx : forall a : A, Decidable (x = a))
  : Contr A.
Proof.
  snapply Build_Contr.
  1: exact x.
  intros y.
  destruct (fp (decpaths_helper_function x y dx)) as [a p].
  unfold decpaths_helper_function in p.
  destruct (dx a) as [r | s].
  - exact (r @ p^).
  - contradiction s.
Defined.
