From HoTT Require Import Basics Types.
Require Import Truncations.Core Truncations.Connectedness.
Require Import Pointed.Core.
Require Import Universes.TruncType Universes.HProp.
Require Import Misc.CompactTypes.
Require Import ExcludedMiddle Projective.

Local Open Scope trunc_scope.
Local Open Scope path_scope.
Local Open Scope type_scope.

(** * More on decidable types, compact types, and LEM *)

(* TODO:
[done] Stable A → split support A.
[done] LEM → (∀ A, merely split support A).
- What do we know about the converse? Look at Kraus-Escardó-Coquand-Altenkirch, Notions of Anonymous Existence in Martin-Löf Type Theory, section 7.
- Connect whatever I have to "populated types" from the paper above.
[trivial using the other things] All types merely Σ-compact → LEM.
[done] AC → All types merely Σ-compact.
- How much weaker than AC is it (if at all)?
- Connect to collapsible types (see [splitsupp_collapsible, merely_rec_hset]).
[done, yes it's equivalent to WLEM] Is "all types are Π-compact" strictly weaker than LEM?
[done] Define "stable-compact" types.
- Are stable-compact types closed under Σ/Π/coproducts/retracts/images?.
- Split-support-compact types?
[done] (¬Σ)-compact is equivalent to Π-compact. So is (¬Π)-compact.
- Get rid of funext wherever possible.
 *)

(** HoTT book, exercise 7.7(i) (stated as LEM <-> all types merely decidable, but it is also true on the level of individual types). *)
Definition merely_decidable_decidable_merely `{Funext} (A : Type)
  (d : Decidable (merely A))
  : merely (Decidable A).
Proof.
  destruct d as [a|f].
  1: strip_truncations.
  all: apply tr.
  1: exact (inl a).
  exact (inr (fun x => f (tr x))).
Defined.

Definition decidable_merely_merely_decidable `{Funext} (A : Type)
  (md : merely (Decidable A))
  : Decidable (merely A).
Proof.
  strip_truncations.
  rapply decidable_trunc_decidable.
Defined.

(** I don't think the converse is true. *)
Definition stable_merely_merely_stable `{Funext} (A : Type)
  (ms : merely (Stable A))
  : Stable (merely A).
Proof.
  strip_truncations.
  intro x.
  apply tr, ms.
  exact (fun f => x (fun ma => Trunc_rec f ma)).
Defined.

Definition not_not_merely {A : Type} (m : merely A) : ~~A
  := fun f => Trunc_rec (fun a => f a) m.

Definition splitsupp_stable {A : Type} (s : Stable A)
  : merely A -> A
  := s o not_not_merely.
(* Corollary: assuming LEM and Funext, all types are merely stable (by [stable_decidable] and [merely_decidable_decidable_merely]) so all types have merely split support. *)

(** AC_{oo,-1} implies that every type is merely Σ-compact. AC_{0,-1} should imply that every set is merely Σ-compact. *)

(* Note that this also needs LEM, so we need Diaconescu-Goodman-Myhill *)
Definition merely_issigmacompact_choice `{Univalence} `{ExcludedMiddle}
  {ac : forall X, IsHSet X -> HasChoice X} (A : Type)
  : merely (IsSigmaCompactProps A).
Proof.
  rapply ac.
  intro P.
  rapply ac.
  intro d.
  apply merely_decidable_decidable_merely.
  rapply LEM.
Defined.

(** * Other compactness-style definitions *)

(** ** ∃-compactness *)

Definition IsHExistsCompact (A : Type)
  := forall P : A -> Type,
      (forall a : A, Decidable (P a)) -> Decidable (hexists P).

Definition ishprop_ishexistscompact `{Funext} (A : Type)
  : IsHProp (IsHExistsCompact A) := _.

Definition ishexistscompact_issigmacompact `{Funext} {A}
  (c : merely (IsSigmaCompact A))
  : IsHExistsCompact A.
Proof.
  strip_truncations.
  intros P dP.
  destruct (c P dP) as [l|r].
  - left; exact (tr l).
  - right; intros u; by strip_truncations.
Defined.

(** ** More on Π-compactness *)

(** Everything up to and including [decidable_not_ispicompactprops] is in TypeTopology. *)

Definition IsPiCompactProps (A : Type)
  := forall P : A -> HProp,
      (forall a, Decidable (P a)) -> Decidable (forall a, P a).

Definition ishprop_ispicompactprops `{Funext} (A : Type)
  : IsHProp (IsPiCompactProps A) := _.

Definition ispicompactprops_ispicompact {A} (h : IsPiCompact A)
  : IsPiCompactProps A := h.

Definition ispicompcat_ispicompactprops {A} (h : IsPiCompactProps A)
  : IsPiCompact A.
Proof.
  intros P dP.
  refine (decidable_iff _ (h (merely o P) _)); constructor.
  2: exact (fun f a => tr (f a)).
  intros f a.
  apply merely_inhabited_iff_inhabited_stable; exact (f a).
Defined.

Definition ispicompactprops_ishexistscompact `{Funext} {A}
  (c : IsHExistsCompact A)
  : IsPiCompactProps A.
Proof.
  intros P dP.
  destruct (c (not o P) _) as [l|r].
  - right; strip_truncations.
    exact (fun f => l.2 (f l.1)).
  - left; intro a.
    apply (stable_decidable (P a)).
    exact (fun u => r (tr (a; u))).
Defined.

Definition decidable_not_ispicompactprops {A}
  (h : IsPiCompactProps A)
  : Decidable (~A)
  := h (const False_hp) _.

(* The converse to this is called "double-negation shift" and is equivalent to ¬¬LEM. *)
Definition forall_not_not_not_not_forall {A} (P : A -> Type)
  (u : ~~(forall a, P a))
  : forall a, ~~(P a).
Proof.
  intros a n.
  apply u; intro f.
  exact (n (f a)).
Defined.

Definition stable_forall {A} (P : A -> Type) (s : forall a, Stable (P a))
  : Stable (forall a, P a)
  := (functor_forall idmap s o forall_not_not_not_not_forall P).

Definition ispicompactprops_alltype_wlem (wlem : forall X, Decidable (~X))
  (A : Type)
  : IsPiCompactProps A.
Proof.
  intros P dP.
  destruct (wlem (forall a, P a)) as [l|r].
  1: right; exact l.
  left; exact (stable_forall _ _ r).
Defined.

(* Adding a negation to the Σ-type gives an equivalent definition to Π-compact. *)
Definition IsNCompact (A : Type)
  := forall P : A -> HProp,
      (forall a, Decidable (P a)) -> Decidable (~(sig P)).

(* I'm guessing this is already in this library. *)
Definition pi_not_iff_not_sigma {A} (P : A -> Type)
  (dP : forall a, Decidable (P a))
  : (forall a, ~(P a)) <-> ~(sig P).
Proof.
  constructor.
  { intros f [x u].
    exact (f x u). }
  { intros f a u.
    exact (f (a; u)). }
Defined.

Definition ispicompactprops_iff_isnncompact `{Funext} (A : Type)
  : (IsNCompact A) <-> (IsPiCompactProps A).
Proof.
  constructor.
  1,2: intros c P dP.
  1: destruct (c (Negation_hp o P) _) as [l|r].
  - left; refine (fun a => (stable_decidable (P a)) _).
    intro n; exact (l (a; n)).
  - right; intro f.
    apply r; intros [a u].
    exact (u (f a)).
  - exact (decidable_iff (pi_not_iff_not_sigma _ _ ) (c _ _)).
Defined.

(** So: LEM <-> all types ∃-compact -> all types Π-compact <-> WLEM. *)

(** ** "Stable-compact" types *)

(* Weaker than Σ-compact. *)
Definition IsStableCompact (A : Type)
  := forall P : A -> Type,
      (forall a, Decidable (P a)) -> Stable (sig P).

(* Weaker than ∃-compact. Equivalent to LEM if you assume it for all types. *)
Definition IsHStableCompact (A : Type)
  := forall P : A -> Type,
      (forall a, Decidable (P a)) -> Stable (hexists P).

(** Note that we if we try to weaken this even more by requiring the Π-type instead of the Σ-type to be stable, it is a case of [stable_forall] and is true for all types. *)

(** We can also make a stronger definition by asking for the family to be fibrewise stable instead of decidable. I do not see how we can then prove implications between this and other forms of compactness. *)

(* tcc: I am not satisfied with this since the family needs to be fibrewise Σ-compact, but at least it takes care of decidable subtypes. *)
Definition isstablecompact_sigma {A} {C : A -> Type}
  (cA : IsStableCompact A) (cC : forall a, IsSigmaCompact (C a))
  : IsStableCompact (sig C).
Proof.
  intros P dP.
  apply (stable_equiv' (equiv_sigma_assoc C P)).
  rapply cA; intro a.
  rapply cC.
Defined.

Definition ishstablecompact_sigma {A} {C : A -> Type}
  (cA : IsHStableCompact A) (cC : forall a, IsSigmaCompact (C a))
  : IsHStableCompact (sig C).
Proof.
  intros P dP.
  apply (stable_equiv' (Trunc_functor_equiv (-1) (equiv_sigma_assoc C P))).
  rapply cA; intro a.
  rapply cC.
Defined.
