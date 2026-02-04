(** * Right adjoints preserve products *)

From HoTT Require Import Basics Types.
Require Import Pointed WildCat WildCat.Core Products WildCat.Adjoint.

Local Open Scope pointed_scope.
Local Open Scope mc_mult_scope.
Local Open Scope path_scope.

Definition isthisgoingtowork {I C D : Type} {F : C -> D} {G : D -> C}
  `{Is1Cat C, Is1Cat D, !Is0Functor F, !Is0Functor G}
  (adj : Adjunction F G) (x : I -> D) `{!Product I (A:=D) x}
  : Product I (G o x).
Proof.
  snapply Build_Product.
  - exact (G (cat_prod I x)).
  - intro i.
    exact (fmap G (cat_pr i)).
  - intros c h.
    apply adj.
    apply cat_prod_corec.
    intro i.
    apply adj, (h i).
  - cbn.
    intros c h i.
    (* use natequiv_adjunction_r. *)
    admit.
  - intros c h1 h2 p.
    cbn in *.
    (* show that their adjuncts are equal *)
Admitted.

Definition maybebetter {I C D : Type} {F : C -> D} {G : D -> C}
(* too many assumptions? *)
  `{Is1Cat C,  Is1Cat D, !Is0Functor F, !Is0Functor G, !HasProducts I C, !HasEquivs C}
  (adj : Adjunction F G) (x : I -> D) `{Product I (A:=D) x}
  : cat_prod I (A:=C) (G o x) $<~> G (cat_prod I (A:=D) x).
Proof.
(* I need to use yon_0gpd, but Adjoint.v contains results for yon. *)
  snapply yon_equiv_0gpd.
  refine (natequiv_compose _ (natequiv_cat_prod_corec_inv I (x:=(G o x)))).
  
  snapply Build_NatEquiv.
  - intro c.
  (* ordinary equivalence given by the adjunction should induce natequiv (need external lemmas). *)
    (* refine ((equiv_adjunction adj c (cat_prod I x)) $oE _). *)
  
  (* snapply yon_equiv.
  1: exact Is1Cat_Strong0.
  unfold "$<~>".
  (* do I need to use objects or can I compose NatEquivs in a faster way? *)
  snapply Build_NatEquiv.
  - intro c.
    unfold "$<~>"; cbn.
    Check (equiv_adjunction adj c (cat_prod I x)).
    refine ((equiv_adjunction adj c (cat_prod I x)) oE _).
    pose (p:= cate_cat_prod_corec_inv I (x:=x) (z:=(F c))). *)

  
Admitted.