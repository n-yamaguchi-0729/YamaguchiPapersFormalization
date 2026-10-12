/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.Pi1.FiniteEtale.GaloisCategory
public import Mathlib.GroupTheory.GroupAction.Transitive

/-!
# Galois objects and Galois covers

This file supplies the abstract Galois-category part of the four equivalent
characterizations of a finite étale Galois cover in Stacks Project, Section
58.7 (`03SF`).  It uses the canonical mathlib notion
`CategoryTheory.PreGaloisCategory.IsGalois`.
-/

@[expose] public section

universe u₁ u₂ w

open CategoryTheory

namespace CategoryTheory.PreGaloisCategory

variable {C : Type u₁} [Category.{u₂} C] [GaloisCategory C]
variable (F : C ⥤ FintypeCat.{w}) [FiberFunctor F]

open Limits

/-- A connected object of a Galois category is Galois if and only if evaluation
at one point identifies its automorphism group with its fiber.  This is the
simply-transitive formulation in Stacks Project, Section 58.7. -/
@[stacks 03SF "four-way characterization by simply transitive fibers"]
theorem isGalois_iff_evaluation_bijective (X : C) [IsConnected X] (x : F.obj X) :
    IsGalois X ↔ Function.Bijective (fun σ : Aut X ↦ F.map σ.hom x) := by
  constructor
  · intro h
    let : IsGalois X := h
    exact evaluation_aut_bijective_of_isGalois F X x
  · intro h
    rw [isGalois_iff_pretransitive F X, MulAction.isPretransitive_iff_base x]
    exact h.surjective

attribute [local instance] FintypeCat.fintype

/-- A connected object of a Galois category is Galois if and only if the
cardinality of its automorphism group equals the cardinality of its fiber.
For a finite étale cover the latter cardinality is its degree. -/
@[stacks 03SF "four-way characterization by automorphism cardinality"]
theorem isGalois_iff_card_aut_eq_card_fiber (X : C) [IsConnected X] :
    IsGalois X ↔ Nat.card (Aut X) = Nat.card (F.obj X) := by
  let x : F.obj X := Classical.choice inferInstance
  constructor
  · intro h
    let : IsGalois X := h
    exact Nat.card_congr (evaluationEquivOfIsGalois F X x)
  · intro h
    apply (isGalois_iff_evaluation_bijective F X x).mpr
    let : Fintype (Aut X) := Fintype.ofFinite (Aut X)
    apply (Fintype.bijective_iff_injective_and_card _).mpr
    exact
      ⟨evaluation_aut_injective_of_isConnected F X x,
        by simpa only [← Nat.card_eq_fintype_card] using h⟩

private lemma fiberBinaryProduct_ext {X Y : C} {a b : F.obj (X ⨯ Y)}
    (hfst : F.map prod.fst a = F.map prod.fst b)
    (hsnd : F.map prod.snd a = F.map prod.snd b) :
    a = b := by
  let e := fiberBinaryProductEquiv F X Y
  apply e.injective
  apply Prod.ext
  · have ha : F.map prod.fst a = (e a).1 := by
      simpa only [e, Prod.eta, Equiv.symm_apply_apply] using
        fiberBinaryProductEquiv_symm_fst_apply F (e a).1 (e a).2
    have hb : F.map prod.fst b = (e b).1 := by
      simpa only [e, Prod.eta, Equiv.symm_apply_apply] using
        fiberBinaryProductEquiv_symm_fst_apply F (e b).1 (e b).2
    exact ha.symm.trans (hfst.trans hb)
  · have ha : F.map prod.snd a = (e a).2 := by
      simpa only [e, Prod.eta, Equiv.symm_apply_apply] using
        fiberBinaryProductEquiv_symm_snd_apply F (e a).1 (e a).2
    have hb : F.map prod.snd b = (e b).2 := by
      simpa only [e, Prod.eta, Equiv.symm_apply_apply] using
        fiberBinaryProductEquiv_symm_snd_apply F (e b).1 (e b).2
    exact ha.symm.trans (hsnd.trans hb)

/-- A connected subobject of a product of two Galois objects is Galois.
This is the Galois-category form of intersecting two normal open subgroups. -/
@[stacks 03SF "connected components of products of Galois covers are Galois"]
theorem isGalois_of_mono_to_binaryProduct {X Y Z : C}
    [IsGalois X] [IsGalois Y] [IsConnected Z]
    (i : Z ⟶ X ⨯ Y) [Mono i] :
    IsGalois Z := by
  let F := CategoryTheory.GaloisCategory.getFiberFunctor C
  apply (isGalois_iff_pretransitive F Z).mpr
  constructor
  intro a b
  obtain ⟨σX, hσX⟩ := MulAction.exists_smul_eq (Aut X)
    (F.map (i ≫ prod.fst) a) (F.map (i ≫ prod.fst) b)
  obtain ⟨σY, hσY⟩ := MulAction.exists_smul_eq (Aut Y)
    (F.map (i ≫ prod.snd) a) (F.map (i ≫ prod.snd) b)
  change F.map σX.hom (F.map (i ≫ prod.fst) a) = F.map (i ≫ prod.fst) b at hσX
  change F.map σY.hom (F.map (i ≫ prod.snd) a) = F.map (i ≫ prod.snd) b at hσY
  let τ : X ⨯ Y ≅ X ⨯ Y := prod.mapIso σX σY
  have hfst :
      F.map prod.fst (F.map (i ≫ τ.hom) a) =
        F.map prod.fst (F.map i b) := by
    calc
      _ = F.map σX.hom (F.map (i ≫ prod.fst) a) := by
        simp only [← FintypeCat.comp_apply, ← F.map_comp]
        exact congrArg (fun f : Z ⟶ X => F.map f a) (by simp [τ, prod.mapIso])
      _ = F.map (i ≫ prod.fst) b := hσX
      _ = F.map prod.fst (F.map i b) := by
        simp only [F.map_comp, FintypeCat.comp_apply]
  have hsnd :
      F.map prod.snd (F.map (i ≫ τ.hom) a) =
        F.map prod.snd (F.map i b) := by
    calc
      _ = F.map σY.hom (F.map (i ≫ prod.snd) a) := by
        simp only [← FintypeCat.comp_apply, ← F.map_comp]
        exact congrArg (fun f : Z ⟶ Y => F.map f a) (by simp [τ, prod.mapIso])
      _ = F.map (i ≫ prod.snd) b := hσY
      _ = F.map prod.snd (F.map i b) := by
        simp only [F.map_comp, FintypeCat.comp_apply]
  obtain ⟨σ, hσ⟩ := connected_component_unique F a b (i ≫ τ.hom) i
    (fiberBinaryProduct_ext F hfst hsnd)
  exact ⟨σ, hσ⟩

/-- If a connected object is a subobject of a product of two Galois objects,
the two induced maps on automorphism groups are jointly injective. -/
@[stacks 03SF "the common Galois group embeds in the product"]
theorem autMapHom_prod_injective_of_mono {X Y Z : C}
    [IsGalois X] [IsGalois Y] [IsConnected Z]
    (i : Z ⟶ X ⨯ Y) [Mono i] :
    Function.Injective
      (MonoidHom.prod (autMapHom (i ≫ prod.fst)) (autMapHom (i ≫ prod.snd))) := by
  intro σ τ hστ
  have hfst : autMap (i ≫ prod.fst) σ = autMap (i ≫ prod.fst) τ := by
    have h := congrArg (fun p : Aut X × Aut Y ↦ p.1) hστ
    change autMap (i ≫ prod.fst) σ = autMap (i ≫ prod.fst) τ at h
    exact h
  have hsnd : autMap (i ≫ prod.snd) σ = autMap (i ≫ prod.snd) τ := by
    have h := congrArg (fun p : Aut X × Aut Y ↦ p.2) hστ
    change autMap (i ≫ prod.snd) σ = autMap (i ≫ prod.snd) τ at h
    exact h
  apply Aut.ext
  rw [← cancel_mono i]
  apply prod.hom_ext
  · simp only [Category.assoc]
    rw [← comp_autMap (i ≫ prod.fst) σ, ← comp_autMap (i ≫ prod.fst) τ, hfst]
  · simp only [Category.assoc]
    rw [← comp_autMap (i ≫ prod.snd) σ, ← comp_autMap (i ≫ prod.snd) τ, hsnd]

/-- Two Galois objects have a common Galois cover.  Its automorphism group
maps injectively to the product of the two original automorphism groups. -/
@[stacks 03SF "common domination of two Galois covers"]
theorem exists_common_galois_cover (X Y : C) [IsGalois X] [IsGalois Y] :
    ∃ (Z : C) (hZ : IsGalois Z),
      letI := hZ
      ∃ (f : Z ⟶ X) (g : Z ⟶ Y),
        Function.Injective (MonoidHom.prod (autMapHom f) (autMapHom g)) := by
  let F := CategoryTheory.GaloisCategory.getFiberFunctor C
  let x : F.obj X := Classical.choice inferInstance
  let y : F.obj Y := Classical.choice inferInstance
  obtain ⟨Z, i, _, _, hZ, hi⟩ := fiber_in_connected_component F (X ⨯ Y)
    ((fiberBinaryProductEquiv F X Y).symm (x, y))
  let : IsConnected Z := hZ
  let : Mono i := hi
  have hGalois : IsGalois Z := isGalois_of_mono_to_binaryProduct i
  let : IsGalois Z := hGalois
  exact ⟨Z, hGalois, i ≫ prod.fst, i ≫ prod.snd,
    autMapHom_prod_injective_of_mono i⟩

end CategoryTheory.PreGaloisCategory

namespace AlgebraicGeometry.FiniteEtale

universe u

open CategoryTheory

variable {Ω : Type u} [Field Ω] [IsSepClosed Ω]

/-- Over a separably closed field, the number of points of a finite étale
scheme is the rank of its structure morphism. -/
@[stacks 03SF "geometric-fiber cardinality equals degree"]
theorem natCard_left_eq_finrank (X : FiniteEtale (Spec (.of Ω))) :
    Nat.card X.left = X.hom.finrank (IsLocalRing.closedPoint Ω) := by
  change Nat.card X.left =
    (X.left ↘ Spec (.of Ω)).finrank (IsLocalRing.closedPoint Ω)
  rw [← IsFiniteEtale.isoSpecFun_hom_SpecMap Ω X.left,
    Scheme.Hom.finrank_comp_left_of_isIso,
    Scheme.Hom.finrank_SpecMap_algebraMap]
  simp only [Module.rankAtStalk_eq_finrank_of_free, Pi.natCast_apply, Nat.cast_id,
    Module.finrank_fintype_fun_eq_card, Nat.card_eq_fintype_card]

variable {S : Scheme.{u}} (ξ : Spec (.of Ω) ⟶ S)

/-- The cardinality of the geometric fiber of a finite étale morphism is its
rank at the image of the geometric point. -/
@[stacks 03SF "geometric-fiber cardinality equals degree"]
theorem natCard_fiber_eq_finrank (X : FiniteEtale S) :
    Nat.card ((fiber ξ).obj X) =
      X.hom.finrank (ξ (IsLocalRing.closedPoint Ω)) := by
  let : Limits.HasPullback X.hom ξ := inferInstance
  let Y : FiniteEtale (Spec (.of Ω)) :=
    FiniteEtale.mk (Limits.pullback.snd X.hom ξ)
  change Nat.card Y.left = X.hom.finrank (ξ (IsLocalRing.closedPoint Ω))
  calc
    Nat.card Y.left =
        Y.hom.finrank (IsLocalRing.closedPoint Ω) :=
      natCard_left_eq_finrank Y
    _ = X.hom.finrank (ξ (IsLocalRing.closedPoint Ω)) :=
      Scheme.Hom.finrank_of_isPullback
        (Limits.pullback.fst X.hom ξ) Y.hom X.hom ξ
        (by
          change IsPullback (Limits.pullback.fst X.hom ξ)
            (Limits.pullback.snd X.hom ξ) X.hom ξ
          exact IsPullback.of_hasPullback X.hom ξ)
        (IsLocalRing.closedPoint Ω)

variable [ConnectedSpace S]

/-- Scheme-theoretic degree form of the automorphism-cardinality
characterization of a connected finite étale Galois cover. -/
@[stacks 03SF "four-way characterization by automorphism cardinality and degree"]
theorem isGalois_iff_card_aut_eq_finrank
    (X : FiniteEtale S) [PreGaloisCategory.IsConnected X] :
    PreGaloisCategory.IsGalois X ↔
      Nat.card (Aut X) = X.hom.finrank (ξ (IsLocalRing.closedPoint Ω)) := by
  rw [PreGaloisCategory.isGalois_iff_card_aut_eq_card_fiber (fiber ξ) X,
    natCard_fiber_eq_finrank ξ X]

/-- A finite étale cover is Galois exactly when it is connected and its
automorphism group has cardinality equal to its degree. -/
@[stacks 03SF "four-way characterization by connectedness and degree"]
theorem isGalois_iff_isConnected_and_card_aut_eq_finrank (X : FiniteEtale S) :
    PreGaloisCategory.IsGalois X ↔
      PreGaloisCategory.IsConnected X ∧
        Nat.card (Aut X) = X.hom.finrank (ξ (IsLocalRing.closedPoint Ω)) := by
  constructor
  · intro h
    let : PreGaloisCategory.IsGalois X := h
    exact ⟨inferInstance, (isGalois_iff_card_aut_eq_finrank ξ X).mp h⟩
  · rintro ⟨hX, h⟩
    let : PreGaloisCategory.IsConnected X := hX
    exact (isGalois_iff_card_aut_eq_finrank ξ X).mpr h

end AlgebraicGeometry.FiniteEtale
