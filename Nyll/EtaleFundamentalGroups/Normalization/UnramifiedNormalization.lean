/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Normalization.UnramifiedNormalBase
import Nyll.EtaleFundamentalGroups.StrictHenselian.GeometricStalkFlat
import Nyll.EtaleFundamentalGroups.StrictHenselian.GeometricStalkStructure
import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent
import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
import Mathlib.AlgebraicGeometry.Morphisms.FlatDescent
import Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties
import Mathlib.RingTheory.RingHom.Unramified
import Mathlib.RingTheory.Etale.Descent
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting
import Mathlib.CategoryTheory.MorphismProperty.Descent
import Nyll.SchemeTheory.Normalization.FiniteSeparable
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant


/-!
# Unramified normalizations are finite étale

A dominant unramified morphism from an integral scheme to a normal integral
scheme is étale. Applied to relative normalization in a field extension of
the function field, integrality then supplies finiteness. No Noetherian
assumption is needed.

Reference: https://stacks.math.columbia.edu/tag/0BQK
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry

namespace EtaleFundamentalGroups

universe u

/-- A quasi-compact dominant unramified morphism between integral schemes
is étale if its target is normal. -/
theorem etale_of_dominant_unramified
    {X Y : Scheme.{u}} [IsIntegral X] [IsNormalIntegral X] [IsIntegral Y]
    (f : Y ⟶ X) [IsDominant f] [QuasiCompact f]
    [FormallyUnramified f] [LocallyOfFiniteType f] : Etale f := by
  let : IsSchemeTheoreticallyDominant f :=
    IsSchemeTheoreticallyDominant.of_isDominant f
  apply (HasRingHomProperty.iff_exists_appLE (P := @Etale)
    (RingHom.Etale.stableUnderComposition.stableUnderCompositionWithLocalizationAway
      (RingHom.Etale.propertyIsLocal.HoldsForLocalizationAway
        RingHom.Etale.containsIdentities)).1).mpr
  intro y
  obtain ⟨U, hU, hyU, -⟩ :=
    exists_isAffineOpen_mem_and_subset (X := X) (U := ⊤) (x := f y) (by trivial)
  obtain ⟨V, hV, hyV, e⟩ :=
    exists_isAffineOpen_mem_and_subset (X := Y) (U := f ⁻¹ᵁ U) (x := y) hyU
  refine ⟨⟨U, hU⟩, ⟨V, hV⟩, hyV, e, ?_⟩
  let : Nonempty V := ⟨⟨y, hyV⟩⟩
  let : Nonempty U := ⟨⟨f y, hyU⟩⟩
  let φ := (f.appLE U V e).hom
  let : Algebra Γ(X, U) Γ(Y, V) := φ.toAlgebra
  change Algebra.Etale Γ(X, U) Γ(Y, V)
  let : IsIntegrallyClosed Γ(X, U) :=
    IsNormalIntegral.affine_isIntegrallyClosed U hU
  have hφ : Function.Injective φ :=
    (map_injective_of_isIntegral Y (homOfLE e)).comp (f.app_injective U)
  let : FaithfulSMul Γ(X, U) Γ(Y, V) :=
    (faithfulSMul_iff_algebraMap_injective Γ(X, U) Γ(Y, V)).mpr hφ
  let : Algebra.FiniteType Γ(X, U) Γ(Y, V) :=
    f.finiteType_appLE hU hV e
  let : Algebra.FormallyUnramified Γ(X, U) Γ(Y, V) :=
    f.formallyUnramified_appLE hU hV e
  exact etale_of_unramified_of_domain_of_faithful

private local instance fieldSpecQuasiCompact
    {K : Type u} [Field K] {S : Scheme.{u}} (f : Spec (.of K) ⟶ S) :
    QuasiCompact f where
  isCompact_preimage U _ _ := (Set.toFinite (f ⁻¹' U)).isCompact

/-- The generic extension morphism has dense image because its image
contains the generic point. -/
theorem isDominant_genericExtensionMorphism
    (X : Scheme.{u}) [IsIntegral X]
    (L : Type u) [Field L] [Algebra X.functionField L] :
    IsDominant (X.genericExtensionMorphism L) := by
  rw [isDominant_iff, DenseRange, dense_iff_closure_eq]
  apply Set.eq_univ_of_forall
  intro x
  apply (genericPoint_specializes x).mem_closed isClosed_closure
  exact subset_closure
    ⟨IsLocalRing.closedPoint (CommRingCat.of L),
      X.genericExtensionMorphism_apply_closedPoint L⟩

/-- The relative normalization in a field extension remains dominant over
the original integral scheme. -/
theorem isDominant_fromNormalization_genericExtension
    (X : Scheme.{u}) [IsIntegral X]
    (L : Type u) [Field L] [Algebra X.functionField L] :
    IsDominant (X.genericExtensionMorphism L).fromNormalization := by
  let f := X.genericExtensionMorphism L
  have hf : IsDominant f := isDominant_genericExtensionMorphism X L
  have : IsDominant (f.toNormalization ≫ f.fromNormalization) := by
    rw [f.toNormalization_fromNormalization]
    exact hf
  exact IsDominant.of_comp f.toNormalization f.fromNormalization

/-- Stacks Project, Tag 0BQK: normalization is unramified exactly when it
is étale, and in this case it is finite. -/
theorem unramified_normalization_iff_etale_iff_finiteEtale
    (X : Scheme.{u}) [IsIntegral X] [IsNormalIntegral X]
    (L : Type u) [Field L] [Algebra X.functionField L] :
    ((FormallyUnramified (X.genericExtensionMorphism L).fromNormalization ∧
        LocallyOfFiniteType (X.genericExtensionMorphism L).fromNormalization) ↔
      Etale (X.genericExtensionMorphism L).fromNormalization) ∧
    (Etale (X.genericExtensionMorphism L).fromNormalization ↔
      IsFinite (X.genericExtensionMorphism L).fromNormalization ∧
        Etale (X.genericExtensionMorphism L).fromNormalization) := by
  let f := X.genericExtensionMorphism L
  let : IsDominant f.fromNormalization :=
    isDominant_fromNormalization_genericExtension X L
  constructor
  · constructor
    · rintro ⟨hUnramified, hFiniteType⟩
      let : FormallyUnramified f.fromNormalization := hUnramified
      let : LocallyOfFiniteType f.fromNormalization := hFiniteType
      exact etale_of_dominant_unramified f.fromNormalization
    · intro hEtale
      let : Etale f.fromNormalization := hEtale
      exact ⟨inferInstance, inferInstance⟩
  · constructor
    · intro hEtale
      let : Etale f.fromNormalization := hEtale
      refine ⟨?_, hEtale⟩
      exact (IsFinite.iff_isIntegralHom_and_locallyOfFiniteType
        f.fromNormalization).mpr ⟨inferInstance, inferInstance⟩
    · exact And.right

/-- An unramified normalization remains unramified over the local ring at
any point. This is the original implication `(2) → (5)` in Tag 0BTF. -/
theorem unramified_normalization_stalk_of_unramified
    (X : Scheme.{u}) [IsIntegral X]
    (L : Type u) [Field L] [Algebra X.functionField L]
    (h : FormallyUnramified (X.genericExtensionMorphism L).fromNormalization ∧
      LocallyOfFiniteType (X.genericExtensionMorphism L).fromNormalization)
    (x : X) :
    FormallyUnramified (pullback.snd
        (X.genericExtensionMorphism L).fromNormalization (X.fromSpecStalk x)) ∧
      LocallyOfFiniteType (pullback.snd
        (X.genericExtensionMorphism L).fromNormalization (X.fromSpecStalk x)) := by
  have : MorphismProperty.IsStableUnderBaseChange
      (@FormallyUnramified : MorphismProperty Scheme.{u}) :=
    HasRingHomProperty.isStableUnderBaseChange
      RingHom.FormallyUnramified.isStableUnderBaseChange
  have : MorphismProperty.IsStableUnderBaseChange
      (@LocallyOfFiniteType : MorphismProperty Scheme.{u}) :=
    HasRingHomProperty.isStableUnderBaseChange RingHom.finiteType_isStableUnderBaseChange
  exact ⟨MorphismProperty.of_isPullback
    (P := (@FormallyUnramified : MorphismProperty Scheme.{u}))
    (IsPullback.of_hasPullback
      (X.genericExtensionMorphism L).fromNormalization (X.fromSpecStalk x)) h.1,
    MorphismProperty.of_isPullback
      (P := (@LocallyOfFiniteType : MorphismProperty Scheme.{u}))
      (IsPullback.of_hasPullback
        (X.genericExtensionMorphism L).fromNormalization (X.fromSpecStalk x)) h.2⟩

/-- Unramifiedness over the actual local ring is equivalent to unramifiedness
over its constructed pointed étale stalk. Faithful flatness of the actual
structure map supplies descent, and pullback pasting compares the literal
scheme morphisms. The residue-field point gives the ordinary henselization;
a separably closed geometric point gives the strict henselization. Thus this
supplies `(5) ↔ (6)` and `(5) ↔ (7)` in Tag 0BTF. No finite-presentation,
separability, Galois, or Noetherian premise is added. -/
theorem unramified_normalization_stalk_iff_geometricStalk
    (X : Scheme.{u}) [IsIntegral X]
    (L : Type u) [Field L] [Algebra X.functionField L]
    (x : X) {Ω : Type u} [Field Ω]
    (φ : X.presheaf.stalk x →+* Ω) [IsLocalHom φ] :
    (FormallyUnramified (pullback.snd
        (X.genericExtensionMorphism L).fromNormalization (X.fromSpecStalk x)) ∧
      LocallyOfFiniteType (pullback.snd
        (X.genericExtensionMorphism L).fromNormalization (X.fromSpecStalk x))) ↔
    (FormallyUnramified (pullback.snd
        (X.genericExtensionMorphism L).fromNormalization
        (Spec.map (CommRingCat.ofHom (StrictHenselian.geometricStalkStructureMap φ)) ≫
          X.fromSpecStalk x)) ∧
      LocallyOfFiniteType (pullback.snd
        (X.genericExtensionMorphism L).fromNormalization
        (Spec.map (CommRingCat.ofHom (StrictHenselian.geometricStalkStructureMap φ)) ≫
          X.fromSpecStalk x))) := by
  let f := (X.genericExtensionMorphism L).fromNormalization
  let b := X.fromSpecStalk x
  let a := Spec.map (CommRingCat.ofHom (StrictHenselian.geometricStalkStructureMap φ))
  let P : MorphismProperty Scheme.{u} := @FormallyUnramified ⊓ @LocallyOfFiniteType
  have : MorphismProperty.IsStableUnderBaseChange
      (@FormallyUnramified : MorphismProperty Scheme.{u}) :=
    HasRingHomProperty.isStableUnderBaseChange
      RingHom.FormallyUnramified.isStableUnderBaseChange
  have : P.IsStableUnderBaseChange := MorphismProperty.IsStableUnderBaseChange.inf
  have : MorphismProperty.DescendsAlong
      (@FormallyUnramified : MorphismProperty Scheme.{u})
      (@Surjective ⊓ @Flat ⊓ @QuasiCompact) :=
    HasRingHomProperty.descendsAlong_flat
      RingHom.FormallyUnramified.codescendsAlong_faithfullyFlat
  have : P.RespectsIso :=
    inferInstanceAs (MorphismProperty.RespectsIso
      ((@FormallyUnramified : MorphismProperty Scheme.{u}) ⊓ @LocallyOfFiniteType))
  have : P.DescendsAlong (@Surjective ⊓ @Flat ⊓ @QuasiCompact) :=
    MorphismProperty.DescendsAlong.inf
  have ha : Flat a ∧ Surjective a :=
    (flat_and_surjective_SpecMap_iff
      (CommRingCat.ofHom (StrictHenselian.geometricStalkStructureMap φ))).mpr
        (StrictHenselian.geometricStalkStructureMap_faithfullyFlat φ)
  have hdescent : P (pullback.snd (pullback.snd f b) a) ↔ P (pullback.snd f b) :=
    MorphismProperty.pullback_snd_iff (P := P)
      (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact)
      ⟨⟨ha.2, ha.1⟩, inferInstance⟩
  let e := pullbackLeftPullbackSndIso f b a
  have hpaste : P (pullback.snd (pullback.snd f b) a) ↔
      P (pullback.snd f (a ≫ b)) := by
    rw [← pullbackLeftPullbackSndIso_hom_snd f b a]
    exact P.cancel_left_of_respectsIso e.hom (pullback.snd f (a ≫ b))
  exact hdescent.symm.trans hpaste

end EtaleFundamentalGroups
