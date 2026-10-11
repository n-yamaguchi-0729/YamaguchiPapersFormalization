/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Normalization.GenericExtensionFiber
import EtaleFundamentalGroups.Normalization.UnramifiedGeometricInertia
import EtaleFundamentalGroups.Inertia.NormalizationBaseChange
import SchemeTheory.Normalization.FiniteSeparable
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# The actual normalization action on a generic integral-closure chart

The original field automorphism restricts to the integral closure on every
nonempty affine chart. This restricted spectrum map and the actual global
normalizationEndomorphism commute with genericNormalizationChart. Their
composites agree after the injective integral-closure inclusion into L,
whose spectrum map is dominant. Reducedness of the chart and separatedness
of the normalization over the original base then give the required equality.

No finiteness, Galoisness, or algebraicity assumption on L/K is needed for
this equivariance statement, so it applies to the algebraic closures used
by the original global inertia-kernel theorem as well.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace EtaleFundamentalGroups

universe u

private local instance fieldSpecQuasiCompact
    {K : Type u} [Field K] {S : Scheme.{u}} (f : Spec (.of K) ⟶ S) :
    QuasiCompact f where
  isCompact_preimage U _ _ := (Set.toFinite (f ⁻¹' U)).isCompact

/-- The literal restricted field automorphism on an integral-closure chart
intertwines with the actual normalization endomorphism over X. -/
@[reassoc]
theorem genericNormalizationChart_endomorphism
    (X : Scheme.{u}) [IsIntegral X]
    (L : Type u) [Field L] [Algebra X.functionField L]
    (U : X.Opens) (hU : IsAffineOpen U) [Nonempty U]
    (σ : L ≃ₐ[X.functionField] L) :
    let : Algebra Γ(X, U) L := X.affineExtensionAlgebra U L
    let : IsScalarTower Γ(X, U) X.functionField L :=
      IsScalarTower.of_algebraMap_eq' rfl
    Spec.map (CommRingCat.ofHom
        (σ.restrictScalars Γ(X, U)).mapIntegralClosure.toRingHom) ≫
        genericNormalizationChart X L U hU =
      genericNormalizationChart X L U hU ≫
        Inertia.normalizationEndomorphism (X.genericExtensionMorphism L)
          (Spec.map (CommRingCat.ofHom σ.toRingHom))
          (genericExtensionMorphism_specMap_algEquiv X L σ) := by
  intro actualAlgebra actualTower
  let B := integralClosure Γ(X, U) L
  let f : Spec (.of L) ⟶ X := X.genericExtensionMorphism L
  let c : Spec (.of B) ⟶ f.normalization := genericNormalizationChart X L U hU
  let p : Spec (.of B) ⟶ Spec Γ(X, U) :=
    Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U) B))
  let i : Spec (.of L) ⟶ Spec (.of B) :=
    Spec.map (CommRingCat.ofHom (algebraMap B L))
  let τ : B ≃ₐ[Γ(X, U)] B := (σ.restrictScalars Γ(X, U)).mapIntegralClosure
  let t : Spec (.of B) ⟶ Spec (.of B) := Spec.map (CommRingCat.ofHom τ.toRingHom)
  let d : f.normalization ⟶ f.normalization :=
    Inertia.normalizationEndomorphism f (Spec.map (CommRingCat.ofHom σ.toRingHom))
      (genericExtensionMorphism_specMap_algEquiv X L σ)
  have ht : t ≫ p = p := by
    change Spec.map (CommRingCat.ofHom τ.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U) B)) =
        Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U) B))
    rw [← Spec.map_comp]
    apply congrArg Spec.map
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro a
    exact τ.commutes a
  have hi : i ≫ t = Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ i := by
    change Spec.map (CommRingCat.ofHom (algebraMap B L)) ≫
      Spec.map (CommRingCat.ofHom τ.toRingHom) =
        Spec.map (CommRingCat.ofHom σ.toRingHom) ≫
          Spec.map (CommRingCat.ofHom (algebraMap B L))
    rw [← Spec.map_comp, ← Spec.map_comp]
    apply congrArg Spec.map
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro b
    exact AlgEquiv.coe_mapIntegralClosure (σ.restrictScalars Γ(X, U)) b
  have hc : c ≫ f.fromNormalization = p ≫ hU.fromSpec :=
    genericNormalizationChart_base X L U hU
  have hd : d ≫ f.fromNormalization = f.fromNormalization :=
    Inertia.normalizationEndomorphism_fromNormalization f
      (Spec.map (CommRingCat.ofHom σ.toRingHom))
      (genericExtensionMorphism_specMap_algEquiv X L σ)
  have hbase : (t ≫ c) ≫ f.fromNormalization = (c ≫ d) ≫ f.fromNormalization := by
    calc
      (t ≫ c) ≫ f.fromNormalization = t ≫ (p ≫ hU.fromSpec) := by
        rw [Category.assoc, hc]
      _ = p ≫ hU.fromSpec := by rw [← Category.assoc, ht]
      _ = c ≫ f.fromNormalization := hc.symm
      _ = (c ≫ d) ≫ f.fromNormalization := by rw [Category.assoc, hd]
  have hgeneric : i ≫ c = f.toNormalization := spec_val_genericNormalizationChart X L U hU
  have hsource : i ≫ (t ≫ c) = i ≫ (c ≫ d) := by
    calc
      i ≫ (t ≫ c) = (i ≫ t) ≫ c := (Category.assoc i t c).symm
      _ = Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ (i ≫ c) := by
        rw [hi, Category.assoc]
      _ = Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ f.toNormalization := by rw [hgeneric]
      _ = f.toNormalization ≫ d :=
        (Inertia.toNormalization_normalizationEndomorphism f
          (Spec.map (CommRingCat.ofHom σ.toRingHom))
          (genericExtensionMorphism_specMap_algEquiv X L σ)).symm
      _ = i ≫ (c ≫ d) := by rw [← Category.assoc, hgeneric]
  have : IsDominant i := by
    rw [isDominant_iff]
    change DenseRange (PrimeSpectrum.comap (algebraMap B L))
    apply (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).mpr
    rw [(RingHom.injective_iff_ker_eq_bot _).mp Subtype.val_injective]
    exact bot_le
  have : IsReduced (Spec (.of B)) := inferInstance
  change t ≫ c = c ≫ d
  exact ext_of_isDominant_of_isSeparated f.fromNormalization hbase i hsource

end EtaleFundamentalGroups
