/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Inertia.NormalizationLocalization
import EtaleFundamentalGroups.Inertia.AffineNormalizationGeometricPoint
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic

/-!
# Comparing an affine normalization with normalization in the function field

For a normal domain `B` over `R`, the integral closure of `R` inside `B`
maps bijectively to the integral closure of `R` inside the fraction field
of `B`. Indeed, an element integral over `R` is integral over `B`, so
normality puts it back in `B`; injectivity then reflects integrality over
`R`.

The resulting canonical affine normalization isomorphism intertwines the
map from the fraction-field spectrum and the map to `Spec R`. Thus it
compares the actual relative normalization used by geometric-point inertia
with the field-theoretic integral closure used by local inertia theorems.
This is a local normal-domain result and does not require the original
ambient scheme of the manuscript to be normal or integral everywhere.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

namespace EtaleFundamentalGroups.Inertia

universe u

variable (R B L : Type u) [CommRing R] [CommRing B] [IsDomain B]
  [IsIntegrallyClosed B] [Field L]
  [Algebra R B] [Algebra B L] [IsFractionRing B L]
  [Algebra R L] [IsScalarTower R B L]

omit [IsDomain B] in
/-- Normality of `B` makes its integral closure over `R` equal to the
integral closure computed in its actual fraction field. -/
theorem integralClosureToFractionField_bijective :
    Function.Bijective (IsScalarTower.toAlgHom R B L).mapIntegralClosure := by
  refine ⟨?_, ?_⟩
  · intro x y h
    apply Subtype.ext
    apply IsFractionRing.injective B L
    exact congrArg (fun z : integralClosure R L => (z : L)) h
  · intro x
    obtain ⟨b, hb⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral
      (x.property.tower_top (A := B))
    have hb' : IsIntegral R (algebraMap B L b) := hb.symm ▸ x.property
    have hbInt : IsIntegral R b :=
      (isIntegral_algHom_iff (IsScalarTower.toAlgHom R B L)
        (IsFractionRing.injective B L)).mp hb'
    exact ⟨⟨b, hbInt⟩, Subtype.ext hb⟩

/-- The comparison is the literal map into the fraction field, with its
inverse supplied by integrally closedness. -/
def integralClosureFractionFieldEquiv :
    integralClosure R B ≃ₐ[R] integralClosure R L :=
  AlgEquiv.ofBijective (IsScalarTower.toAlgHom R B L).mapIntegralClosure
    (integralClosureToFractionField_bijective R B L)

omit [IsDomain B] in
/-- The comparison agrees with the original inclusion into the fraction field. -/
@[simp]
theorem integralClosureFractionFieldEquiv_val (b : integralClosure R B) :
    (integralClosureFractionFieldEquiv R B L b : L) = algebraMap B L (b : B) :=
  rfl

omit [IsDomain B] in
/-- The integral-closure comparison intertwines a ring automorphism with
its actual extension to the fraction field. Compatibility is a consequence
of the fraction-field construction, not an additional input. -/
theorem integralClosureFractionFieldEquiv_mapIntegralClosure
    (σ : B ≃ₐ[R] B) (b : integralClosure R B) :
    integralClosureFractionFieldEquiv R B L (σ.mapIntegralClosure b) =
      (IsFractionRing.algEquivOfAlgEquiv σ : L ≃ₐ[R] L).mapIntegralClosure
        (integralClosureFractionFieldEquiv R B L b) := by
  apply Subtype.ext
  change algebraMap B L (σ (b : B)) =
    (IsFractionRing.algEquivOfAlgEquiv σ : L ≃ₐ[R] L)
      (algebraMap B L (b : B))
  exact (IsFractionRing.algEquivOfAlgEquiv_algebraMap σ (b : B)).symm

/-- The actual relative normalization of `Spec B → Spec R`, expressed
using the integral closure in the fraction field of `B`. -/
def affineNormalizationFunctionFieldIso :
    (Spec.map (CommRingCat.ofHom (algebraMap R B))).normalization ≅
      Spec (CommRingCat.of (integralClosure R L)) :=
  specNormalizationIso R B ≪≫
    Scheme.Spec.mapIso
      (integralClosureFractionFieldEquiv R B L).toRingEquiv.toCommRingCatIso.symm.op

omit [IsDomain B] in
/-- The point from the fraction field has its canonical integral-closure
coordinates under the normalization comparison. -/
@[reassoc]
theorem fractionField_toNormalization_affineNormalizationFunctionFieldIso :
    Spec.map (CommRingCat.ofHom (algebraMap B L)) ≫
        (Spec.map (CommRingCat.ofHom (algebraMap R B))).toNormalization ≫
        (affineNormalizationFunctionFieldIso R B L).hom =
      Spec.map (CommRingCat.ofHom (integralClosure R L).val.toRingHom) := by
  change Spec.map (CommRingCat.ofHom (algebraMap B L)) ≫
    (Spec.map (CommRingCat.ofHom (algebraMap R B))).toNormalization ≫
    ((specNormalizationIso R B).hom ≫
      Spec.map (integralClosureFractionFieldEquiv R B L).toRingEquiv.toCommRingCatIso.inv) = _
  rw [← Category.assoc
    (Spec.map (CommRingCat.ofHom (algebraMap R B))).toNormalization,
    toNormalization_specNormalizationIso_hom,
    ← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro x
  exact congrArg (fun y : integralClosure R L => (y : L))
    ((integralClosureFractionFieldEquiv R B L).apply_symm_apply x)

omit [IsDomain B] in
/-- The function-field normalization comparison preserves the structure
map to the original affine base. -/
@[reassoc]
theorem affineNormalizationFunctionFieldIso_hom_structureMap :
    (affineNormalizationFunctionFieldIso R B L).hom ≫
        Spec.map (CommRingCat.ofHom (algebraMap R (integralClosure R L))) =
      (Spec.map (CommRingCat.ofHom (algebraMap R B))).fromNormalization := by
  change ((specNormalizationIso R B).hom ≫
    Spec.map (integralClosureFractionFieldEquiv R B L).toRingEquiv.toCommRingCatIso.inv) ≫
      Spec.map (CommRingCat.ofHom (algebraMap R (integralClosure R L))) = _
  rw [Category.assoc, ← Spec.map_comp]
  have hcomp :
      CommRingCat.ofHom (algebraMap R (integralClosure R L)) ≫
        (integralClosureFractionFieldEquiv R B L).toRingEquiv.toCommRingCatIso.inv =
      CommRingCat.ofHom (algebraMap R (integralClosure R B)) := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro r
    exact (integralClosureFractionFieldEquiv R B L).symm.commutes r
  rw [hcomp, specNormalizationIso_hom_structureMap]

omit [IsDomain B] in
/-- Under the function-field normalization comparison, the actual
normalization deck extension is the restriction of the actual fraction-field
automorphism to its integral closure. -/
@[reassoc]
theorem affineNormalizationDeck_affineNormalizationFunctionFieldIso
    (σ : B ≃ₐ[R] B) :
    affineNormalizationDeck R B σ ≫
        (affineNormalizationFunctionFieldIso R B L).hom =
      (affineNormalizationFunctionFieldIso R B L).hom ≫
        Spec.map (CommRingCat.ofHom
          (((IsFractionRing.algEquivOfAlgEquiv σ :
            L ≃ₐ[R] L).toAlgHom.mapIntegralClosure).toRingHom)) := by
  let e := integralClosureFractionFieldEquiv R B L
  let τ : L ≃ₐ[R] L := IsFractionRing.algEquivOfAlgEquiv σ
  have hcomp :
      e.toRingEquiv.toCommRingCatIso.inv ≫
        CommRingCat.ofHom σ.toAlgHom.mapIntegralClosure.toRingHom =
      CommRingCat.ofHom τ.toAlgHom.mapIntegralClosure.toRingHom ≫
        e.toRingEquiv.toCommRingCatIso.inv := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro x
    change σ.mapIntegralClosure (e.symm x) = e.symm (τ.mapIntegralClosure x)
    apply e.injective
    rw [integralClosureFractionFieldEquiv_mapIntegralClosure,
      AlgEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply]
  change affineNormalizationDeck R B σ ≫
    ((specNormalizationIso R B).hom ≫ Spec.map e.toRingEquiv.toCommRingCatIso.inv) =
    ((specNormalizationIso R B).hom ≫ Spec.map e.toRingEquiv.toCommRingCatIso.inv) ≫
      Spec.map (CommRingCat.ofHom τ.toAlgHom.mapIntegralClosure.toRingHom)
  rw [← Category.assoc, affineNormalizationDeck_specNormalizationIso_hom,
    Category.assoc, Category.assoc, ← Spec.map_comp, ← Spec.map_comp, hcomp]

end EtaleFundamentalGroups.Inertia
