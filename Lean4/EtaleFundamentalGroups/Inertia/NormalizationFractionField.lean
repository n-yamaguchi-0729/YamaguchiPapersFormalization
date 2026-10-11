/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Inertia.AffineNormalizationGeometricPoint
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.Localization.FractionRing

/-!
# Normalizing in a normal affine scheme or its fraction field

If `B` is integrally closed, an element of its fraction field integral over
`R` already belongs to `B`. Thus the two actual integral closures are
canonically isomorphic. This isomorphism intertwines automorphisms and,
on spectra, the relative-normalization deck maps and their point stabilizers.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

namespace EtaleFundamentalGroups.Inertia

universe u

variable (R B L : Type u) [CommRing R] [CommRing B] [Field L]
variable [Algebra R B] [Algebra B L] [Algebra R L] [IsScalarTower R B L]
variable [IsDomain B] [IsFractionRing B L] [IsIntegrallyClosed B]

/-- Passing to the fraction field of a normal domain does not change the
integral closure of any base ring in it. -/
def integralClosureFractionFieldAlgEquiv :
    integralClosure R B ≃ₐ[R] integralClosure R L := by
  apply AlgEquiv.ofBijective (IsScalarTower.toAlgHom R B L).mapIntegralClosure
  constructor
  · intro x y h
    apply Subtype.ext
    apply IsFractionRing.injective B L
    exact congrArg (fun a : integralClosure R L => (a : L)) h
  · intro x
    obtain ⟨b, hb⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral
      (R := B) (K := L) x.property.tower_top
    have hbIntegral : IsIntegral R b := by
      apply (isIntegral_algebraMap_iff (R := R) (A := B) (B := L)).mp
      rw [hb]
      exact x.property
    exact ⟨⟨b, hbIntegral⟩, Subtype.ext hb⟩

theorem integralClosureFractionFieldAlgEquiv_coe (x : integralClosure R B) :
    (integralClosureFractionFieldAlgEquiv R B L x : L) = algebraMap B L (x : B) := rfl

/-- Extend a base-linear automorphism to the actual fraction field. -/
def fractionFieldAlgEquiv (sigma : B ≃ₐ[R] B) : L ≃ₐ[R] L :=
  IsLocalization.algEquivOfAlgEquiv L L sigma
    (MulEquivClass.map_nonZeroDivisors sigma)

omit [IsDomain B] [IsIntegrallyClosed B] in
theorem fractionFieldAlgEquiv_algebraMap (sigma : B ≃ₐ[R] B) (b : B) :
    fractionFieldAlgEquiv R B L sigma (algebraMap B L b) =
      algebraMap B L (sigma b) :=
  IsLocalization.algEquivOfAlgEquiv_eq
    (MulEquivClass.map_nonZeroDivisors sigma) b

/-- The closure comparison intertwines the literal restrictions of the two
automorphisms. -/
theorem integralClosureFractionFieldAlgEquiv_equivariant
    (sigma : B ≃ₐ[R] B) (x : integralClosure R B) :
    integralClosureFractionFieldAlgEquiv R B L (sigma.mapIntegralClosure x) =
      (fractionFieldAlgEquiv R B L sigma).mapIntegralClosure
        (integralClosureFractionFieldAlgEquiv R B L x) := by
  apply Subtype.ext
  exact (fractionFieldAlgEquiv_algebraMap R B L sigma (x : B)).symm

/-- The normalization in the fraction field is canonically the normalization
in the original normal affine scheme. -/
def affineNormalizationFractionFieldIso :
    (Spec.map (CommRingCat.ofHom (algebraMap R L))).normalization ≅
      (Spec.map (CommRingCat.ofHom (algebraMap R B))).normalization :=
  specNormalizationIso R L ≪≫
    Scheme.Spec.mapIso (integralClosureFractionFieldAlgEquiv R B L).toCommRingCatIso.op ≪≫
      (specNormalizationIso R B).symm

/-- The normalization comparison commutes with the actual deck extensions. -/
@[reassoc]
theorem affineNormalizationFractionFieldIso_hom_deck
    (sigma : B ≃ₐ[R] B) :
    affineNormalizationDeck R L (fractionFieldAlgEquiv R B L sigma) ≫
        (affineNormalizationFractionFieldIso R B L).hom =
      (affineNormalizationFractionFieldIso R B L).hom ≫
        affineNormalizationDeck R B sigma := by
  apply (cancel_mono (specNormalizationIso R B).hom).mp
  simp only [affineNormalizationFractionFieldIso, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom, Iso.op_hom, Category.assoc, Iso.inv_hom_id,
    Category.comp_id, affineNormalizationDeck_specNormalizationIso_hom,
    affineNormalizationDeck_specNormalizationIso_hom_assoc, Iso.inv_hom_id_assoc]
  have heMap : Scheme.Spec.map
      (integralClosureFractionFieldAlgEquiv R B L).toCommRingCatIso.hom.op =
      Spec.map (CommRingCat.ofHom (integralClosureFractionFieldAlgEquiv R B L).toRingHom) := rfl
  rw [heMap, ← Spec.map_comp, ← Spec.map_comp]
  congr 1
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro x
  exact (integralClosureFractionFieldAlgEquiv_equivariant R B L sigma x).symm

/-- An actual normalization point has exactly the same stabilizer after
transport to the normalization in the fraction field. -/
theorem affineNormalizationFractionFieldIso_fixes_iff
    {T : Scheme.{u}}
    (z : T ⟶ (Spec.map (CommRingCat.ofHom (algebraMap R B))).normalization)
    (sigma : B ≃ₐ[R] B) :
    (z ≫ (affineNormalizationFractionFieldIso R B L).inv) ≫
        affineNormalizationDeck R L (fractionFieldAlgEquiv R B L sigma) =
      z ≫ (affineNormalizationFractionFieldIso R B L).inv ↔
    z ≫ affineNormalizationDeck R B sigma = z := by
  rw [← cancel_mono (affineNormalizationFractionFieldIso R B L).hom]
  simp only [Category.assoc, affineNormalizationFractionFieldIso_hom_deck,
    Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]

end EtaleFundamentalGroups.Inertia
