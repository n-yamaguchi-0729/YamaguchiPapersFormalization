/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.RingTheory.Descent.IntegralClosureLocalizationAway
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Localization.Integral
import Nyll.SchemeTheory.Normalization.Affine


/-!
# The generic fibre of an integral closure

For an algebraic commutative algebra `L` over the fraction field `K` of a commutative ring `R`,
localizing the integral closure of `R` in `L` at the nonzero elements of
`R` gives `L`. Consequently its generic fibre is the literal scheme `Spec L`,
including when `L` is a finite product rather than a field.
The comparison uses the original inclusions into `L` on both sides.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped nonZeroDivisors TensorProduct

namespace EtaleFundamentalGroups

universe u

variable (R K L : Type u) [CommRing R] [Field K] [CommRing L]
  [Algebra R K] [IsFractionRing R K] [Algebra K L] [Algebra R L]
  [IsScalarTower R K L] [Algebra.IsAlgebraic K L]

include K in
/-- Clearing an algebraic element's denominators identifies `L` with the
localization of the integral closure at the nonzero elements of `R`. -/
theorem integralClosure_generic_isLocalization :
    IsLocalization (Algebra.algebraMapSubmonoid (integralClosure R L) R⁰) L := by
  have : Algebra.IsIntegral K L := Algebra.IsAlgebraic.isIntegral
  exact SchemeTheory.integralClosure_isLocalization R⁰ K L

/-- The integral closure and the base fraction field have pushout `L`, with
the given structural maps. No finiteness of the integral closure is required. -/
theorem integralClosure_generic_isPushout :
    Algebra.IsPushout R (integralClosure R L) K L := by
  have : IsLocalization (Algebra.algebraMapSubmonoid (integralClosure R L) R⁰) L :=
    integralClosure_generic_isLocalization R K L
  exact Algebra.isPushout_of_isLocalization R⁰ K (integralClosure R L) L

/-- The coordinate ring of the generic fibre is the prescribed algebra,
compatibly with its `K`-algebra structure. -/
def integralClosureGenericFiberAlgEquiv :
    K ⊗[R] integralClosure R L ≃ₐ[K] L := by
  have : Algebra.IsPushout R K (integralClosure R L) L :=
    (integralClosure_generic_isPushout R K L).symm
  exact Algebra.IsPushout.equiv R K (integralClosure R L) L

/-- The generic-fibre comparison sends a pure tensor to the product of the
two original inclusions into `L`. -/
theorem integralClosureGenericFiberAlgEquiv_tmul
    (k : K) (b : integralClosure R L) :
    integralClosureGenericFiberAlgEquiv R K L (k ⊗ₜ[R] b) =
      algebraMap K L k * (b : L) := by
  have : Algebra.IsPushout R K (integralClosure R L) L :=
    (integralClosure_generic_isPushout R K L).symm
  exact Algebra.IsPushout.equiv_tmul R K (integralClosure R L) L k b

/-- The generic fibre of the spectrum of the integral closure is the actual `Spec L`,
using the actual inclusion of the integral closure into `L`. -/
theorem isPullback_spec_integralClosure_generic :
    IsPullback
      (Spec.map (CommRingCat.ofHom (algebraMap (integralClosure R L) L)))
      (Spec.map (CommRingCat.ofHom (algebraMap K L)))
      (Spec.map (CommRingCat.ofHom (algebraMap R (integralClosure R L))))
      (Spec.map (CommRingCat.ofHom (algebraMap R K))) := by
  have : Algebra.IsPushout R (integralClosure R L) K L :=
    integralClosure_generic_isPushout R K L
  exact isPullback_SpecMap_of_isPushout _ _ _ _
    (CommRingCat.isPushout_of_isPushout R (integralClosure R L) K L)

omit [Field K] [Algebra R K] [IsFractionRing R K]
  [Algebra K L] [IsScalarTower R K L] [Algebra.IsAlgebraic K L] in
/-- The affine normalization comparison respects its structural map to
`Spec R`. -/
@[reassoc]
theorem specNormalizationIso_hom_base :
    (specNormalizationIso R L).hom ≫
        Spec.map (CommRingCat.ofHom (algebraMap R (integralClosure R L))) =
      (Spec.map (CommRingCat.ofHom (algebraMap R L))).fromNormalization := by
  apply spec_toNormalization_hom_ext R L
  rw [← Category.assoc, toNormalization_specNormalizationIso_hom,
    ← Spec.map_comp, Scheme.Hom.toNormalization_fromNormalization]
  rfl

/-- The relative normalization of `Spec R` in `Spec L` has generic fibre
`Spec L`, with the canonical map into that normalization as the first leg. -/
theorem isPullback_affineNormalization_generic :
    IsPullback
      (Spec.map (CommRingCat.ofHom (algebraMap R L))).toNormalization
      (Spec.map (CommRingCat.ofHom (algebraMap K L)))
      (Spec.map (CommRingCat.ofHom (algebraMap R L))).fromNormalization
      (Spec.map (CommRingCat.ofHom (algebraMap R K))) := by
  exact (isPullback_spec_integralClosure_generic R K L).of_iso
    (Iso.refl _) (specNormalizationIso R L).symm (Iso.refl _) (Iso.refl _)
    (by
      rw [Iso.refl_hom, Category.id_comp, Iso.symm_hom,
        Iso.comp_inv_eq, toNormalization_specNormalizationIso_hom]
      rfl)
    (by simp only [Iso.refl_hom, Category.id_comp, Category.comp_id])
    (by
      simp only [Iso.refl_hom, Category.comp_id, Iso.symm_hom,
        ← specNormalizationIso_hom_base R L, Iso.inv_hom_id_assoc])
    (by simp only [Iso.refl_hom, Category.id_comp, Category.comp_id])

end EtaleFundamentalGroups
