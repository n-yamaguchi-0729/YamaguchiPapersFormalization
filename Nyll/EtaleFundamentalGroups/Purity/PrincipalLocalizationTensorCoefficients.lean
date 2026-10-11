/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Purity.PrincipalLocalizationComplex
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import Mathlib.Algebra.Homology.Additive
import Mathlib.Algebra.Module.LocalizedModule.IsLocalization
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.RingTheory.Localization.BaseChange

/-!
# Tensor coefficients for the principal localization complex

The usual tensor description of module localization identifies tensoring
the ring's principal localization complex with the principal complex of
the coefficient module. Compatibility with the differential is checked
on pure tensors using the actual localization maps.
-/

noncomputable section

namespace EtaleFundamentalGroups.Purity

universe u

open CategoryTheory Limits MonoidalCategory
open scoped TensorProduct

variable {R : Type u} [CommRing R]

private def tensorLocalizedRingEquiv (S : Submonoid R) (M : ModuleCat.{u} R) :
    M ⊗[R] LocalizedModule S R ≃ₗ[R] LocalizedModule S M :=
  (TensorProduct.congr (LinearEquiv.refl R M)
    (IsLocalizedModule.linearEquiv S (LocalizedModule.mkLinearMap S R)
      (Algebra.linearMap R (Localization S)))).trans
    ((TensorProduct.comm R M (Localization S)).trans
      ((LocalizedModule.equivTensorProduct S M).symm.restrictScalars R))

private theorem tensorLocalizedRingEquiv_mk (S : Submonoid R)
    (M : ModuleCat.{u} R) (m : M) (r : R) :
    tensorLocalizedRingEquiv S M
      (m ⊗ₜ[R] LocalizedModule.mkLinearMap S R r) =
        LocalizedModule.mkLinearMap S M (r • m) := by
  simp only [tensorLocalizedRingEquiv, LinearEquiv.trans_apply,
    TensorProduct.congr_tmul, LinearEquiv.refl_apply,
    IsLocalizedModule.linearEquiv_apply, TensorProduct.comm_tmul,
    LinearEquiv.restrictScalars_apply]
  change (LocalizedModule.equivTensorProduct S M).symm
    (algebraMap R (Localization S) r ⊗ₜ[R] m) =
      LocalizedModule.mkLinearMap S M (r • m)
  change (LocalizedModule.equivTensorProduct S M).symm
    (Localization.mk r (1 : S) ⊗ₜ[R] m) =
      LocalizedModule.mkLinearMap S M (r • m)
  rw [LocalizedModule.equivTensorProduct_symm_apply_tmul]
  exact ((LocalizedModule.mkLinearMap S M).map_smul r m).symm

private def principalTensorCoefficientXIso (x : R) (M : ModuleCat.{u} R) :
    ∀ n : ℕ,
      (((tensorLeft M).mapHomologicalComplex (ComplexShape.up ℕ)).obj
        (principalLocalizationComplex x (ModuleCat.of R R))).X n ≅
          (principalLocalizationComplex x M).X n
  | 0 => ρ_ M
  | 1 => (tensorLocalizedRingEquiv (Submonoid.powers x) M).toModuleIso
  | n + 2 =>
    ((tensorLeft M).map_isZero
      (principalLocalizationComplex_isZero_X x (ModuleCat.of R R) (n + 2) (by omega))).iso
      (principalLocalizationComplex_isZero_X x M (n + 2) (by omega))

/-- Tensoring the principal complex of the ring with a coefficient
module gives its actual principal localization complex. -/
def principalLocalizationTensorCoefficientsIso (x : R) (M : ModuleCat.{u} R) :
    ((tensorLeft M).mapHomologicalComplex (ComplexShape.up ℕ)).obj
      (principalLocalizationComplex x (ModuleCat.of R R)) ≅
        principalLocalizationComplex x M := by
  refine HomologicalComplex.Hom.isoOfComponents
    (principalTensorCoefficientXIso x M) ?_
  intro i j hij
  change i + 1 = j at hij
  subst j
  cases i with
  | zero =>
    apply ModuleCat.hom_ext
    apply TensorProduct.ext'
    intro m r
    exact (tensorLocalizedRingEquiv_mk (Submonoid.powers x) M m r).symm
  | succ i =>
    exact (principalLocalizationComplex_isZero_X x M (i + 1 + 1) (by omega)).eq_of_tgt _ _

end EtaleFundamentalGroups.Purity

end
