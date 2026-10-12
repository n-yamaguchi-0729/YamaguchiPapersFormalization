/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.ProjectiveSpace.Basic
import Nyll.AlgebraicCurves.Geometry.Projective.ProjSpace_exists_algHom_away_apply_ratio_eq
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Algebra.Algebra.Subalgebra.Lattice
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.Tactic.FinCases

/-!
# The affine coordinate chart of the projective line

The degree-zero homogeneous localization of `R[T₀,T₁]` at `T₁` is identified
with `R[t]`, with `t` mapping to `T₀ / T₁`. The inverse is constructed by
evaluating the homogeneous coordinates at `(t, 1)`; equality on coordinate
ratios proves that the maps are inverse. Taking spectra gives the actual
scheme chart, over an arbitrary commutative base ring.

This chart is used in the proof of Proposition 2.5 of Ryoji Shimizu and
Naganori Yamaguchi,
[On branched coverings of the projective line over the integers](https://arxiv.org/abs/2608.15057v1).
-/

noncomputable section

open CategoryTheory AlgebraicGeometry

namespace ShimizuYamaguchi26BranchedCoverings

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The projective line as the projective spectrum of a graded polynomial ring. -/
abbrev ProjectiveLine (R : Type u) [CommRing R] : Scheme.{u} :=
  Proj (MvPolynomial.homogeneousSubmodule (Fin 2) R)

/-- The homogeneous coordinate ring of the chart `T₁ ≠ 0`. -/
abbrev StandardChartRing (R : Type u) [CommRing R] : Type u :=
  HomogeneousLocalization.Away (MvPolynomial.homogeneousSubmodule (Fin 2) R)
    (MvPolynomial.X (1 : Fin 2))

/-- The complement of the section at infinity, defined as a genuine scheme open. -/
def infinityComplement (R : Type u) [CommRing R] : (ProjectiveLine R).Opens :=
  Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin 2) R)
    (MvPolynomial.X (1 : Fin 2))

private theorem standardChart_aeval_bijective (R : Type u) [CommRing R] :
    Function.Bijective (Polynomial.aeval (ProjSpace.ratio R 1 1 0) :
      Polynomial R →ₐ[R] StandardChartRing R) := by
  obtain ⟨φ, hφ⟩ := ProjSpace.exists_algHom_away_apply_ratio_eq R 1 (1 : Fin 2)
    (fun j : Fin 2 => if j = 0 then Polynomial.X else (1 : Polynomial R))
    (by rw [ite_eq_right (by decide : (1 : Fin 2) ≠ 0)])
  let ψ : Polynomial R →ₐ[R] StandardChartRing R :=
    Polynomial.aeval (ProjSpace.ratio R 1 1 0)
  have hleft : φ.comp ψ = AlgHom.id R (Polynomial R) := by
    apply Polynomial.algHom_ext
    change φ (Polynomial.aeval (ProjSpace.ratio R 1 1 0) Polynomial.X) = Polynomial.X
    rw [Polynomial.aeval_X, hφ, ite_eq_left rfl]
  have hright : ψ.comp φ = AlgHom.id R (StandardChartRing R) := by
    apply AlgHom.ext_of_adjoin_eq_top (ProjSpace.adjoin_range_ratio R 1 (1 : Fin 2))
    rintro z ⟨j, rfl⟩
    change Polynomial.aeval (ProjSpace.ratio R 1 1 0) (φ (ProjSpace.ratio R 1 1 j)) =
      ProjSpace.ratio R 1 1 j
    rw [hφ]
    fin_cases j
    · change Polynomial.aeval (ProjSpace.ratio R 1 1 0)
        (if (0 : Fin 2) = 0 then Polynomial.X else 1) = ProjSpace.ratio R 1 1 0
      rw [ite_eq_left rfl, Polynomial.aeval_X]
    · change Polynomial.aeval (ProjSpace.ratio R 1 1 0)
        (if (1 : Fin 2) = 0 then Polynomial.X else 1) = ProjSpace.ratio R 1 1 1
      rw [ite_eq_right (by decide : (1 : Fin 2) ≠ 0), map_one, ProjSpace.ratio_self]
  have hleft' : Function.LeftInverse φ ψ := fun p => DFunLike.congr_fun hleft p
  have hright' : Function.RightInverse φ ψ := fun z => DFunLike.congr_fun hright z
  exact ⟨hleft'.injective, hright'.surjective⟩

/-- The standard chart ring is the polynomial algebra in the ratio `T₀ / T₁`. -/
def standardChartEquiv (R : Type u) [CommRing R] :
    Polynomial R ≃ₐ[R] StandardChartRing R :=
  AlgEquiv.ofBijective (Polynomial.aeval (ProjSpace.ratio R 1 1 0))
    (standardChart_aeval_bijective R)

/-- The affine coordinate maps to the homogeneous coordinate ratio. -/
theorem standardChartEquiv_X (R : Type u) [CommRing R] :
    standardChartEquiv R Polynomial.X = ProjSpace.ratio R 1 1 0 := by
  rw [standardChartEquiv, AlgEquiv.ofBijective_apply, Polynomial.aeval_X]

/-- The standard chart is the spectrum of a one-variable polynomial ring. -/
def standardAffineChartIso (R : Type u) [CommRing R] :
    (infinityComplement R).toScheme ≅ Spec (CommRingCat.of (Polynomial R)) :=
  Proj.basicOpenIsoSpec (MvPolynomial.homogeneousSubmodule (Fin 2) R)
      (MvPolynomial.X (1 : Fin 2)) (ProjSpace.X_mem_one R 1 1) one_pos ≪≫
    Scheme.Spec.mapIso (standardChartEquiv R).toRingEquiv.toCommRingCatIso.op

/-- The usual affine chart as a morphism into the actual projective line. -/
def standardChartEmbedding (R : Type u) [CommRing R] :
    Spec (CommRingCat.of (Polynomial R)) ⟶ ProjectiveLine R :=
  (Scheme.Spec.mapIso (standardChartEquiv R).toRingEquiv.toCommRingCatIso.op).inv ≫
    Proj.awayι (MvPolynomial.homogeneousSubmodule (Fin 2) R)
      (MvPolynomial.X (1 : Fin 2)) (ProjSpace.X_mem_one R 1 1) one_pos

instance (R : Type u) [CommRing R] : IsOpenImmersion (standardChartEmbedding R) := by
  unfold standardChartEmbedding
  infer_instance

/-- The image of the affine chart is exactly the complement of infinity. -/
theorem standardChartEmbedding_opensRange (R : Type u) [CommRing R] :
    (standardChartEmbedding R).opensRange = infinityComplement R := by
  unfold standardChartEmbedding infinityComplement
  rw [Scheme.Hom.opensRange_comp_of_isIso, Proj.opensRange_awayι]

end ShimizuYamaguchi26BranchedCoverings
