/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Anthropic FLT source material is identified by code comparison;
the exact source-file correspondence remains unresolved.
Upstream repository: https://github.com/anthropics/fermats-last-theorem
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.RingTheory.RingHom.StandardSmooth
import AlgebraicCurves.Foundations.Algebra.Algebra_IsStandardSmooth_exists_isStandardSmoothOfRelativeDimension_of_field
import AlgebraicCurves.Foundations.CommutativeAlgebra.isRegularLocalRing_localization_atPrime_mvPolynomial
import AlgebraicCurves.Foundations.CommutativeAlgebra.isRegularLocalRing_localization_atPrime_of_etale_of_comap
import AlgebraicCurves.Foundations.CommutativeAlgebra.Mathlib_RingTheory_SmoothAlgebraOverFieldRegularStalks
import AlgebraicCurves.Foundations.CommutativeAlgebra.Mathlib_RingTheory_SmoothFieldFiberRegularStalksStandardSmoothReduction

/-!
# is Regular Local Ring localization at Prime of is Standard Smooth
-/

section ProofImplementation

namespace AlgebraicCurves.Foundations.CommutativeAlgebra.Proofs
namespace isRegularLocalRing_localization_atPrime_of_isStandardSmooth

theorem _root_.isRegularLocalRing_localization_atPrime_of_isStandardSmooth
    (k B : Type*) [Field k] [CommRing B] [Algebra k B]
    [Algebra.IsStandardSmooth k B] (q : Ideal B) [q.IsPrime] :
    IsRegularLocalRing (Localization.AtPrime q) := by
  classical
  obtain ⟨m, hm⟩ :=
    Algebra.IsStandardSmooth.exists_isStandardSmoothOfRelativeDimension_of_field (k := k) (B := B)
  have := hm
  obtain ⟨g, hg⟩ := Algebra.IsStandardSmoothOfRelativeDimension.exists_etale_mvPolynomial m k B
  let : Algebra (MvPolynomial (Fin m) k) B := g.toRingHom.toAlgebra
  have : Algebra.Etale (MvPolynomial (Fin m) k) B := hg
  have : IsScalarTower k (MvPolynomial (Fin m) k) B :=
    IsScalarTower.of_algebraMap_eq fun c => (g.commutes c).symm
  have hbase := isRegularLocalRing_localization_atPrime_mvPolynomial k m
    (q.comap (algebraMap (MvPolynomial (Fin m) k) B))
  exact isRegularLocalRing_localization_atPrime_of_etale_of_comap
    (MvPolynomial (Fin m) k) B q hbase
end isRegularLocalRing_localization_atPrime_of_isStandardSmooth
end AlgebraicCurves.Foundations.CommutativeAlgebra.Proofs
end ProofImplementation
