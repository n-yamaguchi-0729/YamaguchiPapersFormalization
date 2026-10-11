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

import Mathlib.RingTheory.Polynomial.RationalRoot
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.RingTheory.NoetherNormalization

import Nyll.AlgebraicCurves.Foundations.CommutativeAlgebra.Ideal_height_eq_height_under_of_isIntegrallyClosed_of_isIntegral

/-!
# Ideal height eq height under of finite Type of is Integral
-/

section ProofImplementation

namespace AlgebraicCurves.Foundations.CommutativeAlgebra.Proofs
namespace Ideal_height_eq_height_under_of_finiteType_of_isIntegral

universe u

theorem _root_.Ideal.height_eq_height_under_of_finiteType_of_isIntegral
    (k A B : Type u) [Field k] [CommRing A] [IsDomain A] [Algebra k A] [Algebra.FiniteType k A]
    [CommRing B] [IsDomain B] [Algebra k B] [Algebra.FiniteType k B]
    [Algebra A B] [IsScalarTower k A B] [FaithfulSMul A B] [Algebra.IsIntegral A B]
    (q : Ideal B) [q.IsPrime] :
    q.height = (q.under A).height := by
  have : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing k A
  have : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing k B
  obtain ⟨d, g, hinj, hint⟩ := exists_integral_inj_algHom_of_fg k A
  let : Algebra (MvPolynomial (Fin d) k) A := g.toRingHom.toAlgebra
  let : Algebra (MvPolynomial (Fin d) k) B := ((algebraMap A B).comp g.toRingHom).toAlgebra
  have : IsScalarTower (MvPolynomial (Fin d) k) A B := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have : FaithfulSMul (MvPolynomial (Fin d) k) A :=
    (faithfulSMul_iff_algebraMap_injective _ A).mpr hinj
  have : FaithfulSMul (MvPolynomial (Fin d) k) B :=
    (faithfulSMul_iff_algebraMap_injective _ B).mpr
      ((FaithfulSMul.algebraMap_injective A B).comp hinj)
  have : Algebra.IsIntegral (MvPolynomial (Fin d) k) A := ⟨hint⟩
  have : Algebra.IsIntegral (MvPolynomial (Fin d) k) B := Algebra.IsIntegral.trans A
  rw [Ideal.height_eq_height_under_of_isIntegrallyClosed_of_isIntegral (MvPolynomial (Fin d) k) B q,
    Ideal.height_eq_height_under_of_isIntegrallyClosed_of_isIntegral (MvPolynomial (Fin d) k) A
      (q.under A), Ideal.under_under]
end Ideal_height_eq_height_under_of_finiteType_of_isIntegral
end AlgebraicCurves.Foundations.CommutativeAlgebra.Proofs
end ProofImplementation
