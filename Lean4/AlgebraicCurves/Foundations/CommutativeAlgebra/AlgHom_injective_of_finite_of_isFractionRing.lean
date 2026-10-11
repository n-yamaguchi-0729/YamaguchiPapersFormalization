/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgHom_injective_of_finite_of_isFractionRing.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import AlgebraicCurves.Foundations.Algebra.Algebra_trdeg_quotient_lt

/-!
# Alg Hom injective of finite of is Fraction Ring
-/

section ProofImplementation

namespace AlgebraicCurves.Foundations.CommutativeAlgebra.Proofs
namespace AlgHom_injective_of_finite_of_isFractionRing

universe u

theorem _root_.AlgHom.injective_of_finite_of_isFractionRing {k A B K : Type u} [Field k]
    [CommRing A] [IsDomain A] [Algebra k A] [Algebra.FiniteType k A]
    [CommRing B] [IsDomain B] [Algebra k B] [Algebra.FiniteType k B]
    [Field K] [Algebra k K] [Algebra A K] [IsFractionRing A K] [IsScalarTower k A K]
    [Algebra B K] [IsFractionRing B K] [IsScalarTower k B K]
    (φ : A →ₐ[k] B) (hφ : φ.toRingHom.Finite) : Function.Injective φ := by
  have : FaithfulSMul k A := (faithfulSMul_iff_algebraMap_injective k A).mpr (algebraMap k
    A).injective
  have : FaithfulSMul k B := (faithfulSMul_iff_algebraMap_injective k B).mpr (algebraMap k
    B).injective
  have : FaithfulSMul A K := (faithfulSMul_iff_algebraMap_injective A K).mpr
    (IsFractionRing.injective A K)
  have : FaithfulSMul B K := (faithfulSMul_iff_algebraMap_injective B K).mpr
    (IsFractionRing.injective B K)
  have algAK : Algebra.IsAlgebraic A K := IsLocalization.isAlgebraic K (nonZeroDivisors A)
  have algBK : Algebra.IsAlgebraic B K := IsLocalization.isAlgebraic K (nonZeroDivisors B)
  have h1 := trdeg_add_eq k A (A := K)
  have h2 := trdeg_add_eq k B (A := K)
  rw [trdeg_eq_zero_iff.mpr algAK, add_zero] at h1
  rw [trdeg_eq_zero_iff.mpr algBK, add_zero] at h2
  have hAB : Algebra.trdeg k A = Algebra.trdeg k B := h1.trans h2.symm
  by_contra hnot
  set I : Ideal A := RingHom.ker φ.toRingHom with hIdef
  have hI : I ≠ ⊥ := by
    intro hbot
    apply hnot
    intro x y hxy
    have : x - y ∈ I :=
      by rw [RingHom.mem_ker, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_sub, hxy, sub_self]
    rw [hbot, Ideal.mem_bot, sub_eq_zero] at this
    exact this
  have hI' : I ≠ ⊤ := RingHom.ker_ne_top φ.toRingHom
  have : Nontrivial (A ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hI'
  let algAB : Algebra A B := φ.toRingHom.toAlgebra
  have : Module.Finite A B := hφ
  let : Algebra (A ⧸ I) B := (RingHom.kerLift φ.toRingHom).toAlgebra
  have : IsScalarTower A (A ⧸ I) B :=
    IsScalarTower.of_algebraMap_eq (fun a => (RingHom.kerLift_mk φ.toRingHom a).symm)
  have : IsScalarTower k (A ⧸ I) B := IsScalarTower.of_algebraMap_eq (fun x => by
    change algebraMap k B x = RingHom.kerLift φ.toRingHom (Ideal.Quotient.mk I (algebraMap k A x))
    rw [RingHom.kerLift_mk]
    exact (φ.commutes x).symm)
  have : FaithfulSMul (A ⧸ I) B :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (RingHom.kerLift_injective φ.toRingHom)
  have : FaithfulSMul k (A ⧸ I) :=
    (faithfulSMul_iff_algebraMap_injective k _).mpr (algebraMap k (A ⧸ I)).injective
  have : Module.Finite (A ⧸ I) B := Module.Finite.of_restrictScalars_finite A (A ⧸ I) B
  have algB : Algebra.IsAlgebraic (A ⧸ I) B := Algebra.IsIntegral.isAlgebraic
  have h3 := trdeg_add_eq k (A ⧸ I) (A := B)
  rw [trdeg_eq_zero_iff.mpr algB, add_zero] at h3
  have hlt : Algebra.trdeg k (A ⧸ I) < Algebra.trdeg k A := Algebra.trdeg_quotient_lt (K := k) I hI
    hI'
  rw [h3, ← hAB] at hlt
  exact lt_irrefl _ hlt
end AlgHom_injective_of_finite_of_isFractionRing
end AlgebraicCurves.Foundations.CommutativeAlgebra.Proofs
end ProofImplementation
