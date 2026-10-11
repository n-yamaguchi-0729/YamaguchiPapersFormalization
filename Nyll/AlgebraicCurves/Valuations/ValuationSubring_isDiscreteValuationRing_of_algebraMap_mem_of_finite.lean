/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_ValuationSubring_isDiscreteValuationRing_of_algebraMap_mem_of_finite.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.RingTheory.DiscreteValuationRing.TFAE

import Nyll.AlgebraicCurves.Foundations.CommutativeAlgebra.Subalgebra_isNoetherianRing_and_dimensionLEOne_of_isFractionRing_of_finite

/-!
# Valuation Subring is Discrete Valuation Ring of algebra Map mem of finite
-/

section ProofImplementation

namespace AlgebraicCurves.Valuations.Proofs
namespace ValuationSubring_isDiscreteValuationRing_of_algebraMap_mem_of_finite

namespace KrullAkizukiDVR

theorem main {A K L : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A] [Ring.KrullDimLE 1 A]
    [Field K] [Algebra A K] [IsFractionRing A K]
    [Field L] [Algebra A L] [Algebra K L] [IsScalarTower A K L] [Module.Finite K L]
    (O : ValuationSubring L) (hA : ∀ a : A, algebraMap A L a ∈ O) (hO : O ≠ ⊤) :
    IsDiscreteValuationRing O := by
  let B : Subalgebra A L :=
    { carrier := O
      mul_mem' := fun ha hb => O.mul_mem _ _ ha hb
      one_mem' := O.one_mem
      add_mem' := fun ha hb => O.add_mem _ _ ha hb
      zero_mem' := O.zero_mem
      algebraMap_mem' := hA }
  have hB := Subalgebra.isNoetherianRing_and_dimensionLEOne_of_isFractionRing_of_finite (K := K) B
  let _ : IsNoetherianRing B := hB.1
  let e : B ≃+* O :=
    { toFun := fun x => ⟨x.1, x.2⟩
      invFun := fun x => ⟨x.1, x.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl
      map_add' := fun _ _ => rfl }
  let _ : IsNoetherianRing O := isNoetherianRing_of_ringEquiv B e
  have hnf : ¬ IsField O := by
    intro hF
    apply hO
    rw [eq_top_iff]
    intro x _
    by_contra hx
    have hx0 : x ≠ 0 := by
      rintro rfl
      exact hx O.zero_mem
    have hxinv : x⁻¹ ∈ O := (O.mem_or_inv_mem x).resolve_left hx
    have hne : (⟨x⁻¹, hxinv⟩ : O) ≠ 0 := by
      intro h
      apply hx0
      have := congrArg Subtype.val h
      simpa using this
    obtain ⟨y, hy⟩ := hF.mul_inv_cancel hne
    have hy' : x⁻¹ * (y : L) = 1 := by
      have := congrArg Subtype.val hy
      simpa using this
    have hyx : (y : L) = x := by
      have h1 : x * (x⁻¹ * (y : L)) = x := by rw [hy', mul_one]
      rwa [← mul_assoc, mul_inv_cancel₀ hx0, one_mul] at h1
    exact hx (hyx ▸ y.2)
  let _ : IsLocalRing O := inferInstance
  let _ : ValuationRing O := inferInstance
  have htfae := IsDiscreteValuationRing.TFAE O hnf
  exact (htfae.out 1 2).mpr ‹ValuationRing O›

end KrullAkizukiDVR

theorem _root_.ValuationSubring.isDiscreteValuationRing_of_algebraMap_mem_of_finite
    {A K L : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A] [Ring.KrullDimLE 1 A]
    [Field K] [Algebra A K] [IsFractionRing A K]
    [Field L] [Algebra A L] [Algebra K L] [IsScalarTower A K L] [Module.Finite K L]
    (O : ValuationSubring L) (hA : ∀ a : A, algebraMap A L a ∈ O) (hO : O ≠ ⊤) :
    IsDiscreteValuationRing O :=
  KrullAkizukiDVR.main (K := K) O hA hO
end ValuationSubring_isDiscreteValuationRing_of_algebraMap_mem_of_finite
end AlgebraicCurves.Valuations.Proofs
end ProofImplementation
