/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_linearIndependent_algebraMap_of_constantsAreBase_of_isAlgebraic.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.RingTheory.Valuation.Integral

import Nyll.AlgebraicCurves.Divisors.ClassGroup
import Nyll.AlgebraicCurves.Cohomology.Adelic.Index
import Nyll.AlgebraicCurves.Foundations.FieldTheory.Algebra_TensorProduct_isField_of_isSeparable_of_forall_isAlgebraic_mem_range

/-!
# Linear Independent algebra Map of constants Are Base of is Algebraic
-/

section ProofImplementation

namespace AlgebraicCurves.FunctionFields.Proofs
namespace LinearIndependent_algebraMap_of_constantsAreBase_of_isAlgebraic

open AlgebraicCurve
open scoped TensorProduct

namespace LdCab

open AlgebraicCurve

theorem mem_range_of_isAlgebraic {K F : Type*} [Field K] [Field F] [Algebra K F] (hC :
  AlgebraicCurve.ConstantsAreBase K F)
    (y : F) (hy : IsAlgebraic K y) : y ∈ (algebraMap K F).range := by
  have hint : IsIntegral K y := hy.isIntegral
  have hmem : y ∈ AlgebraicCurve.LSpace (0 : Divisor K F) := by
    rw [AlgebraicCurve.mem_lSpace_iff]
    intro v
    have hI : v.toValuationSubring.valuation.Integers ↥v.toValuationSubring :=
      { hom_inj := Subtype.val_injective
        map_le_one := fun a => (v.toValuationSubring.valuation_le_one_iff _).mpr a.2
        exists_of_le_one := fun r hr => ⟨⟨r, (v.toValuationSubring.valuation_le_one_iff _).mp hr⟩,
          rfl⟩ }
    have hint' : IsIntegral ↥v.toValuationSubring y := hint.tower_top
    have hyv : y ∈ v.toValuationSubring := by
      have := Valuation.Integers.mem_of_integral hI hint'
      rw [Valuation.mem_integer_iff, ValuationSubring.valuation_le_one_iff] at this
      exact this
    rw [Finsupp.coe_zero, Pi.zero_apply, WithZero.exp_zero]
    have := v.adicValuation_coe ⟨y, hyv⟩
    rw [this]
    exact IsDedekindDomain.HeightOneSpectrum.intValuation_le_one _ _
  rw [hC] at hmem
  obtain ⟨c, hc⟩ := hmem
  exact ⟨c, hc⟩

end LdCab

open LdCab in
theorem _root_.AlgebraicCurve.linearIndependent_algebraMap_of_constantsAreBase_of_isAlgebraic
    (K F K' F' : Type*)
    [Field K] [Field F] [Field K'] [Field F'] [Algebra K F] [Algebra K' F']
    [Algebra K K'] [Algebra F F'] [Algebra K F'] [IsScalarTower K K' F'] [IsScalarTower K F F']
    [PerfectField K] [Algebra.IsAlgebraic K K']
    (hC : AlgebraicCurve.ConstantsAreBase K F)
    {ι : Type*} {b : ι → F} (hb : LinearIndependent K b) :
    LinearIndependent K' (fun i => algebraMap F F' (b i)) := by
  classical
  have hconst : ∀ y : F, IsAlgebraic K y → y ∈ (algebraMap K F).range := mem_range_of_isAlgebraic hC
  have : Algebra.IsSeparable K K' := Algebra.IsAlgebraic.isSeparable_of_perfectField
  have hfield : IsField (F ⊗[K] K') :=
    Algebra.TensorProduct.isField_of_isSeparable_of_forall_isAlgebraic_mem_range K F K' hconst
  have hfield' : IsField (K' ⊗[K] F) := MulEquiv.isField hfield (Algebra.TensorProduct.comm K K'
    F).toMulEquiv
  let : Field (K' ⊗[K] F) := hfield'.toField
  let ψ : K' ⊗[K] F →ₐ[K'] F' := Algebra.TensorProduct.lift (Algebra.ofId K' F')
    (IsScalarTower.toAlgHom K F F') (fun _ _ => Commute.all _ _)
  have hψ : ∀ f : F, ψ ((1 : K') ⊗ₜ[K] f) = algebraMap F F' f := by
    intro f
    change Algebra.TensorProduct.lift _ _ _ ((1 : K') ⊗ₜ[K] f) = _
    rw [Algebra.TensorProduct.lift_tmul]
    simp [Algebra.ofId_apply]
  have hψinj : Function.Injective ψ := RingHom.injective ψ.toRingHom
  have hψker : LinearMap.ker ψ.toLinearMap = ⊥ := LinearMap.ker_eq_bot.mpr hψinj
  let M : Submodule K F := Submodule.span K (Set.range b)
  let bM : Module.Basis ι K M := Module.Basis.span hb
  let B := Algebra.TensorProduct.basis K' bM
  have hincl : Function.Injective (M.subtype.baseChange K') := by
    show Function.Injective ((M.subtype.baseChange K' : K' ⊗[K] M →ₗ[K'] K' ⊗[K] F) : K' ⊗[K] M →
      K' ⊗[K] F)
    rw [LinearMap.baseChange_eq_ltensor]
    exact Module.Flat.lTensor_preserves_injective_linearMap M.subtype (Submodule.injective_subtype
      M)
  have hli1 : LinearIndependent K' ((M.subtype.baseChange K') ∘ B) := B.linearIndependent.map' _
    (LinearMap.ker_eq_bot.mpr hincl)
  have hli2 : LinearIndependent K' (ψ.toLinearMap ∘ ((M.subtype.baseChange K') ∘ B)) := hli1.map' _
    hψker
  convert hli2 using 1
  funext i
  simp only [Function.comp_apply]
  rw [show B i = (1 : K') ⊗ₜ[K] (bM i) from Algebra.TensorProduct.basis_apply bM i,
    LinearMap.baseChange_tmul, Submodule.subtype_apply,
    show ((bM i : M) : F) = b i from congrArg Subtype.val (Module.Basis.span_apply hb i)]
  exact (hψ (b i)).symm
end LinearIndependent_algebraMap_of_constantsAreBase_of_isAlgebraic
end AlgebraicCurves.FunctionFields.Proofs
end ProofImplementation
