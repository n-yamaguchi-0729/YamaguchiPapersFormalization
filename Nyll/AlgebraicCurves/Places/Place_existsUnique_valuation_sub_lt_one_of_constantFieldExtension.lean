/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_Place_existsUnique_valuation_sub_lt_one_of_constantFieldExtension.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Divisors.ClassGroup
import Nyll.AlgebraicCurves.FunctionFields.CurveOver
import Nyll.AlgebraicCurves.Places.Place_eq_of_forall_valuation_sub_lt_one_of_constantFieldExtension
import Nyll.AlgebraicCurves.FunctionFields.LinearIndependent_of_constantFieldExtension
import Nyll.AlgebraicCurves.Places.Place_exists_of_valuationSubring

/-!
# Place exists Unique valuation sub lt one of constant Field Extension
-/

section ProofImplementation

namespace AlgebraicCurves.Places.Proofs
namespace Place_existsUnique_valuation_sub_lt_one_of_constantFieldExtension
attribute [-instance] AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia
  AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward
  AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward
  AlgebraicCurve.Place.instIsLocalHomRestrictInclusion
  AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation
  AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation
  AlgebraicCurve.RationalFunctionField.instNontrivialInftyValueGroup
attribute [-simp] AlgebraicCurve.Divisor.mapRestrict_single
  AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion
  AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring
  AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue
  AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom
  AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one
  AlgebraicCurve.Place.congrEquiv_symm_apply
  AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal
  AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply
  AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply
  AlgebraicCurve.RationalFunctionField.deg_placeOfPoint
  AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring
attribute [-simp] AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty
  AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some
  AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint
  AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none

open _root_.AlgebraicCurve
open scoped TensorProduct

namespace AlgebraicCurve
open _root_.AlgebraicCurve
namespace PointPlaceDictionary
open _root_.AlgebraicCurve

variable {K F E FE : Type*} [Field K] [Field F] [Algebra K F] [Field E] [Field FE]
  [Algebra K E] [Algebra E FE] [Algebra F FE] [Algebra K FE] [IsScalarTower K E FE]
  [IsScalarTower K F FE]

variable (K F E FE) in
/-- The tensor-product map multiplying the images of the two fields in their common extension. -/
noncomputable def mulMap : E ⊗[K] F →ₐ[E] FE :=
  Algebra.TensorProduct.lift (Algebra.ofId E FE) (IsScalarTower.toAlgHom K F FE)
    (fun _ _ => Commute.all _ _)
@[scoped simp]
theorem mulMap_tmul (c : E) (f : F) :
    mulMap K F E FE (c ⊗ₜ f) = algebraMap E FE c * algebraMap F FE f := rfl

/-- The tensor-product evaluation map induced by the given base-field embedding. -/
noncomputable def evalMap (e : F →ₐ[K] E) : E ⊗[K] F →ₐ[E] E :=
  Algebra.TensorProduct.lift (AlgHom.id E E) e (fun _ _ => Commute.all _ _)
@[scoped simp]
theorem evalMap_tmul (e : F →ₐ[K] E) (c : E) (f : F) : evalMap e (c ⊗ₜ f) = c * e f := rfl

theorem mulMap_injective
    (hli : LinearIndependent E (fun i => algebraMap F FE (Module.Basis.ofVectorSpace K F i))) :
    Function.Injective (mulMap K F E FE) := by
  classical
  let bE := Algebra.TensorProduct.basis E (Module.Basis.ofVectorSpace K F)
  rw [injective_iff_map_eq_zero]
  intro z hz
  have hrepr : Finsupp.linearCombination E bE (bE.repr z) = z := bE.linearCombination_repr z
  have hcomp : ((mulMap K F E FE).toLinearMap : E ⊗[K] F →ₗ[E] FE) ∘ bE =
      fun i => algebraMap F FE (Module.Basis.ofVectorSpace K F i) := by
    funext i
    simp [bE, Algebra.TensorProduct.basis_apply]
  have h0 : Finsupp.linearCombination E (fun i => algebraMap F FE (Module.Basis.ofVectorSpace K F
    i))
      (bE.repr z) = 0 := by
    rw [← hcomp, ← Finsupp.apply_linearCombination, hrepr]
    exact hz
  have hc : bE.repr z = 0 := hli (by rw [map_zero]; exact h0)
  rw [← hrepr, hc, map_zero]

theorem exists_centred [IsAlgClosed K] [CharZero K]
    (hfg : ∃ x : F, Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (hfgE : ∃ x : FE, Transcendental E x ∧
      FiniteDimensional (IntermediateField.adjoin E ({x} : Set FE)) FE)
    (hgen : IntermediateField.adjoin E (Set.range (algebraMap F FE)) = ⊤)
    (e : F →ₐ[K] E) :
    ∃ P : Place E FE, ∀ f : F,
      P.toValuationSubring.valuation (algebraMap F FE f - algebraMap E FE (e f)) < 1 := by
  classical
  have hinj : Function.Injective (mulMap K F E FE) :=
    mulMap_injective (linearIndependent_of_constantFieldExtension K F E FE hfg hfgE hgen
      (Module.Basis.ofVectorSpace K F).linearIndependent)
  let ε : (E ⊗[K] F) ≃ₐ[E] (mulMap K F E FE).range := AlgEquiv.ofInjective _ hinj
  let θ : (mulMap K F E FE).range →ₐ[E] E :=
    (evalMap e).comp (ε.symm : (mulMap K F E FE).range →ₐ[E] E ⊗[K] F)
  let I : Ideal (mulMap K F E FE).range := RingHom.ker θ.toRingHom
  have hI : I ≠ ⊤ := RingHom.ker_ne_top θ.toRingHom
  obtain ⟨B, hRB, hIB⟩ :=
    Ideal.image_subset_nonunits_valuationSubring (A := (mulMap K F E FE).range.toSubring) I hI
  have hEB : ∀ c : E, algebraMap E FE c ∈ B := fun c =>
    hRB ((mulMap K F E FE).range.algebraMap_mem c)
  have hval : ∀ f : F, mulMap K F E FE (1 ⊗ₜ f - algebraMap E (E ⊗[K] F) (e f)) =
      algebraMap F FE f - algebraMap E FE (e f) := fun f => by
    rw [map_sub, AlgHom.commutes, mulMap_tmul, map_one, one_mul]
  have hmemR : ∀ f : F, algebraMap F FE f - algebraMap E FE (e f) ∈ (mulMap K F E FE).range :=
    fun f => (AlgHom.mem_range _).mpr ⟨_, hval f⟩
  have hcen : ∀ f : F, B.valuation (algebraMap F FE f - algebraMap E FE (e f)) < 1 := by
    intro f
    rw [← ValuationSubring.mem_nonunits_iff]
    refine hIB ⟨⟨_, hmemR f⟩, ?_, rfl⟩
    change θ ⟨_, hmemR f⟩ = 0
    have hsymm : ε.symm ⟨_, hmemR f⟩ = 1 ⊗ₜ f - algebraMap E (E ⊗[K] F) (e f) := by
      rw [AlgEquiv.symm_apply_eq]
      apply Subtype.ext
      exact (hval f).symm
    change evalMap e (ε.symm ⟨_, hmemR f⟩) = 0
    rw [hsymm, map_sub, evalMap_tmul, one_mul, AlgHom.commutes, Algebra.algebraMap_self,
      RingHom.id_apply, sub_self]
  obtain ⟨x, hx, -⟩ := id hfg
  have hli : LinearIndependent K ![(1 : F), x] := by
    refine LinearIndependent.pair_iff.2 fun s t hst => ?_
    by_cases ht : t = 0
    · subst ht
      simp only [zero_smul, add_zero, smul_eq_zero, one_ne_zero, or_false] at hst
      exact ⟨hst, rfl⟩
    · exfalso
      apply hx
      have ht' : algebraMap K F t ≠ 0 := (map_ne_zero _).2 ht
      have hx' : x = algebraMap K F (-s / t) := by
        rw [Algebra.smul_def, Algebra.smul_def, mul_one] at hst
        rw [map_div₀, map_neg, eq_div_iff ht', mul_comm]
        exact eq_neg_of_add_eq_zero_right hst
      rw [hx']
      exact isAlgebraic_algebraMap _
  have hxE : algebraMap F FE x ∉ (algebraMap E FE).range := by
    have hli' := linearIndependent_of_constantFieldExtension K F E FE hfg hfgE hgen hli
    have h2 : LinearIndependent E ![algebraMap F FE 1, algebraMap F FE x] := by
      convert hli' using 1
      ext j
      fin_cases j <;> rfl
    rw [LinearIndependent.pair_iff] at h2
    rintro ⟨c, hc⟩
    have := h2 c (-1) (by
      rw [map_one, ← hc, Algebra.smul_def, mul_one, neg_one_smul, add_neg_cancel])
    exact absurd this.2 (by norm_num)
  have htne : algebraMap F FE x - algebraMap E FE (e x) ≠ 0 := fun h =>
    hxE ⟨e x, (sub_eq_zero.mp h).symm⟩
  have hBtop : B ≠ ⊤ := by
    intro hB
    have hmem := (ValuationSubring.mem_nonunits_iff (A := B)).mpr (hcen x)
    rcases (ValuationSubring.mem_nonunits_iff_or (A := B)).mp hmem with h0 | hinv
    · exact htne h0
    · exact hinv (hB ▸ ValuationSubring.mem_top _)
  obtain ⟨x₀, -, hx₀fin⟩ := id hfgE
  have := hx₀fin
  have : CharZero E := charZero_of_injective_algebraMap (algebraMap K E).injective
  obtain ⟨P, hP⟩ := Place.exists_of_valuationSubring (K := E) x₀ B hEB hBtop
  exact ⟨P, fun f => by rw [hP]; exact hcen f⟩

theorem exists_centre_of_forall_mem [IsAlgClosed E] [IsCurveOver E FE] (P : Place E FE)
    (hP : ∀ f : F, algebraMap F FE f ∈ P.toValuationSubring) :
    ∃ e : F →ₐ[K] E, ∀ f : F,
      P.toValuationSubring.valuation (algebraMap F FE f - algebraMap E FE (e f)) < 1 := by
  classical
  have : Module.Finite E P.ResidueField := IsCurveOver.finiteResidue P
  have : Algebra.IsIntegral E P.ResidueField := Algebra.IsIntegral.of_finite E P.ResidueField
  have hbij : Function.Bijective (algebraMap E P.ResidueField) :=
    IsAlgClosed.algebraMap_bijective_of_isIntegral
  let ρ : E ≃+* P.ResidueField := RingEquiv.ofBijective (algebraMap E P.ResidueField) hbij
  let ι : F →+* P.toValuationSubring := (algebraMap F FE).codRestrict P.toValuationSubring hP
  let r : F →+* P.ResidueField := (IsLocalRing.residue P.toValuationSubring).comp ι
  have hρ : ∀ c : E, ρ c = IsLocalRing.residue _ (algebraMap E P.toValuationSubring c) :=
    fun c => rfl
  have hr : ∀ a : K, r (algebraMap K F a) = ρ (algebraMap K E a) := by
    intro a
    rw [hρ]
    change IsLocalRing.residue _ (ι (algebraMap K F a)) = _
    congr 1
    apply Subtype.ext
    change algebraMap F FE (algebraMap K F a) = (algebraMap E P.toValuationSubring _ : FE)
    rw [Place.coe_algebraMap, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
  let e : F →ₐ[K] E :=
    { ρ.symm.toRingHom.comp r with
      commutes' := fun a => by
        change ρ.symm (r (algebraMap K F a)) = algebraMap K E a
        rw [hr, RingEquiv.symm_apply_apply] }
  refine ⟨e, fun f => ?_⟩
  have he : ρ (e f) = r f := by
    change ρ (ρ.symm (r f)) = r f
    exact ρ.apply_symm_apply _
  have hmem : (⟨algebraMap F FE f, hP f⟩ - algebraMap E P.toValuationSubring (e f) :
      P.toValuationSubring) ∈ IsLocalRing.maximalIdeal P.toValuationSubring := by
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub, ← hρ, he, sub_eq_zero]
    rfl
  have := (ValuationSubring.valuation_lt_one_iff _ _).mp hmem
  simpa [Place.coe_algebraMap] using this

end AlgebraicCurve.PointPlaceDictionary

open AlgebraicCurve.PointPlaceDictionary in
theorem _root_.AlgebraicCurve.Place.existsUnique_valuation_sub_lt_one_of_constantFieldExtension
    (K F : Type*) [Field K] [Field F] [Algebra K F] [IsAlgClosed K] [CharZero K] [IsCurveOver K F]
    (hfg : ∃ x : F, Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (E FE : Type*) [Field E] [Field FE] [Algebra K E] [Algebra E FE] [Algebra F FE] [Algebra K FE]
    [IsScalarTower K E FE] [IsScalarTower K F FE] [IsAlgClosed E] [IsCurveOver E FE]
    (hfgE : ∃ x : FE, Transcendental E x ∧
      FiniteDimensional (IntermediateField.adjoin E ({x} : Set FE)) FE)
    (hgen : IntermediateField.adjoin E (Set.range (algebraMap F FE)) = ⊤) :
    (∀ e : F →ₐ[K] E, ∃! P : Place E FE, ∀ f : F,
        P.toValuationSubring.valuation (algebraMap F FE f - algebraMap E FE (e f)) < 1) ∧
    (∀ P : Place E FE, (∀ f : F, algebraMap F FE f ∈ P.toValuationSubring) →
      ∃ e : F →ₐ[K] E, ∀ f : F,
        P.toValuationSubring.valuation (algebraMap F FE f - algebraMap E FE (e f)) < 1) := by
  refine ⟨fun e => ?_, fun P hP => exists_centre_of_forall_mem P hP⟩
  obtain ⟨P, hP⟩ := exists_centred hfg hfgE hgen e
  exact ⟨P, hP, fun Q hQ =>
    Place.eq_of_forall_valuation_sub_lt_one_of_constantFieldExtension K F hfg E FE hfgE hgen e
      Q P hQ hP⟩
end AlgebraicCurves.Places.Proofs.Place_existsUnique_valuation_sub_lt_one_of_constantFieldExtension
end ProofImplementation
