/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_finsum_ramificationIndexAlong_sub_one_eq.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.Polynomial.AlgebraMap
import AlgebraicCurves.FunctionFields.CurveOver
import AlgebraicCurves.Divisors.Canonical
import AlgebraicCurves.Differentials.Regular
import AlgebraicCurves.Divisors.Correspondences
import AlgebraicCurves.Divisors.ClassGroup
import AlgebraicCurves.Divisors.Maps
import AlgebraicCurves.Differentials.Residues.Canonical
import AlgebraicCurves.Cohomology.RiemannRoch.Finite_and_finrank_regularDifferentials_eq_genus
import AlgebraicCurves.Differentials.DCoordGenerates_of_isCurveOver
import AlgebraicCurves.Divisors.HasPrincipalDivisors_of_transcendental
import AlgebraicCurves.Differentials.LocalUnitDerivativeRegular_of_isCurveOver
import AlgebraicCurves.Places.Place_deg_ne_zero_of_finiteDimensional_adjoin
import AlgebraicCurves.Geometry.Exists_D_ne_zero
import AlgebraicCurves.Differentials.Kaehler.KaehlerDifferential_D_ne_zero_of_transcendental
import AlgebraicCurves.FunctionFields.EssFiniteType_of_transcendental_of_finiteDimensional
import AlgebraicCurves.Divisors.HasCanonicalDivisor_of_isCurveOver
import AlgebraicCurves.Cohomology.RiemannRoch.StichtenothGenusExists_of_isCurveOver
import AlgebraicCurves.Cohomology.RiemannRoch.Two_mul_genus_sub_two_eq_of_degree_canonical
import AlgebraicCurves.Cohomology.RiemannRoch.FunctionFieldRiemannRoch_of_isAlgClosed
import AlgebraicCurves.FunctionFields.InstIsCurveOverRatFunc
import AlgebraicCurves.Divisors.InstHasCanonicalDivisorRatFuncPerfectField
import AlgebraicCurves.Cohomology.RiemannRoch.Genus_ratFunc_eq_zero
import AlgebraicCurves.Places.Place_deg_eq_one_of_isAlgClosed
import AlgebraicCurves.FunctionFields.ConstantsAreBase_of_isAlgClosed
import AlgebraicCurves.Divisors.Degree_canonicalDivisor_eq_of_isAlgClosed
import AlgebraicCurves.FunctionFields.IsCurveOver_of_transcendental_of_perfectField
import AlgebraicCurves.Cohomology.RiemannRoch.Genus_eq_genusFF
import AlgebraicCurves.Cohomology.RiemannRoch.GenusFF_eq_of_algEquiv
import AlgebraicCurves.Cohomology.WeilDualityAdelic_of_functionFieldRiemannRoch_of_stichtenothGenusExists

/-!
# Finsum ramification Index Along sub one eq
-/

section ProofImplementation

namespace AlgebraicCurves.Places.Proofs.Finsum_ramificationIndexAlong_sub_one_eq
attribute [-instance] AlgebraicCurve.RationalFunctionField.instNontrivialInftyValueGroup
attribute [-simp] AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty
  AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some
  AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint
  AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none
  AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one
attribute [-simp] AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec
  AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq
  AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec
  AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq

open AlgebraicCurve IntermediateField

namespace RHEtower

section Tower

variable {K : Type*} [Field K] [IsAlgClosed K] [CharZero K]
variable {F : Type*} [Field F] [Algebra K F]
variable {f : F}

omit [IsAlgClosed K] [CharZero K] in
theorem transcendental_gen (htr : Transcendental K f) :
    Transcendental K (⟨f, IntermediateField.mem_adjoin_simple_self K f⟩ :
      ↥(IntermediateField.adjoin K ({f} : Set F))) := by
  intro halg
  apply htr
  obtain ⟨p, hp0, hp⟩ := halg
  refine ⟨p, hp0, ?_⟩
  have h2 := Polynomial.aeval_algHom_apply
    (IntermediateField.val (IntermediateField.adjoin K ({f} : Set F)))
    ⟨f, IntermediateField.mem_adjoin_simple_self K f⟩ p
  rw [hp, map_zero] at h2
  simpa using h2
omit [IsAlgClosed K] [CharZero K] in
theorem generator_adjoin' (f : F) :
    ∀ y : ↥(IntermediateField.adjoin K ({f} : Set F)), ∃ pn pd : Polynomial K,
      y = Polynomial.aeval
          (⟨f, IntermediateField.mem_adjoin_simple_self K f⟩ :
            ↥(IntermediateField.adjoin K ({f} : Set F))) pn
        / Polynomial.aeval
          (⟨f, IntermediateField.mem_adjoin_simple_self K f⟩ :
            ↥(IntermediateField.adjoin K ({f} : Set F))) pd := by
  intro y
  obtain ⟨pn, pd, h⟩ := (IntermediateField.mem_adjoin_simple_iff K (y : F)).mp y.2
  refine ⟨pn, pd, ?_⟩
  have hc : ∀ p : Polynomial K,
      ((Polynomial.aeval
        (⟨f, IntermediateField.mem_adjoin_simple_self K f⟩ :
          ↥(IntermediateField.adjoin K ({f} : Set F))) p : _) : F)
      = Polynomial.aeval f p := by
    intro p
    exact (Polynomial.aeval_algHom_apply
      (IntermediateField.val (IntermediateField.adjoin K ({f} : Set F)))
      ⟨f, IntermediateField.mem_adjoin_simple_self K f⟩ p).symm
  apply Subtype.coe_injective
  push_cast [hc]
  exact h

theorem finiteDimensional_top (K' L : Type*) [Field K'] [Field L] [Algebra K' L] :
    FiniteDimensional (↥(⊤ : IntermediateField K' L)) L := by
  have hspan : Submodule.span (↥(⊤ : IntermediateField K' L)) ({(1 : L)} : Set L) = ⊤ := by
    rw [Submodule.eq_top_iff']
    intro y
    have : y = (⟨y, trivial⟩ : ↥(⊤ : IntermediateField K' L)) • (1 : L) := by
      simp [IntermediateField.smul_def]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  exact ⟨⟨{1}, by rw [Finset.coe_singleton]; exact hspan⟩⟩
omit [IsAlgClosed K] [CharZero K] in
theorem finiteDimensional_adjoin_gen' (f : F) :
    FiniteDimensional
      (↥(IntermediateField.adjoin K
        ({(⟨f, IntermediateField.mem_adjoin_simple_self K f⟩ :
            ↥(IntermediateField.adjoin K ({f} : Set F)))} :
          Set (↥(IntermediateField.adjoin K ({f} : Set F))))))
      (↥(IntermediateField.adjoin K ({f} : Set F))) := by
  classical
  set E₀ := ↥(IntermediateField.adjoin K ({f} : Set F))
  set x₀ : E₀ := ⟨f, IntermediateField.mem_adjoin_simple_self K f⟩
  have htop : IntermediateField.adjoin K ({x₀} : Set E₀) = ⊤ := by
    rw [eq_top_iff]
    intro y _
    obtain ⟨pn, pd, hy⟩ := generator_adjoin' f y
    have haev : ∀ p : Polynomial K,
        Polynomial.aeval x₀ p ∈ IntermediateField.adjoin K ({x₀} : Set E₀) := by
      intro p
      have h1 : Polynomial.aeval x₀ p ∈ Algebra.adjoin K ({x₀} : Set E₀) :=
        Polynomial.aeval_mem_adjoin_singleton K x₀
      exact (IntermediateField.algebra_adjoin_le_adjoin K _) h1
    rw [hy]
    exact div_mem (haev pn) (haev pd)
  rw [htop]
  exact finiteDimensional_top K E₀

theorem transcendental_ratFunc_X (K' : Type*) [Field K'] :
    Transcendental K' (RatFunc.X : RatFunc K') := by
  rw [transcendental_iff_injective]
  have hcomp : (Polynomial.aeval (RatFunc.X : RatFunc K'))
      = IsScalarTower.toAlgHom K' (Polynomial K') (RatFunc K') := by
    apply Polynomial.algHom_ext
    simp
  rw [hcomp]
  exact IsFractionRing.injective (Polynomial K') (RatFunc K')

theorem adjoin_ratFunc_X_eq_top (K' : Type*) [Field K'] :
    IntermediateField.adjoin K' ({(RatFunc.X : RatFunc K')} : Set (RatFunc K')) = ⊤ := by
  rw [eq_top_iff]
  intro y _
  have haev : ∀ r : Polynomial K',
      algebraMap (Polynomial K') (RatFunc K') r ∈
        IntermediateField.adjoin K' ({(RatFunc.X : RatFunc K')} : Set (RatFunc K')) := by
    intro r
    have h1 : algebraMap (Polynomial K') (RatFunc K') r
        = Polynomial.aeval (RatFunc.X : RatFunc K') r := by
      have hcomp : (Polynomial.aeval (RatFunc.X : RatFunc K'))
          = IsScalarTower.toAlgHom K' (Polynomial K') (RatFunc K') := by
        apply Polynomial.algHom_ext
        simp
      rw [hcomp]
      rfl
    rw [h1]
    exact (IntermediateField.algebra_adjoin_le_adjoin K' _)
      (Polynomial.aeval_mem_adjoin_singleton K' _)
  induction y using RatFunc.induction_on with
  | _ p q hq =>
    exact div_mem (haev p) (haev q)

theorem essFiniteType_ratFunc (K' : Type*) [Field K'] :
    Algebra.EssFiniteType K' (RatFunc K') := by
  refine essFiniteType_of_transcendental_of_finiteDimensional
    (transcendental_ratFunc_X K') ?_
  rw [adjoin_ratFunc_X_eq_top]
  exact finiteDimensional_top K' (RatFunc K')

/-- Identifies the field generated by a transcendental element with the rational function field. -/
noncomputable def adjoinEquivRatFunc (htr : Transcendental K f) :
    (↥(IntermediateField.adjoin K ({f} : Set F))) ≃ₐ[K] RatFunc K := by
  have hAI : AlgebraicIndependent K (fun _ : Unit => f) := by
    rw [algebraicIndependent_iff_injective_aeval]
    have hcomp : (MvPolynomial.aeval (R := K) (fun _ : Unit => f))
        = (Polynomial.aeval f).comp
            (MvPolynomial.uniqueAlgEquiv (R := K) Unit :
              MvPolynomial Unit K ≃ₐ[K] Polynomial K).toAlgHom := by
      apply MvPolynomial.algHom_ext
      intro i
      simp only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, MvPolynomial.aeval_X,
        MvPolynomial.uniqueAlgEquiv_apply, MvPolynomial.eval₂_X, Polynomial.aeval_X]
    rw [hcomp]
    exact (transcendental_iff_injective.mp htr).comp
      (MvPolynomial.uniqueAlgEquiv (R := K) Unit :
        MvPolynomial Unit K ≃ₐ[K] Polynomial K).injective
  have hr : IntermediateField.adjoin K (Set.range (fun _ : Unit => f))
      = IntermediateField.adjoin K ({f} : Set F) := by
    rw [Set.range_const]
  haveI : IsFractionRing K K :=
    IsLocalization.self (fun x hx =>
      IsUnit.mk0 x (mem_nonZeroDivisors_iff_ne_zero.mp hx))
  let e₃ : FractionRing (MvPolynomial Unit K) ≃ₐ[K] FractionRing (Polynomial K) :=
    IsFractionRing.fieldEquivOfAlgEquiv (FA := K) _ _
      (MvPolynomial.uniqueAlgEquiv (R := K) Unit : MvPolynomial Unit K ≃ₐ[K] Polynomial K)
  exact ((IntermediateField.equivOfEq hr).symm.trans hAI.aevalEquivField.symm).symm.symm.trans
    (e₃.trans (RatFunc.toFractionRingAlgEquiv K K).symm)

end Tower

section Heads

variable {K : Type*} [Field K] [IsAlgClosed K] [CharZero K]
variable {F : Type*} [Field F] [Algebra K F]
variable {f : F} (htr : Transcendental K f)

local notation "E" => (IntermediateField.adjoin K (Set.singleton f) : Type _)

omit [IsAlgClosed K] in
include htr in
theorem isCurveOver_E : IsCurveOver K E := by
  have : PerfectField K := PerfectField.ofCharZero
  exact AlgebraicCurve.isCurveOver_of_transcendental_of_perfectField
    (transcendental_gen htr) (finiteDimensional_adjoin_gen' f)
omit [IsAlgClosed K] [CharZero K] in
include htr in
theorem essFiniteType_E : Algebra.EssFiniteType K E :=
  essFiniteType_of_transcendental_of_finiteDimensional
    (transcendental_gen htr) (finiteDimensional_adjoin_gen' f)
omit [IsAlgClosed K] in
include htr in
theorem hasCanonicalDivisor_E :
    haveI : IsCurveOver K E := isCurveOver_E htr
    HasCanonicalDivisor (K := K) (F := E) := by
  have : PerfectField K := PerfectField.ofCharZero
  have : IsCurveOver K E := isCurveOver_E htr
  have : Algebra.EssFiniteType K E := essFiniteType_E htr
  exact hasCanonicalDivisor_of_isCurveOver
include htr in
theorem genus_E_eq_zero :
    haveI : IsCurveOver K E := isCurveOver_E htr
    haveI : HasCanonicalDivisor (K := K) (F := E) := hasCanonicalDivisor_E htr
    genus K E = 0 := by
  classical
  have : PerfectField K := PerfectField.ofCharZero
  have hIC : IsCurveOver K E := isCurveOver_E htr
  have hEF : Algebra.EssFiniteType K E := essFiniteType_E htr
  have hCD : HasCanonicalDivisor (K := K) (F := E) := hasCanonicalDivisor_E htr
  have hDC : ∀ v : Place K E, v.DCoordGenerates := dCoordGenerates_of_isCurveOver
  have hICr : IsCurveOver K (RatFunc K) := instIsCurveOverRatFunc K
  have hEFr : Algebra.EssFiniteType K (RatFunc K) := essFiniteType_ratFunc K
  have hCDr : HasCanonicalDivisor (K := K) (F := RatFunc K) :=
    instHasCanonicalDivisorRatFuncPerfectField K
  have hDCr : ∀ v : Place K (RatFunc K), v.DCoordGenerates := dCoordGenerates_of_isCurveOver
  let e := adjoinEquivRatFunc htr
  let : Algebra (RatFunc K) E := (e.symm.toAlgHom.toRingHom).toAlgebra
  have : IsScalarTower K (RatFunc K) E := IsScalarTower.of_algebraMap_eq' (by
    ext r
    exact congrArg Subtype.val ((e.symm.commutes r).symm))
  let eR : E ≃ₐ[RatFunc K] RatFunc K :=
    AlgEquiv.ofRingEquiv (f := e.toRingEquiv) (fun r => e.apply_symm_apply r)
  have : FiniteDimensional (RatFunc K) E := Module.Finite.equiv eR.symm.toLinearEquiv
  have : Algebra.IsSeparable (RatFunc K) E :=
    Algebra.IsSeparable.of_algHom _ _ eR.toAlgHom
  have hC_R : ConstantsAreBase K (RatFunc K) :=
    constantsAreBase_of_isAlgClosed K (RatFunc K)
  have hRR_R : FunctionFieldRiemannRoch K (RatFunc K) :=
    functionFieldRiemannRoch_of_isAlgClosed
  have hSG_R : StichtenothGenusExists K (RatFunc K) :=
    stichtenothGenusExists_of_isCurveOver hC_R
  have hWDA_R : WeilDualityAdelic K (RatFunc K) :=
    AlgebraicCurve.weilDualityAdelic_of_functionFieldRiemannRoch_of_stichtenothGenusExists hRR_R
    hSG_R
  have hC_E : ConstantsAreBase K E := constantsAreBase_of_isAlgClosed K E
  have hRR_E : FunctionFieldRiemannRoch K E := functionFieldRiemannRoch_of_isAlgClosed
  have hSG_E : StichtenothGenusExists K E := stichtenothGenusExists_of_isCurveOver hC_E
  have hWDA_E : WeilDualityAdelic K E :=
    AlgebraicCurve.weilDualityAdelic_of_functionFieldRiemannRoch_of_stichtenothGenusExists hRR_E
    hSG_E
  have h1 : genus K E = genusFF K E := AlgebraicCurve.genus_eq_genusFF hRR_E hWDA_E hC_E
  have h2 : genusFF K E = genusFF K (RatFunc K) := AlgebraicCurve.genusFF_eq_of_algEquiv e
  have h3 : genus K (RatFunc K) = genusFF K (RatFunc K) :=
    AlgebraicCurve.genus_eq_genusFF hRR_R hWDA_R hC_R
  have h4 : genus K (RatFunc K) = 0 := genus_ratFunc_eq_zero K
  omega

end Heads

end RHEtower

open AlgebraicCurve IntermediateField KaehlerDifferential

namespace SolRH

variable {K : Type*} [Field K] [IsAlgClosed K] [CharZero K]
variable {F : Type*} [Field F] [Algebra K F] [IsCurveOver K F] [Algebra.EssFiniteType K F]
variable [HasCanonicalDivisor (K := K) (F := F)]
variable {f : F} (htr : Transcendental K f)
  [FiniteDimensional (↥(adjoin K ({f} : Set F))) F]

include htr

local notation "E" => (adjoin K (Set.singleton f) : Type _)

private lemma degree_canonicalDivisorOf_F {ω : Ω[F⁄K]} (hω : ω ≠ 0) :
    Divisor.degree (canonicalDivisorOf hω) = 2 * (genus K F : ℤ) - 2 := by
  classical
  have : PerfectField K := PerfectField.ofCharZero
  have : ∀ w : Place K F, w.DCoordGenerates := dCoordGenerates_of_isCurveOver
  let e := RHEtower.adjoinEquivRatFunc htr
  let algRE : Algebra (RatFunc K) E := e.symm.toAlgHom.toRingHom.toAlgebra
  have : IsScalarTower K (RatFunc K) E := IsScalarTower.of_algebraMap_eq' (by
    ext r; exact congrArg Subtype.val ((e.symm.commutes r).symm))
  let eR : E ≃ₐ[RatFunc K] RatFunc K :=
    AlgEquiv.ofRingEquiv (f := e.toRingEquiv) (fun r => e.apply_symm_apply r)
  have : Module.Finite (RatFunc K) E := Module.Finite.equiv eR.symm.toLinearEquiv
  let algRF : Algebra (RatFunc K) F :=
    (((adjoin K ({f} : Set F)).val).comp e.symm.toAlgHom).toRingHom.toAlgebra
  have : IsScalarTower K (RatFunc K) F := IsScalarTower.of_algebraMap_eq' (by
    ext r
    change algebraMap K F r = (adjoin K ({f} : Set F)).val (e.symm (algebraMap K (RatFunc K) r))
    rw [e.symm.commutes]; rfl)
  have : IsScalarTower (RatFunc K) E F := IsScalarTower.of_algebraMap_eq' rfl
  have : FiniteDimensional (RatFunc K) F := Module.Finite.trans E F
  have : CharZero (RatFunc K) :=
    charZero_of_injective_algebraMap (algebraMap K (RatFunc K)).injective
  have : Algebra.IsIntegral (RatFunc K) F := Algebra.IsIntegral.of_finite _ _
  have : IsCurveOver K (RatFunc K) := instIsCurveOverRatFunc K
  have : Algebra.EssFiniteType K (RatFunc K) := RHEtower.essFiniteType_ratFunc K
  have : HasCanonicalDivisor (K := K) (F := RatFunc K) :=
    instHasCanonicalDivisorRatFuncPerfectField K
  have : ∀ v : Place K (RatFunc K), v.DCoordGenerates := dCoordGenerates_of_isCurveOver
  have : Nontrivial Ω[F⁄K] := ⟨ω, 0, hω⟩
  have : Nontrivial Ω[RatFunc K⁄K] := by
    obtain ⟨t, ht⟩ := AlgebraicCurve.exists_D_ne_zero (K := K) (F := RatFunc K)
    exact ⟨D K (RatFunc K) t, 0, ht⟩
  exact degree_canonicalDivisor_eq_of_isAlgClosed hω
omit [IsCurveOver K F] [Algebra.EssFiniteType K F] [HasCanonicalDivisor (K := K) (F := F)]
  [FiniteDimensional (↥(adjoin K ({f} : Set F))) F] in
private lemma degree_canonicalDivisorOf_E :
    haveI : IsCurveOver K E := RHEtower.isCurveOver_E htr
    haveI : HasCanonicalDivisor (K := K) (F := E) := RHEtower.hasCanonicalDivisor_E htr
    ∀ {ω : Ω[E⁄K]} (hω : ω ≠ 0),
      Divisor.degree (canonicalDivisorOf hω) = 2 * (genus K E : ℤ) - 2 := by
  have : IsCurveOver K E := RHEtower.isCurveOver_E htr
  have : Algebra.EssFiniteType K E := RHEtower.essFiniteType_E htr
  have : HasCanonicalDivisor (K := K) (F := E) := RHEtower.hasCanonicalDivisor_E htr
  intro ω hω
  have hgen := RHEtower.transcendental_gen htr
  have hfd : FiniteDimensional (↥(adjoin K ({AdjoinSimple.gen K f} : Set E))) E :=
    RHEtower.finiteDimensional_adjoin_gen' f
  exact @degree_canonicalDivisorOf_F K _ _ _ E _ _ _ _ _ _ hgen hfd _ hω
omit [IsAlgClosed K] [CharZero K] [IsCurveOver K F] [Algebra.EssFiniteType K F] htr
  [HasCanonicalDivisor (K := K) (F := F)]
  [FiniteDimensional (↥(adjoin K ({f} : Set F))) F] in
private lemma ramIdxAlong_eq_ramIdx (w : Place K F) :
    Place.ramificationIndexAlong (adjoin K ({f} : Set F)).val w = w.ramificationIndex E := by
  unfold Place.ramificationIndexAlong
  congr 1

end SolRH

open SolRH in
theorem _root_.AlgebraicCurve.finsum_ramificationIndexAlong_sub_one_eq
    {K : Type*} [Field K] [IsAlgClosed K] [CharZero K]
    {F : Type*} [Field F] [Algebra K F] [IsCurveOver K F] [Algebra.EssFiniteType K F]
    [HasCanonicalDivisor (K := K) (F := F)]
    {f : F} (htr : Transcendental K f)
    [FiniteDimensional (↥(adjoin K ({f} : Set F))) F] :
    (∑ᶠ w : Place K F, ((Place.ramificationIndexAlong (adjoin K ({f} : Set F)).val w : ℤ) - 1)) =
      2 * (Module.finrank K ↥(regularDifferentials K F) : ℤ) - 2 +
      2 * (Module.finrank (↥(adjoin K ({f} : Set F))) F : ℤ) := by
  rw [(AlgebraicCurve.finite_and_finrank_regularDifferentials_eq_genus
    (K := K) (F := F)).2]
  set E := adjoin K ({f} : Set F)
  have : IsCurveOver K (↥E) := RHEtower.isCurveOver_E htr
  have : Algebra.EssFiniteType K (↥E) := RHEtower.essFiniteType_E htr
  have : HasCanonicalDivisor (K := K) (F := ↥E) := RHEtower.hasCanonicalDivisor_E htr
  have : ∀ v : Place K (↥E), v.DCoordGenerates :=
    fun v => AlgebraicCurve.dCoordGenerates_of_isCurveOver v
  have : ∀ w : Place K F, w.DCoordGenerates :=
    fun w => AlgebraicCurve.dCoordGenerates_of_isCurveOver w
  have : Algebra.IsIntegral (↥E) F := Algebra.IsIntegral.of_finite (↥E) F
  have : Algebra.IsSeparable (↥E) F := Algebra.IsSeparable.of_integral (↥E) F
  set t := AdjoinSimple.gen K f
  have : CharZero (↥E) :=
    charZero_of_injective_algebraMap (algebraMap K (↥E)).injective
  have hdf_ne : D K F f ≠ 0 := KaehlerDifferential.D_ne_zero_of_transcendental K f htr
  have ht_ne : D K (↥E) t ≠ 0 := by
    have hfd : FiniteDimensional (↥(adjoin K ({t} : Set (↥E)))) (↥E) :=
      RHEtower.finiteDimensional_adjoin_gen' f
    have : Algebra.IsIntegral (↥(adjoin K ({t} : Set (↥E)))) (↥E) :=
      Algebra.IsIntegral.of_finite _ _
    have : CharZero (↥(adjoin K ({t} : Set (↥E)))) :=
      charZero_of_injective_algebraMap (algebraMap K _).injective
    exact KaehlerDifferential.D_ne_zero_of_transcendental K t (RHEtower.transcendental_gen htr)
  have hmap : map K K (↥E) F (D K (↥E) t) = D K F f := by
    have := KaehlerDifferential.map_D K K (↥E) F t
    rwa [AdjoinSimple.algebraMap_gen K f] at this
  have : CharZero F := charZero_of_injective_algebraMap (algebraMap K F).injective
  have htame : ∀ w : Place K F, ((w.ramificationIndex (↥E) : ℕ) : F) ≠ 0 := by
    intro w
    exact_mod_cast Nat.cast_ne_zero.mpr (w.ramificationIndex_pos (F := ↥E)).ne'
  have hRH := AlgebraicCurve.two_mul_genus_sub_two_eq_of_degree_canonical
    (K := K) (F := ↥E) (F' := F)
    (htame := htame)
    (hω₀ := ht_ne) (hω₀' := hmap ▸ hdf_ne)
    (hK := degree_canonicalDivisorOf_E htr ht_ne)
    (hK' := by
      have heq : canonicalDivisorOf (hmap ▸ hdf_ne) = canonicalDivisorOf hdf_ne := by
        congr 1
      rw [heq]; exact degree_canonicalDivisorOf_F htr hdf_ne)
    (hreg := AlgebraicCurve.localUnitDerivativeRegular_of_isCurveOver)
  erw [RHEtower.genus_E_eq_zero htr] at hRH
  simp only [Nat.cast_zero, mul_zero, zero_sub, mul_neg, mul_comm _ (2 : ℤ)] at hRH
  have hdeg : ∀ w : Place K F, (w.deg : ℤ) = 1 := fun w => by
    exact_mod_cast AlgebraicCurve.Place.deg_eq_one_of_isAlgClosed w
      (AlgebraicCurve.Place.deg_ne_zero_of_finiteDimensional_adjoin f htr w)
  simp only [hdeg, mul_one] at hRH
  have hrw : ∀ w : Place K F,
      ((Place.ramificationIndexAlong E.val w : ℕ) : ℤ) = ((w.ramificationIndex (↥E) : ℕ) : ℤ) := by
    intro w; exact_mod_cast ramIdxAlong_eq_ramIdx w
  simp only [hrw]
  linarith [hRH]
end AlgebraicCurves.Places.Proofs.Finsum_ramificationIndexAlong_sub_one_eq
end ProofImplementation

open _root_.IsDedekindDomain.HeightOneSpectrum in
open _root_.AlgebraicCurve.Place in
attribute [-instance]
  AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK
  AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar
  kw_ffgc_finiteDimensional_adicCompletion
  kw_ffgc_isScalarTower_integersIntegersCompletion
  ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers
  kw_ffgc_continuousSMul_adicCompletionComap
  kw_ffgc_isScalarTower_integersCompletionCompletion
  instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal
  AlgebraicCurve.instHasCanonicalLocalResidueK
  instAlgebra_restrictResidueField
  instIsScalarTower_restrictResidueField
  AlgebraicCurve.instHasLocalResidue
  AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver
  AlgebraicCurve.HasSeparableResidue.of_perfectField
  instIsLocalHom_restrictSubringHom
  AlgebraicCurve.instHasCanonicalLocalResidueKStar
  ModularCurve.KwNo6Pin.isLocalRing_completion
  AlgebraicCurve.RationalFunctionField.instNontrivialInftyValueGroup
  instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation
  instIsTrivialOnWithZeroMultiplicativeIntAdicValuation
  instIsPrimeCenter
  instIsFractionRingIntegralClosureAt
  instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
  instIsDedekindDomainIntegralClosureAt
  instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
attribute [-simp] AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec
  AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe
  AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq
  AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.mulAdele_apply
  AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one
  AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe
  AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe
  AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec
  AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring
  ModularCurve.Lg37.Lg37CompletionSection.mk.injEq
  AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq
  AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq
  ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec
  AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec
  AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule
  AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty
  AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some
  AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint
  AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none
  AlgebraicCurve.Place.congrEquiv_symm_apply
  AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal
  AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply
  AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply
  AlgebraicCurve.RationalFunctionField.deg_placeOfPoint
  AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring
  AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver
  AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply
attribute [-simp] AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal
  AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one
