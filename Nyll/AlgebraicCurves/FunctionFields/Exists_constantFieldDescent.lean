/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_exists_constantFieldDescent.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.Analysis.Complex.Cardinality
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Basic.Complex.Basic
import Mathlib.FieldTheory.IsAlgClosed.Classification
import Mathlib.RingTheory.Algebraic.Cardinality
import Nyll.AlgebraicCurves.Divisors.ClassGroup
import Nyll.AlgebraicCurves.FunctionFields.CurveOver
import Nyll.AlgebraicCurves.Divisors.Canonical
import Nyll.AlgebraicCurves.FunctionFields.IsCurveOver_of_transcendental_of_isSeparable
import Nyll.AlgebraicCurves.Divisors.HasCanonicalDivisor_of_isCurveOver

/-!
# Exists constant Field Descent
-/

section ProofImplementation

namespace AlgebraicCurves.FunctionFields.Proofs.Exists_constantFieldDescent
open _root_.AlgebraicCurve.Place in
attribute [-instance]
  AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia
  instIsScalarTowerResidueFieldRestrictPushforward
  instAlgebraResidueFieldRestrictPushforward
  instIsLocalHomRestrictInclusion
  instIsPrimeCenter
  instIsFractionRingIntegralClosureAt
  instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
  instIsDedekindDomainIntegralClosureAt
  instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
  instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation
  instIsTrivialOnWithZeroMultiplicativeIntAdicValuation
  AlgebraicCurve.RationalFunctionField.instNontrivialInftyValueGroup
attribute [-simp] AlgebraicCurve.Divisor.mapRestrict_single
  AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion
  AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring
  AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue
  AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom
  AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver
  AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply
  AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Place.congrEquiv_symm_apply
  AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal
  AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply
  AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply
  AlgebraicCurve.RationalFunctionField.deg_placeOfPoint
attribute [-simp] AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring
  AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty
  AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some
  AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint
  AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none
  AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one

open Polynomial IntermediateField Cardinal

universe u v

namespace W4B

theorem nonempty_ringHom_complex (k : Type u) [Field k] [CharZero k] [Countable k] :
    Nonempty (k →+* ℂ) := by
  classical
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis ℤ k
  obtain ⟨t, ht⟩ := exists_isTranscendenceBasis ℤ ℂ
  have htcard : #ℂ = #t :=
    IsAlgClosed.cardinal_eq_cardinal_transcendence_basis_of_aleph0_lt' _ ht
      (by simp) (by rw [Cardinal.mk_complex]; exact Cardinal.aleph0_lt_continuum)
  have hst : Cardinal.lift.{0} #s ≤ Cardinal.lift.{u} #t := by
    rw [← htcard, Cardinal.mk_complex]
    calc Cardinal.lift.{0} #s ≤ ℵ₀ := by simp
      _ ≤ Cardinal.lift.{u} 𝔠 := by simpa using Cardinal.aleph0_le_continuum
  obtain ⟨e⟩ := Cardinal.lift_mk_le'.1 hst
  have hv : AlgebraicIndependent ℤ (((↑) : t → ℂ) ∘ e) := ht.1.comp e e.injective
  set R₀ := Algebra.adjoin ℤ (Set.range ((↑) : s → k))
  let φ : R₀ →+* ℂ :=
    ((Subalgebra.val _).comp
      (hv.aevalEquiv.toAlgHom.comp hs.1.aevalEquiv.symm.toAlgHom)).toRingHom
  have hφ : Function.Injective φ := by
    change Function.Injective (fun z => (Subalgebra.val _) (hv.aevalEquiv (hs.1.aevalEquiv.symm z)))
    exact Subtype.val_injective.comp (hv.aevalEquiv.injective.comp hs.1.aevalEquiv.symm.injective)
  let : Algebra R₀ ℂ := φ.toAlgebra
  have : Algebra.IsAlgebraic R₀ k := hs.isAlgebraic
  have : Module.IsTorsionFree R₀ ℂ := Module.isTorsionFree_iff_algebraMap_injective.2 hφ
  exact ⟨(IsAlgClosed.lift (R := R₀) (S := k) (M := ℂ)).toRingHom⟩

theorem isAlgebraic_of_rational_relation {k Φ : Type*} [Field k] [Field Φ] [Algebra k Φ]
    (x y : Φ) (J : Finset ℕ) (r s : ℕ → k[X])
    (hrel : ∑ j ∈ J, (aeval x (r j) / aeval x (s j)) * y ^ j = 0)
    (hne : ∃ j ∈ J, aeval x (r j) / aeval x (s j) ≠ 0) :
    IsAlgebraic k⟮x⟯ y := by
  classical
  have hmem : ∀ j, aeval x (r j) / aeval x (s j) ∈ k⟮x⟯ := fun j =>
    (mem_adjoin_simple_iff (F := k) _).2 ⟨r j, s j, rfl⟩
  let c : ℕ → k⟮x⟯ := fun j => ⟨_, hmem j⟩
  have hc : ∀ j, (c j : Φ) = aeval x (r j) / aeval x (s j) := fun j => rfl
  let q : k⟮x⟯[X] := ∑ j ∈ J, C (c j) * X ^ j
  have hcoeff : ∀ j ∈ J, q.coeff j = c j := by
    intro j hj
    simp only [q, finsetSum_coeff, coeff_C_mul_X_pow]
    rw [Finset.sum_eq_single j]
    · simp
    · intro b _ hb; simp [Ne.symm hb]
    · intro h; exact absurd hj h
  refine ⟨q, ?_, ?_⟩
  · obtain ⟨j₀, hj₀, hne⟩ := hne
    intro hq
    apply hne
    have := hcoeff j₀ hj₀
    rw [hq, coeff_zero] at this
    rw [← hc, ← this]; rfl
  · simp only [q, map_sum, map_mul, map_pow, aeval_C, aeval_X]
    convert hrel using 2
    rw [← hc]; rfl

end W4B

namespace W4B

theorem descent_abstract {k F : Type*} [Field k] [Field F] [Algebra k F]
    {x y : F} (hx : Transcendental k x) (J : Finset ℕ) (r s : ℕ → k[X])
    (hrel : ∑ j ∈ J, (aeval x (r j) / aeval x (s j)) * y ^ j = 0)
    (hne : ∃ j ∈ J, aeval x (r j) / aeval x (s j) ≠ 0) :
    ∃ x₀ : k⟮x, y⟯, (x₀ : F) = x ∧ Transcendental k x₀ ∧
      FiniteDimensional k⟮x₀⟯ k⟮x, y⟯ := by
  classical
  set F₀ : IntermediateField k F := k⟮x, y⟯ with hF₀
  let x₀ : F₀ := ⟨x, subset_adjoin k _ (by simp)⟩
  let y₀ : F₀ := ⟨y, subset_adjoin k _ (by simp)⟩
  have hval : ∀ p : k[X], ((aeval x₀ p : F₀) : F) = aeval x p := by
    intro p
    rw [← IntermediateField.coe_val, ← aeval_algHom_apply]
    rfl
  have hx₀ : Transcendental k x₀ :=
    (transcendental_algebraMap_iff (R := k) (S := F₀) (A := F) (algebraMap F₀ F).injective).1 hx
  have hrel₀ : ∑ j ∈ J, (aeval x₀ (r j) / aeval x₀ (s j)) * y₀ ^ j = 0 := by
    apply (algebraMap F₀ F).injective
    rw [map_sum, map_zero, ← hrel]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, map_div₀, map_pow]
    change ((aeval x₀ (r j) : F₀) : F) / ((aeval x₀ (s j) : F₀) : F) * (y₀ : F) ^ j = _
    rw [hval, hval]
  have hne₀ : ∃ j ∈ J, aeval x₀ (r j) / aeval x₀ (s j) ≠ 0 := by
    obtain ⟨j, hj, hne⟩ := hne
    refine ⟨j, hj, fun h => hne ?_⟩
    have h' := congrArg (algebraMap F₀ F) h
    rw [map_div₀, map_zero] at h'
    change ((aeval x₀ (r j) : F₀) : F) / ((aeval x₀ (s j) : F₀) : F) = 0 at h'
    rwa [hval, hval] at h'
  have hyint : IsIntegral k⟮x₀⟯ y₀ :=
    (isAlgebraic_of_rational_relation x₀ y₀ J r s hrel₀ hne₀).isIntegral
  have htop₀ : k⟮x₀, y₀⟯ = (⊤ : IntermediateField k F₀) := by
    apply IntermediateField.lift_injective
    rw [lift_adjoin, lift_top]
    simp [Set.image_insert_eq, Set.image_singleton, x₀, y₀, hF₀]
  have hfin₀ : FiniteDimensional k⟮x₀⟯ F₀ := by
    have h1 : FiniteDimensional k⟮x₀⟯ k⟮x₀⟯⟮y₀⟯ := adjoin.finiteDimensional hyint
    have h2 : k⟮x₀⟯⟮y₀⟯ = ⊤ := by
      rw [← restrictScalars_eq_top_iff (K := k), adjoin_simple_adjoin_simple, htop₀]
    rw [h2] at h1
    exact LinearEquiv.finiteDimensional
      (IntermediateField.topEquiv (F := k⟮x₀⟯) (E := F₀)).toLinearEquiv
  exact ⟨x₀, rfl, hx₀, hfin₀⟩

theorem exists_constantFieldDescent_core (K : Type u) (F : Type v) [Field K] [Field F]
    [Algebra K F] [IsAlgClosed K] [CharZero K]
    {x : F} (hx : Transcendental K x) (hfin : FiniteDimensional K⟮x⟯ F) :
    ∃ (K₀ : Type u) (F₀ : Type v) (_ : Field K₀) (_ : Field F₀)
      (_ : Algebra K₀ F₀) (_ : Algebra K₀ K) (_ : Algebra F₀ F) (_ : Algebra K₀ F)
      (_ : IsScalarTower K₀ K F) (_ : IsScalarTower K₀ F₀ F) (_ : Algebra K₀ ℂ)
      (_ : IsAlgClosed K₀) (_ : Countable K₀) (_ : CharZero K₀),
      (∃ x₀ : F₀, Transcendental K₀ x₀ ∧ FiniteDimensional K₀⟮x₀⟯ F₀) ∧
      IntermediateField.adjoin K (Set.range (algebraMap F₀ F)) = ⊤ := by
  classical
  have := hfin
  have : CharZero F := charZero_of_injective_algebraMap (algebraMap K F).injective
  have : PerfectField K⟮x⟯ := PerfectField.ofCharZero
  have : Algebra.IsSeparable K⟮x⟯ F := Algebra.IsAlgebraic.isSeparable_of_perfectField
  obtain ⟨y, hy⟩ := Field.exists_primitive_element K⟮x⟯ F
  have hxy : K⟮x, y⟯ = ⊤ := by
    rw [← adjoin_simple_adjoin_simple, hy, restrictScalars_top]
  obtain ⟨q, hq0, hqy⟩ : IsAlgebraic K⟮x⟯ y := Algebra.IsAlgebraic.isAlgebraic y
  have hcoef : ∀ j, ∃ r s : K[X], (q.coeff j : F) = aeval x r / aeval x s := fun j =>
    (mem_adjoin_simple_iff (F := K) _).1 (q.coeff j).2
  choose r s hrs using hcoef
  set J := q.support with hJ
  have hrel : ∑ j ∈ J, (aeval x (r j) / aeval x (s j)) * y ^ j = 0 := by
    rw [aeval_def, eval₂_eq_sum, Polynomial.sum_def] at hqy
    simp_rw [← hrs]
    exact hqy
  have hne : ∃ j ∈ J, aeval x (r j) / aeval x (s j) ≠ 0 := by
    obtain ⟨j, hj⟩ := Polynomial.support_nonempty.2 hq0
    refine ⟨j, hj, ?_⟩
    rw [← hrs]
    exact fun h => (mem_support_iff.1 hj) (ZeroMemClass.coe_eq_zero.1 h)
  let C : Set K := ⋃ j ∈ J, (((r j).coeffs ∪ (s j).coeffs : Finset K) : Set K)
  have hCfin : C.Finite := Set.Finite.biUnion J.finite_toSet fun j _ => Finset.finite_toSet _
  let L : Subfield K := Subfield.closure C
  let K₀ : IntermediateField L K := algebraicClosure L K
  have : IsAlgClosed K₀ := IsAlgClosure.isAlgClosed L
  have : Countable L := by
    have : Countable C := hCfin.countable.to_subtype
    rw [← Cardinal.mk_le_aleph0_iff]
    exact (Subfield.cardinalMk_closure_le_max C).trans (max_le Cardinal.mk_le_aleph0 le_rfl)
  have : Countable K₀ := by
    rw [← Cardinal.mk_le_aleph0_iff]
    exact (Algebra.IsAlgebraic.cardinalMk_le_max L K₀).trans
      (max_le Cardinal.mk_le_aleph0 le_rfl)
  have hCK₀ : C ⊆ Set.range (algebraMap K₀ K) := by
    intro c hc
    exact ⟨⟨c, K₀.algebraMap_mem ⟨c, Subfield.subset_closure hc⟩⟩, rfl⟩
  have hlift : ∀ p : K[X], (p.coeffs : Set K) ⊆ C →
      ∃ p₀ : K₀[X], p₀.map (algebraMap K₀ K) = p := fun p hp =>
    (mem_lifts _).1 ((lifts_iff_coeffs_subset_range _).2 (hp.trans hCK₀))
  have hrC : ∀ j ∈ J, ((r j).coeffs : Set K) ⊆ C := fun j hj c hc =>
    Set.mem_biUnion hj (by simp [hc])
  have hsC : ∀ j ∈ J, ((s j).coeffs : Set K) ⊆ C := fun j hj c hc =>
    Set.mem_biUnion hj (by simp [hc])
  have hr₀ : ∀ j, ∃ p₀ : K₀[X], j ∈ J → p₀.map (algebraMap K₀ K) = r j := fun j => by
    by_cases hj : j ∈ J
    · obtain ⟨p₀, hp₀⟩ := hlift _ (hrC j hj); exact ⟨p₀, fun _ => hp₀⟩
    · exact ⟨0, fun h => absurd h hj⟩
  have hs₀ : ∀ j, ∃ p₀ : K₀[X], j ∈ J → p₀.map (algebraMap K₀ K) = s j := fun j => by
    by_cases hj : j ∈ J
    · obtain ⟨p₀, hp₀⟩ := hlift _ (hsC j hj); exact ⟨p₀, fun _ => hp₀⟩
    · exact ⟨0, fun h => absurd h hj⟩
  choose r₀ hr₀ using hr₀
  choose s₀ hs₀ using hs₀
  have hrel' : ∑ j ∈ J, (aeval x (r₀ j) / aeval x (s₀ j)) * y ^ j = 0 := by
    rw [← hrel]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [← aeval_map_algebraMap K x (r₀ j), ← aeval_map_algebraMap K x (s₀ j), hr₀ j hj, hs₀ j hj]
  have hne' : ∃ j ∈ J, aeval x (r₀ j) / aeval x (s₀ j) ≠ 0 := by
    obtain ⟨j, hj, hne⟩ := hne
    refine ⟨j, hj, ?_⟩
    rwa [← aeval_map_algebraMap K x (r₀ j), ← aeval_map_algebraMap K x (s₀ j), hr₀ j hj,
      hs₀ j hj]
  obtain ⟨x₀, hx₀x, hx₀, hfin₀⟩ :=
    descent_abstract (hx.of_tower_top K₀) J r₀ s₀ hrel' hne'
  obtain ⟨ψ⟩ := nonempty_ringHom_complex K₀
  refine ⟨K₀, K₀⟮x, y⟯, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, ψ.toAlgebra, inferInstance, inferInstance,
    inferInstance, ⟨x₀, hx₀, hfin₀⟩, ?_⟩
  rw [eq_top_iff, ← hxy]
  refine adjoin.mono K _ _ ?_
  rintro z (rfl | h)
  · exact ⟨⟨z, subset_adjoin K₀ _ (by simp)⟩, rfl⟩
  · rw [Set.mem_singleton_iff.1 h]; exact ⟨⟨y, subset_adjoin K₀ _ (by simp)⟩, rfl⟩

end W4B

open AlgebraicCurve

namespace W4B

theorem essFiniteType_of_fg' {K F : Type*} [Field K] [Field F] [Algebra K F]
    (hfg : ∃ x : F, Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F) :
    Algebra.EssFiniteType K F := by
  obtain ⟨x, -, hfin⟩ := hfg
  have h1 : Algebra.EssFiniteType K (IntermediateField.adjoin K ({x} : Set F)) :=
    IntermediateField.essFiniteType_iff.2
      (IntermediateField.fg_adjoin_of_finite (Set.finite_singleton x))
  have h2 : Algebra.EssFiniteType (IntermediateField.adjoin K ({x} : Set F)) F := inferInstance
  exact Algebra.EssFiniteType.comp K (IntermediateField.adjoin K ({x} : Set F)) F

theorem hasCanonicalDivisor_of_charZero' (K F : Type*) [Field K] [Field F] [Algebra K F]
    [CharZero K] [IsCurveOver K F]
    (hfg : ∃ x : F, Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F) :
    HasCanonicalDivisor (K := K) (F := F) := by
  have : Algebra.EssFiniteType K F := essFiniteType_of_fg' hfg
  have : PerfectField K := PerfectField.ofCharZero
  exact AlgebraicCurve.hasCanonicalDivisor_of_isCurveOver (K := K) (F := F)

end W4B

theorem _root_.AlgebraicCurve.exists_constantFieldDescent (K : Type u) (F : Type v) [Field K]
  [Field F]
    [Algebra K F] [IsAlgClosed K] [CharZero K]
    (hfg : ∃ x : F, Transcendental K x ∧ FiniteDimensional (IntermediateField.adjoin K ({x} : Set
      F)) F)
    [IsCurveOver K F] [HasCanonicalDivisor (K := K) (F := F)] :
    ∃ (K₀ : Type u) (F₀ : Type v) (_ : Field K₀) (_ : Field F₀)
      (_ : Algebra K₀ F₀) (_ : Algebra K₀ K) (_ : Algebra F₀ F) (_ : Algebra K₀ F)
      (_ : IsScalarTower K₀ K F) (_ : IsScalarTower K₀ F₀ F) (_ : Algebra K₀ ℂ)
      (_ : IsAlgClosed K₀) (_ : Countable K₀)
      (_ : IsCurveOver K₀ F₀) (_ : HasCanonicalDivisor (K := K₀) (F := F₀)),
      (∃ x : F₀, Transcendental K₀ x ∧
        FiniteDimensional (IntermediateField.adjoin K₀ ({x} : Set F₀)) F₀) ∧
      IntermediateField.adjoin K (Set.range (algebraMap F₀ F)) = ⊤ := by
  obtain ⟨x, hx, hfin⟩ := hfg
  obtain ⟨K₀, F₀, _, _, _, _, _, _, _, _, algC, _, _, _, ⟨x₀, hx₀, hfin₀⟩, htop⟩ :=
    W4B.exists_constantFieldDescent_core K F hx hfin
  have : CharZero F₀ := charZero_of_injective_algebraMap (algebraMap K₀ F₀).injective
  have : Algebra.IsSeparable (IntermediateField.adjoin K₀ ({x₀} : Set F₀)) F₀ := inferInstance
  have hC : IsCurveOver K₀ F₀ :=
    AlgebraicCurve.isCurveOver_of_transcendental_of_isSeparable K₀ F₀ x₀ hx₀ hfin₀ inferInstance
  have hK : HasCanonicalDivisor (K := K₀) (F := F₀) :=
    W4B.hasCanonicalDivisor_of_charZero' K₀ F₀ ⟨x₀, hx₀, hfin₀⟩
  exact ⟨K₀, F₀, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, algC, inferInstance, inferInstance, hC, hK,
    ⟨x₀, hx₀, hfin₀⟩, htop⟩
end AlgebraicCurves.FunctionFields.Proofs.Exists_constantFieldDescent
end ProofImplementation
