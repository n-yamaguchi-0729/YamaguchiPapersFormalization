/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_exists_constantFieldExtension.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import AlgebraicCurves.Divisors.ClassGroup
import AlgebraicCurves.FunctionFields.CurveOver
import AlgebraicCurves.Divisors.Canonical
import AlgebraicCurves.FunctionFields.IsCurveOver_of_transcendental_of_isSeparable
import AlgebraicCurves.Divisors.HasCanonicalDivisor_of_isCurveOver

/-!
# Exists constant Field Extension
-/

section ProofImplementation

namespace AlgebraicCurves.FunctionFields.Proofs.Exists_constantFieldExtension
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

open Polynomial TensorProduct

namespace W4B

theorem aeval_ofFinsupp_eq {R A : Type*} [CommRing R] [Ring A] [Algebra R A] (x : A)
    (l : ℕ →₀ R) : aeval x (⟨.ofCoeff l⟩ : R[X]) = Finsupp.linearCombination R (fun n : ℕ => x ^ n)
      l := by
  simp only [aeval_def, eval₂_eq_sum, Polynomial.sum_def, Finsupp.linearCombination_apply,
    Finsupp.sum,
    support_ofFinsupp, coeff_ofFinsupp]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [Algebra.smul_def]

theorem transcendental_iff_linearIndependent_pow {R A : Type*} [CommRing R] [Ring A]
    [Algebra R A] (x : A) :
    Transcendental R x ↔ LinearIndependent R (fun n : ℕ => x ^ n) := by
  rw [transcendental_iff, linearIndependent_iff]
  constructor
  · intro h l hl
    have := h ⟨.ofCoeff l⟩ (by rwa [aeval_ofFinsupp_eq])
    exact AddMonoidAlgebra.ofCoeff_eq_zero.1 (Polynomial.ofFinsupp_eq_zero.1 this)
  · intro h p hp
    obtain ⟨l⟩ := p
    have hl := h l.coeff (by rwa [← aeval_ofFinsupp_eq, AddMonoidAlgebra.ofCoeff_coeff])
    exact Polynomial.ofFinsupp_eq_zero.2 (AddMonoidAlgebra.coeff_eq_zero.1 hl)

theorem transcendental_one_tmul {K₀ : Type*} [Field K₀] (K' : Type*) [Field K'] [Algebra K₀ K']
    {F₀ : Type*} [Field F₀] [Algebra K₀ F₀] {x : F₀} (hx : Transcendental K₀ x) :
    Transcendental K' ((1 : K') ⊗ₜ[K₀] x) := by
  rw [transcendental_iff_linearIndependent_pow] at hx ⊢
  have := Module.Flat.linearIndependent_one_tmul (S := K') hx
  convert this using 1
  ext n
  simp [Algebra.TensorProduct.tmul_pow]

theorem essFiniteType_of_fg {K F : Type*} [Field K] [Field F] [Algebra K F]
    (hfg : ∃ x : F, Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F) :
    Algebra.EssFiniteType K F := by
  obtain ⟨x, -, hfin⟩ := hfg
  have h1 : Algebra.EssFiniteType K (IntermediateField.adjoin K ({x} : Set F)) :=
    IntermediateField.essFiniteType_iff.2
      (IntermediateField.fg_adjoin_of_finite (Set.finite_singleton x))
  have h2 : Algebra.EssFiniteType (IntermediateField.adjoin K ({x} : Set F)) F := inferInstance
  exact Algebra.EssFiniteType.comp K (IntermediateField.adjoin K ({x} : Set F)) F

section Abstract

variable {K₀ F₀ K' F' : Type*}
  [Field K₀] [Field F₀] [Field K'] [Field F'] [Algebra K₀ F₀] [Algebra K₀ K'] [Algebra K' F']
  (τ : K' ⊗[K₀] F₀ →ₐ[K'] F')

/-- The homomorphism from the original function field into the constant-field extension. -/
noncomputable def incl : F₀ →+* F' :=
  τ.toRingHom.comp (Algebra.TensorProduct.includeRight (R := K₀) (A := K')).toRingHom

theorem incl_apply (f : F₀) : incl τ f = τ ((1 : K') ⊗ₜ[K₀] f) := rfl

theorem incl_algebraMap (k : K₀) :
    incl τ (algebraMap K₀ F₀ k) = algebraMap K' F' (algebraMap K₀ K' k) := by
  rw [incl_apply, ← τ.commutes, Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self,
    RingHom.id_apply, Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one,
    TensorProduct.smul_tmul]

theorem tau_tmul (k : K') (f : F₀) :
    τ (k ⊗ₜ[K₀] f) = algebraMap K' F' k * incl τ f := by
  have : k ⊗ₜ[K₀] f = algebraMap K' (K' ⊗[K₀] F₀) k * ((1 : K') ⊗ₜ[K₀] f) := by
    rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
      Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  rw [this, map_mul, AlgHom.commutes, incl_apply]

theorem tau_mem (L : IntermediateField K' F') (hL : ∀ f : F₀, incl τ f ∈ L)
    (a : K' ⊗[K₀] F₀) : τ a ∈ L := by
  induction a using TensorProduct.inductionOn with
  | tmul k f => rw [tau_tmul]; exact mul_mem (algebraMap_mem L k) (hL f)
  | add a b ha hb => rw [map_add]; exact add_mem ha hb

variable (hgen : ∀ z : F', ∃ a b : K' ⊗[K₀] F₀, τ a / τ b = z)

include hgen in
theorem eq_top_of_forall_incl_mem (L : IntermediateField K' F')
    (hL : ∀ f : F₀, incl τ f ∈ L) : L = ⊤ := by
  rw [eq_top_iff]
  intro z _
  obtain ⟨a, b, rfl⟩ := hgen z
  exact div_mem (tau_mem τ L hL a) (tau_mem τ L hL b)
include hgen in
theorem adjoin_range_incl_eq_top :
    IntermediateField.adjoin K' (Set.range (incl τ)) = ⊤ :=
  eq_top_of_forall_incl_mem τ hgen _ fun f => IntermediateField.subset_adjoin _ _ ⟨f, rfl⟩

variable [Algebra K₀ F'] [IsScalarTower K₀ K' F']

/-- The inclusion into the constant-field extension regarded as an algebra homomorphism. -/
noncomputable def inclₐ : F₀ →ₐ[K₀] F' :=
  { incl τ with
    commutes' := fun k => by
      simp only [RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe,
        MonoidHom.coe_ofClass]
      rw [incl_algebraMap, ← IsScalarTower.algebraMap_apply] }

@[scoped simp] theorem inclₐ_apply (f : F₀) : inclₐ τ f = incl τ f := rfl

theorem incl_mem_adjoin_image {S : Set F₀} {f : F₀} (hf : f ∈ IntermediateField.adjoin K₀ S) :
    incl τ f ∈ IntermediateField.adjoin K' (incl τ '' S) := by
  have h1 : inclₐ τ f ∈ (IntermediateField.adjoin K₀ S).map (inclₐ τ) := ⟨f, hf, rfl⟩
  rw [IntermediateField.adjoin_map] at h1
  have h2 : IntermediateField.adjoin K₀ (inclₐ τ '' S) ≤
      (IntermediateField.adjoin K' (incl τ '' S)).restrictScalars K₀ :=
    IntermediateField.adjoin_le_iff.mpr (IntermediateField.subset_adjoin K' _)
  exact h2 h1

variable {x : F₀} (hx : Transcendental K₀ x)
  (hfin : FiniteDimensional (IntermediateField.adjoin K₀ ({x} : Set F₀)) F₀)
  (hker : ∀ p : K'[X], τ (aeval ((1 : K') ⊗ₜ[K₀] x) p) = 0 → p = 0)

include hker in
omit [Algebra K₀ F'] [IsScalarTower K₀ K' F'] in
theorem transcendental_incl : Transcendental K' (incl τ x) := by
  rw [transcendental_iff]
  intro p hp
  apply hker
  rw [← Polynomial.aeval_algHom_apply]
  exact hp
include hfin in
theorem isIntegral_incl (f : F₀) :
    IsIntegral (IntermediateField.adjoin K' ({incl τ x} : Set F')) (incl τ f) := by
  set E := IntermediateField.adjoin K' ({incl τ x} : Set F')
  have hmem : ∀ c : IntermediateField.adjoin K₀ ({x} : Set F₀), incl τ (c : F₀) ∈ E := by
    intro c
    have := incl_mem_adjoin_image τ (S := {x}) c.2
    rwa [Set.image_singleton] at this
  let ψ : IntermediateField.adjoin K₀ ({x} : Set F₀) →+* E :=
    ((incl τ).comp (algebraMap _ F₀)).codRestrict E hmem
  have hcomp : (algebraMap E F').comp ψ =
      (incl τ).comp (algebraMap (IntermediateField.adjoin K₀ ({x} : Set F₀)) F₀) := by
    ext c; rfl
  exact IsIntegral.map_of_comp_eq ψ (incl τ) hcomp (IsIntegral.of_finite _ f)
include hx hfin hgen in
theorem finiteDimensional_adjoin_incl :
    FiniteDimensional (IntermediateField.adjoin K' ({incl τ x} : Set F')) F' := by
  set E := IntermediateField.adjoin K' ({incl τ x} : Set F')
  have : Algebra.EssFiniteType K₀ F₀ := essFiniteType_of_fg ⟨x, hx, hfin⟩
  obtain ⟨s, hs⟩ := IntermediateField.fg_top K₀ F₀
  have : Finite (incl τ '' (s : Set F₀)) := Set.Finite.to_subtype ((s.finite_toSet).image _)
  have hLfin : FiniteDimensional E (IntermediateField.adjoin E (incl τ '' (s : Set F₀))) :=
    IntermediateField.finiteDimensional_adjoin fun z hz => by
      obtain ⟨f, -, rfl⟩ := hz
      exact isIntegral_incl τ hfin f
  have hLtop : IntermediateField.adjoin E (incl τ '' (s : Set F₀)) = ⊤ := by
    rw [← IntermediateField.restrictScalars_eq_top_iff (K := K'),
      IntermediateField.adjoin_adjoin_left]
    apply eq_top_of_forall_incl_mem τ hgen
    intro f
    have hf : f ∈ IntermediateField.adjoin K₀ (s : Set F₀) := by rw [hs]; trivial
    exact IntermediateField.adjoin.mono K' _ _ Set.subset_union_right (incl_mem_adjoin_image τ hf)
  rw [hLtop] at hLfin
  exact LinearEquiv.finiteDimensional (IntermediateField.topEquiv (F := E) (E := F')).toLinearEquiv

end Abstract

section Concrete

universe u v w

variable {K₀ : Type u} {F₀ : Type v} {K' : Type w}
  [Field K₀] [Field F₀] [Field K'] [Algebra K₀ F₀] [Algebra K₀ K']
  (P : Ideal (K' ⊗[K₀] F₀))

/-- The quotient of the tensor product by the chosen prime ideal. -/
abbrev CFQ : Type (max v w) := (K' ⊗[K₀] F₀) ⧸ P

/-- The fraction field of the tensor-product quotient. -/
abbrev CFExt : Type (max v w) := FractionRing (CFQ P)

noncomputable scoped instance CFExt.algK' : Algebra K' (CFExt P) := inferInstance

noncomputable scoped instance CFExt.algK₀ : Algebra K₀ (CFExt P) := inferInstance

scoped instance CFExt.towerK : IsScalarTower K₀ K' (CFExt P) := inferInstance

scoped instance CFExt.towerQ : IsScalarTower K' (CFQ P) (CFExt P) := inferInstance


/-- The map from the tensor product to the fraction field of its quotient. -/
noncomputable def tau : K' ⊗[K₀] F₀ →ₐ[K'] CFExt P :=
  (IsScalarTower.toAlgHom K' (CFQ P) (CFExt P)).comp (Ideal.Quotient.mkₐ K' P)

theorem tau_apply (a : K' ⊗[K₀] F₀) :
    tau P a = IsScalarTower.toAlgHom K' (CFQ P) (CFExt P) (Ideal.Quotient.mk P a) := rfl

variable [P.IsPrime]

theorem tau_gen (z : CFExt P) : ∃ a b : K' ⊗[K₀] F₀, tau P a / tau P b = z := by
  obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := CFQ P) z
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
  exact ⟨a, b, rfl⟩
omit [P.IsPrime] in
theorem tau_eq_zero_iff (a : K' ⊗[K₀] F₀) : tau P a = 0 ↔ a ∈ P := by
  rw [← Ideal.Quotient.eq_zero_iff_mem, tau_apply, IsScalarTower.coe_toAlgHom',
    map_eq_zero_iff _ (IsFractionRing.injective (CFQ P) (CFExt P))]
omit [P.IsPrime] in
theorem exists_constantFieldExtension_core (K₀ : Type u) (F₀ : Type v) (K' : Type w)
    [Field K₀] [Field F₀] [Field K'] [Algebra K₀ F₀] [Algebra K₀ K']
    {x : F₀} (hx : Transcendental K₀ x)
    (hfin : FiniteDimensional (IntermediateField.adjoin K₀ ({x} : Set F₀)) F₀) :
    ∃ (F' : Type (max v w)) (_ : Field F') (_ : Algebra K' F') (_ : Algebra F₀ F')
      (_ : Algebra K₀ F') (_ : IsScalarTower K₀ K' F') (_ : IsScalarTower K₀ F₀ F'),
      Transcendental K' (algebraMap F₀ F' x) ∧
      FiniteDimensional (IntermediateField.adjoin K' ({algebraMap F₀ F' x} : Set F')) F' ∧
      IntermediateField.adjoin K' (Set.range (algebraMap F₀ F')) = ⊤ := by
  classical
  have hxA_tr : Transcendental K' ((1 : K') ⊗ₜ[K₀] x) := transcendental_one_tmul K' hx
  let S : Submonoid (K' ⊗[K₀] F₀) :=
    (nonZeroDivisors K'[X]).map (aeval ((1 : K') ⊗ₜ[K₀] x) : K'[X] →ₐ[K'] K' ⊗[K₀] F₀)
  have hdisj : Disjoint ((⊥ : Ideal (K' ⊗[K₀] F₀)) : Set (K' ⊗[K₀] F₀)) S := by
    refine Set.disjoint_left.2 fun a ha hS => ?_
    have ha0 : a = 0 := by simpa using ha
    obtain ⟨p, hp, rfl⟩ := hS
    have : p = 0 := (transcendental_iff.1 hxA_tr) p ha0
    exact nonZeroDivisors.ne_zero hp this
  obtain ⟨P, hPprime, -, hPdisj⟩ :=
    Ideal.exists_le_prime_disjoint (⊥ : Ideal (K' ⊗[K₀] F₀)) S hdisj
  have hker : ∀ p : K'[X], tau P (aeval ((1 : K') ⊗ₜ[K₀] x) p) = 0 → p = 0 := by
    intro p hp
    rw [tau_eq_zero_iff] at hp
    by_contra hne
    have hS : aeval ((1 : K') ⊗ₜ[K₀] x) p ∈ S := ⟨p, mem_nonZeroDivisors_of_ne_zero hne, rfl⟩
    exact Set.disjoint_left.1 hPdisj hp hS
  let algF₀ : Algebra F₀ (CFExt P) := (incl (tau P)).toAlgebra
  let : SMul F₀ (CFExt P) := algF₀.toSMul
  have tF₀ : IsScalarTower K₀ F₀ (CFExt P) :=
    IsScalarTower.of_algebraMap_eq fun k => (incl_algebraMap (tau P) k).symm
  refine ⟨CFExt P, inferInstance, inferInstance, algF₀, inferInstance, inferInstance, tF₀,
    ?_, ?_, ?_⟩
  · exact transcendental_incl (tau P) hker
  · exact finiteDimensional_adjoin_incl (tau P) (tau_gen P) hx hfin
  · exact adjoin_range_incl_eq_top (tau P) (tau_gen P)

end Concrete

end W4B

open AlgebraicCurve

namespace W4B

theorem hasCanonicalDivisor_of_charZero (K F : Type*) [Field K] [Field F] [Algebra K F]
    [CharZero K] [IsCurveOver K F]
    (hfg : ∃ x : F, Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F) :
    HasCanonicalDivisor (K := K) (F := F) := by
  have : Algebra.EssFiniteType K F := essFiniteType_of_fg hfg
  have : PerfectField K := PerfectField.ofCharZero
  exact AlgebraicCurve.hasCanonicalDivisor_of_isCurveOver (K := K) (F := F)

end W4B

universe u v w

theorem _root_.AlgebraicCurve.exists_constantFieldExtension (K₀ : Type u) (F₀ : Type v) (K' : Type
  w)
    [Field K₀] [Field F₀] [Field K'] [Algebra K₀ F₀] [Algebra K₀ K']
    [IsAlgClosed K₀] [CharZero K₀] [IsAlgClosed K']
    (hfg₀ : ∃ x : F₀, Transcendental K₀ x ∧
      FiniteDimensional (IntermediateField.adjoin K₀ ({x} : Set F₀)) F₀)
    [IsCurveOver K₀ F₀] [HasCanonicalDivisor (K := K₀) (F := F₀)] :
    ∃ (F' : Type (max v w)) (_ : Field F') (_ : Algebra K' F') (_ : Algebra F₀ F')
      (_ : Algebra K₀ F') (_ : IsScalarTower K₀ K' F') (_ : IsScalarTower K₀ F₀ F')
      (_ : IsCurveOver K' F') (_ : HasCanonicalDivisor (K := K') (F := F')),
      (∃ x : F', Transcendental K' x ∧
        FiniteDimensional (IntermediateField.adjoin K' ({x} : Set F')) F') ∧
      IntermediateField.adjoin K' (Set.range (algebraMap F₀ F')) = ⊤ := by
  obtain ⟨x, hx, hfin⟩ := hfg₀
  obtain ⟨F', _, _, _, _, _, _, htr, hfin', htop⟩ :=
    W4B.exists_constantFieldExtension_core K₀ F₀ K' hx hfin
  have : CharZero K' := charZero_of_injective_algebraMap (algebraMap K₀ K').injective
  have : CharZero F' := charZero_of_injective_algebraMap (algebraMap K' F').injective
  have : Algebra.IsSeparable (IntermediateField.adjoin K' ({algebraMap F₀ F' x} : Set F')) F' :=
    inferInstance
  have hC : IsCurveOver K' F' :=
    AlgebraicCurve.isCurveOver_of_transcendental_of_isSeparable K' F' (algebraMap F₀ F' x)
      htr hfin' inferInstance
  have hK : HasCanonicalDivisor (K := K') (F := F') :=
    W4B.hasCanonicalDivisor_of_charZero K' F' ⟨algebraMap F₀ F' x, htr, hfin'⟩
  exact ⟨F', inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, hC, hK, ⟨algebraMap F₀ F' x, htr, hfin'⟩, htop⟩
end AlgebraicCurves.FunctionFields.Proofs.Exists_constantFieldExtension
end ProofImplementation
