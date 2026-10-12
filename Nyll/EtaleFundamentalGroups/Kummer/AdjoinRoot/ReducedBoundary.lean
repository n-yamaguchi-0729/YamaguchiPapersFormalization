/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Algebra.GroupWithZero.NonZeroDivisors
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.DedekindDomain.Basic
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
import Mathlib.RingTheory.Ideal.Over
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.LocalRing.RingHom.Basic
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Localization.Basic
import Mathlib.RingTheory.Localization.Defs
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.RamificationInertia.Ramification
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.TensorProduct.Maps
import Nyll.EtaleFundamentalGroups.Kummer.AdjoinRoot.UniformizerRamification
import Nyll.EtaleFundamentalGroups.Kummer.Radicals.Explicit
import Nyll.EtaleFundamentalGroups.Kummer.RootCovers.Local.Basic
import Nyll.EtaleFundamentalGroups.Kummer.RootCovers.Local.Residue
import Nyll.EtaleFundamentalGroups.Kummer.UnitAbsorption.HigherRadical
import Nyll.EtaleFundamentalGroups.Kummer.UnitAbsorption.HigherRadicalActualFactor
import Nyll.SchemeTheory.RingTheory.ReducedCartierDivisor
import Nyll.SchemeTheory.RingTheory.RegularLocalDomain

/-!
# Kummer covers at a reduced boundary

The positive root cover over `A_P` is an actual localization of the original
root algebra `A[X] / (X ^ n - f)`. Its closed prime is constructed by
pulling back the maximal ideal; no prime or local-ring comparison is assumed.

If `A` is Noetherian, `f` is a nonzerodivisor, and `A / (f)` is reduced,
then at every minimal prime over `(f)` this root algebra over `A_P` is a
DVR and is the integral closure of `A_P` in its fraction field. The
ramification index is `n`, and the canonical residue map is bijective.
When `n` is a unit in `A`, this index is a unit in the base residue field.

These are the local algebra and ramification calculations for the standard
cover in Stacks Project, Example 58.31.4 (tag `0EYF`):
https://stacks.math.columbia.edu/tag/0EYF
-/

noncomputable section

namespace EtaleFundamentalGroups.Kummer

open Polynomial
open scoped TensorProduct

universe u

/-- The actual base change of a root algebra to the localization at an
arbitrary prime, with the mapped radicand written explicitly. -/
def adjoinRootAtPrimeBaseChangeAlgEquiv
    {A : Type u} [CommRing A] (P : Ideal A) [P.IsPrime] (n : ℕ) (f : A) :
    (Localization.AtPrime P ⊗[A] AdjoinRoot (X ^ n - C f)) ≃ₐ[Localization.AtPrime P]
      AdjoinRoot (X ^ n - C (algebraMap A (Localization.AtPrime P) f)) :=
  (adjoinRootBaseChangeAlgEquiv (S := Localization.AtPrime P) (X ^ n - C f)).trans
    (AdjoinRoot.algEquivOfEq (Localization.AtPrime P) _ _ (by
      rw [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C]))

/-- Over a prime containing the radicand, the base-changed positive root
cover is already local. Its actual closed-point preimage lies over that
prime, and the root cover is the localization at this preimage. -/
theorem isLocalization_adjoinRootAtPrime_closedPoint
    {A : Type u} [CommRing A] (P : Ideal A) [P.IsPrime]
    {n : ℕ} (hn : 0 < n) (f : A) (hfP : f ∈ P) :
    let V := Localization.AtPrime P
    let C₀ := AdjoinRoot (X ^ n - C f)
    let B := AdjoinRoot (X ^ n - C (algebraMap A V f))
    let e := adjoinRootAtPrimeBaseChangeAlgEquiv P n f
    let : Algebra C₀ B :=
      (e.toRingHom.comp (Algebra.TensorProduct.includeRight :
        C₀ →ₐ[A] V ⊗[A] C₀).toRingHom).toAlgebra
    let : IsLocalRing B := isLocalRing_adjoinRoot_X_pow_sub_C hn
      ((IsLocalization.AtPrime.to_map_mem_maximal_iff V P f).mpr hfP)
    let q := (IsLocalRing.maximalIdeal B).comap (algebraMap C₀ B)
    let : q.IsPrime := Ideal.comap_isPrime (algebraMap C₀ B) _
    q.under A = P ∧ IsLocalization q.primeCompl B := by
  intro V C₀ B e hCB hlocal q hq
  have : Module.FaithfullyFlat V B :=
    faithfullyFlat_adjoinRoot_X_pow_sub_C hn (algebraMap A V f)
  have hbase (a : A) : algebraMap C₀ B (algebraMap A C₀ a) =
      algebraMap V B (algebraMap A V a) := by
    change e (1 ⊗ₜ[A] algebraMap A C₀ a) =
      algebraMap V B (algebraMap A V a)
    calc
      e (1 ⊗ₜ[A] algebraMap A C₀ a) =
          e (algebraMap V (V ⊗[A] C₀) (algebraMap A V a)) := by
        congr 1
        exact (Algebra.TensorProduct.tmul_one_eq_one_tmul a).symm
      _ = _ := e.commutes _
  have hunder : q.under A = P := by
    ext a
    change algebraMap C₀ B (algebraMap A C₀ a) ∈
      IsLocalRing.maximalIdeal B ↔ a ∈ P
    rw [hbase]
    change algebraMap A V a ∈
      (IsLocalRing.maximalIdeal B).comap (algebraMap V B) ↔ a ∈ P
    rw [IsLocalRing.maximalIdeal_comap]
    exact IsLocalization.AtPrime.to_map_mem_maximal_iff V P a
  refine ⟨hunder, ?_⟩
  let M := Algebra.algebraMapSubmonoid C₀ P.primeCompl
  let : Algebra C₀ (V ⊗[A] C₀) := Algebra.TensorProduct.rightAlgebra
  let eC : (V ⊗[A] C₀) ≃ₐ[C₀] B :=
    { e.toRingEquiv with commutes' := fun _ ↦ rfl }
  have : IsLocalization M (V ⊗[A] C₀) :=
    IsLocalization.tensorRight (R := A) (S := C₀) (A := V) P.primeCompl
  have : IsLocalization M B := IsLocalization.isLocalization_of_algEquiv M eC
  have hMle : M ≤ q.primeCompl := by
    rintro _ ⟨a, ha, rfl⟩
    change algebraMap A C₀ a ∉ q
    intro hmem
    have haUnder : a ∈ q.under A := hmem
    rw [hunder] at haUnder
    exact ha haUnder
  apply IsLocalization.of_le_of_exists_dvd M q.primeCompl hMle
  intro b hb
  have hbUnit : IsUnit (algebraMap C₀ B b) :=
    IsLocalRing.notMem_maximalIdeal.mp hb
  exact (IsLocalization.algebraMap_isUnit_iff (M := M)).mp hbUnit

/-- The original reduced-Cartier hypotheses produce the normalization DVR
at each generic boundary point. Its residue extension is trivial and its
ramification index is precisely the exponent, hence invertible in the
base residue field when the exponent is invertible in `A`.

The domain and DVR witnesses are outputs; neither normality nor a
comparison with an unspecified extension field is an input. -/
theorem standardKummerCover_reducedBoundary
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    (f : A) (hf : f ∈ nonZeroDivisors A)
    [IsReduced (A ⧸ Ideal.span ({f} : Set A))]
    (P : Ideal A) [P.IsPrime]
    (hP : P ∈ (Ideal.span ({f} : Set A)).minimalPrimes)
    {n : ℕ} (hn : 0 < n) (hnUnit : IsUnit (n : A)) :
    let V := Localization.AtPrime P
    let B := AdjoinRoot (X ^ n - C (algebraMap A V f))
    let : IsRegularLocalRing V :=
      SchemeTheory.isRegularLocalRing_localizationAtPrime_of_reduced_quotient f hf P hP
    let : IsDomain V := IsRegularLocalRing.isDomain V
    let : IsDiscreteValuationRing V :=
      SchemeTheory.isDiscreteValuationRing_localizationAtPrime_of_reduced_quotient f hf P hP
    ∃ hdomain : IsDomain B,
      let : IsDomain B := hdomain
      ∃ hdvr : IsDiscreteValuationRing B,
        let : IsDiscreteValuationRing B := hdvr
        let : Module.FaithfullyFlat V B :=
          faithfullyFlat_adjoinRoot_X_pow_sub_C hn (algebraMap A V f)
        IsIntegralClosure B V (FractionRing B) ∧
          (IsLocalRing.maximalIdeal B).ramificationIdx V = n ∧
          Function.Bijective (IsLocalRing.ResidueField.map (algebraMap V B)) ∧
          IsUnit ((IsLocalRing.maximalIdeal B).ramificationIdx V :
            IsLocalRing.ResidueField V) := by
  intro V B hregular hdomainV hdvrV
  let π : V := algebraMap A V f
  have hmax : IsLocalRing.maximalIdeal V = Ideal.span ({π} : Set V) :=
    SchemeTheory.maximalIdeal_localizationAtPrime_eq_span_of_reduced_quotient f P hP
  have hπ : Prime π :=
    ((IsDiscreteValuationRing.irreducible_iff_uniformizer π).mpr hmax).prime
  refine ⟨isDomain_adjoinRoot_X_pow_sub_C_of_prime hn π hπ, ?_⟩
  intro hdomainB
  refine ⟨isDiscreteValuationRing_adjoinRoot_X_pow_sub_C_of_prime hn π hπ, ?_⟩
  intro hdvrB hflat
  have : Module.Finite V B := (Polynomial.monic_X_pow_sub_C π hn.ne').finite_adjoinRoot
  have : Algebra.IsIntegral V B := Algebra.IsIntegral.of_finite V B
  have hindex : (IsLocalRing.maximalIdeal B).ramificationIdx V = n :=
    ramificationIdx_adjoinRoot_uniformizer hn π hπ
  refine ⟨IsIntegralClosure.of_isIntegrallyClosed B V (FractionRing B), hindex, ?_, ?_⟩
  · exact residueFieldMap_bijective_adjoinRoot_X_pow_sub_C hn
      ((IsLocalRing.mem_maximalIdeal π).mpr hπ.not_isUnit)
  · rw [hindex]
    simpa only [map_natCast] using
      hnUnit.map ((IsLocalRing.residue V).comp (algebraMap A V))

end EtaleFundamentalGroups.Kummer
