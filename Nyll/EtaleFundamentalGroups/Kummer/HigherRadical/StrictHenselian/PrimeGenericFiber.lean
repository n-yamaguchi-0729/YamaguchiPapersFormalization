/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Kummer.HigherRadical.UnitFactor.StrictHenselianLocalization

/-!
# The closed retained-factor prime and the higher generic fibre

The prime produced by strict-Henselian splitting is a closed prime of the
retained lower factor.  After base change to a higher root and passage to
the fraction field of that higher root ring, its extension is the unit
ideal: the lower radical root becomes a power of the now-invertible higher
root.

Consequently this closed prime cannot be the contraction of a proper
generic-component ideal.  Any comparison with a fixed generic component
must therefore pass through an integral or localized component before the
higher-root generic fibre is formed.
-/

noncomputable section

open scoped TensorProduct

namespace EtaleFundamentalGroups.Kummer

open Polynomial
open ValuationTheory.DiscreteValuationField
open ValuationTheory.DiscreteValuationField.ValuedExtension

universe uK uV uF uL uW

/-- A closed prime of the retained lower factor maps to the unit ideal in
the higher-root generic fibre.

The statement applies in particular to the prime produced by
`higherRadicalUnitFactorData_exists_strictHenselian_localizationAlgEquiv`.
No compatibility with a chosen generic component is assumed. -/
theorem higherRadicalUnitFactorData_closedPrime_map_higherGenericFiber_eq_top
    {K : Type uK} {Froot : Type uF} {L : Type uL}
    [Field K] [Field Froot] [Field L] [Algebra K L]
    (base : DVF.{uK, uV} K) (target : DVF.{uL, uW} L)
    [base.valuation.HasExtension target.valuation]
    [Module.Finite base.valuationSubring target.valuationSubring]
    {N : ℕ} (hN : 0 < N)
    (varpi : base.valuationSubring)
    (hvarpi : base.valuation.IsUniformizer (varpi : K))
    (hdiv : ramificationIndex base target ∣ N)
    (pi : target.valuationSubring)
    (beta : AlgebraicClosure L)
    (factor : HigherRadicalUnitFactorData base target varpi pi N beta)
    [Algebra (AdjoinRoot (X ^ N - C varpi)) Froot]
    [IsFractionRing (AdjoinRoot (X ^ N - C varpi)) Froot]
    [HenselianLocalRing
      (AdjoinRoot
        (X ^ ramificationIndex base target - C varpi))]
    (q :
      let e := ramificationIndex base target
      let Rₑ := AdjoinRoot (X ^ e - C varpi)
      let Cq := AdjoinRoot factor.q
      letI : Algebra Rₑ Cq :=
        factor.radicalToUnitFactor.toRingHom.toAlgebra
      (IsLocalRing.maximalIdeal Rₑ).primesOver Cq) :
    let e := ramificationIndex base target
    let Rₑ := AdjoinRoot (X ^ e - C varpi)
    let Rₙ := AdjoinRoot (X ^ N - C varpi)
    let Cq := AdjoinRoot factor.q
    let higherRootMap : Rₑ →ₐ[base.valuationSubring] Rₙ :=
      adjoinRootPowerMapOfDvd hdiv varpi
    letI : Algebra Rₑ Rₙ := higherRootMap.toRingHom.toAlgebra
    letI : Algebra Rₑ Cq :=
      factor.radicalToUnitFactor.toRingHom.toAlgebra
    let Tₙ := Rₙ ⊗[Rₑ] Cq
    let G := Froot ⊗[Rₙ] Tₙ
    let cToG : Cq →+* G :=
      (Algebra.TensorProduct.includeRight : Tₙ →ₐ[Rₙ] G).toRingHom.comp
        (Algebra.TensorProduct.includeRight : Cq →ₐ[Rₑ] Tₙ).toRingHom
    q.1.map cToG = ⊤ := by
  dsimp only
  let V := base.valuationSubring
  let e := ramificationIndex base target
  let Rₑ := AdjoinRoot (X ^ e - C varpi)
  let Rₙ := AdjoinRoot (X ^ N - C varpi)
  let Cq := AdjoinRoot factor.q
  let higherRootMap : Rₑ →ₐ[V] Rₙ :=
    adjoinRootPowerMapOfDvd hdiv varpi
  let : Algebra Rₑ Rₙ := higherRootMap.toRingHom.toAlgebra
  let : Algebra Rₑ Cq :=
    factor.radicalToUnitFactor.toRingHom.toAlgebra
  let Tₙ := Rₙ ⊗[Rₑ] Cq
  let G := Froot ⊗[Rₙ] Tₙ
  let cToG : Cq →+* G :=
    (Algebra.TensorProduct.includeRight : Tₙ →ₐ[Rₙ] G).toRingHom.comp
      (Algebra.TensorProduct.includeRight : Cq →ₐ[Rₑ] Tₙ).toRingHom
  let rootₑ : Rₑ := AdjoinRoot.root (X ^ e - C varpi)
  let rootₙ : Rₙ := AdjoinRoot.root (X ^ N - C varpi)
  have he : 0 < e := ramificationIndex_pos_of_moduleFinite base target
  have hvarpiMem : varpi ∈ IsLocalRing.maximalIdeal V :=
    (IsLocalRing.mem_maximalIdeal _).2
      (dvfUniformizer_prime base varpi hvarpi).not_isUnit
  have hrootₑMax : rootₑ ∈ IsLocalRing.maximalIdeal Rₑ := by
    rw [maximalIdeal_adjoinRoot_X_pow_sub_C he hvarpiMem]
    apply (show Ideal.span {rootₑ} ≤
        localRootCoverClosedIdeal V e varpi from le_sup_right)
    exact Ideal.mem_span_singleton_self rootₑ
  have hrootₑq : algebraMap Rₑ Cq rootₑ ∈ q.1 :=
    (Ideal.mem_of_liesOver
      (P := q.1) (p := IsLocalRing.maximalIdeal Rₑ) rootₑ).mp hrootₑMax
  let : IsDomain Rₙ :=
    isDomain_adjoinRoot_X_pow_sub_C_of_prime hN varpi
      (dvfUniformizer_prime base varpi hvarpi)
  let : Module.FaithfullyFlat V Rₙ :=
    faithfullyFlat_adjoinRoot_X_pow_sub_C hN varpi
  have hrootₙne : rootₙ ≠ 0 := by
    intro hroot
    apply hvarpi.ne_zero
    have hsub : varpi = 0 := by
      apply FaithfulSMul.algebraMap_injective V Rₙ
      rw [AdjoinRoot.algebraMap_eq]
      rw [show AdjoinRoot.of (X ^ N - C varpi) varpi = rootₙ ^ N by
        simpa only [rootₙ] using (adjoinRoot_root_pow N varpi).symm]
      simp [hroot, hN.ne']
    exact congrArg (fun z : V ↦ (z : K)) hsub
  have hrootₙFne : algebraMap Rₙ Froot rootₙ ≠ 0 :=
    by simpa only [map_zero] using
      (IsFractionRing.injective Rₙ Froot).ne hrootₙne
  have hrootₙFunit : IsUnit (algebraMap Rₙ Froot rootₙ) :=
    isUnit_iff_ne_zero.mpr hrootₙFne
  have hrootₙGunit : IsUnit (algebraMap Rₙ G rootₙ) := by
    have hmap := hrootₙFunit.map
      (Algebra.TensorProduct.includeLeft : Froot →ₐ[Rₙ] G)
    rw [← (Algebra.TensorProduct.includeLeft : Froot →ₐ[Rₙ] G).commutes]
    exact hmap
  have hrootImage :
      cToG (algebraMap Rₑ Cq rootₑ) =
        algebraMap Rₙ G (higherRootMap rootₑ) := by
    let inC : Cq →ₐ[Rₑ] Tₙ := Algebra.TensorProduct.includeRight
    let inR : Rₙ →ₐ[Rₑ] Tₙ := Algebra.TensorProduct.includeLeft
    let inT : Tₙ →ₐ[Rₙ] G := Algebra.TensorProduct.includeRight
    let inF : Froot →ₐ[Rₙ] G := Algebra.TensorProduct.includeLeft
    have hinner (z : Rₑ) :
        inC (algebraMap Rₑ Cq z) =
          inR (algebraMap Rₑ Rₙ z) := by
      exact DFunLike.congr_fun
        (Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap
          (R := Rₑ) (A := Rₙ) (B := Cq)).symm z
    have houter (z : Rₙ) :
        inT (inR z) = algebraMap Rₙ G z := by
      calc
        inT (inR z) = inT (algebraMap Rₙ Tₙ z) := rfl
        _ = inF (algebraMap Rₙ Froot z) :=
          DFunLike.congr_fun
            (Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap
              (R := Rₙ) (A := Froot) (B := Tₙ)).symm z
        _ = algebraMap Rₙ G z := inF.commutes z
    change inT (inC (algebraMap Rₑ Cq rootₑ)) =
      algebraMap Rₙ G (higherRootMap rootₑ)
    rw [hinner, houter]
    rfl
  have hrootₑGunit : IsUnit (cToG (algebraMap Rₑ Cq rootₑ)) := by
    rw [hrootImage, adjoinRootPowerMapOfDvd_root]
    rw [map_pow]
    exact hrootₙGunit.pow _
  apply (q.1.map cToG).eq_top_of_isUnit_mem
    (Ideal.mem_map_of_mem cToG hrootₑq)
  exact hrootₑGunit

/-- If an ideal maps to the unit ideal, it cannot be contained in the
contraction of a proper target ideal. -/
theorem not_le_comap_of_map_eq_top
    {A : Type uK} {B : Type uL} [CommRing A] [CommRing B]
    (f : A →+* B) (p : Ideal A) (J : Ideal B)
    (hp : p.map f = ⊤) (hJ : J ≠ ⊤) :
    ¬p ≤ J.comap f := by
  intro h
  have hmap : p.map f ≤ J := Ideal.map_le_iff_le_comap.mpr h
  rw [hp] at hmap
  exact hJ (top_unique hmap)

end EtaleFundamentalGroups.Kummer

end
