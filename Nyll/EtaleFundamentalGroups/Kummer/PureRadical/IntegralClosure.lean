/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Nyll.EtaleFundamentalGroups.Kummer.PureRadical.IntermediateCoordinates

/-!
# The integral closure of a pure radical intermediate field

For a domain `A` with fraction field `K`, let `F = K(β)` and suppose that
`β ^ m = t`.  Once the monogenic root algebra
`A[X] / (X ^ m - t)` is known to be a normal domain, it is the integral
closure of `A` in `F`.  The theorem below produces the resulting canonical
algebra equivalence and records the image of the radical root.
-/

noncomputable section

namespace EtaleFundamentalGroups.Kummer

open Polynomial

universe u v w

/-- The canonical map from a pure-radical root algebra to a field containing
the prescribed root. -/
def pureRadicalAdjoinRootToField
    {A : Type u} {K : Type v} {F : Type w}
    [CommRing A] [Field K] [Field F]
    [Algebra A K] [Algebra K F] [Algebra A F] [IsScalarTower A K F]
    {m : ℕ} (t : A) (β : F)
    (hβpow : β ^ m = algebraMap K F (algebraMap A K t)) :
    AdjoinRoot (X ^ m - C t) →ₐ[A] F := by
  apply AdjoinRoot.liftAlgHom (X ^ m - C t) (Algebra.ofId A F) β
  simp [hβpow, IsScalarTower.algebraMap_apply A K F]

@[simp]
theorem pureRadicalAdjoinRootToField_root
    {A : Type u} {K : Type v} {F : Type w}
    [CommRing A] [Field K] [Field F]
    [Algebra A K] [Algebra K F] [Algebra A F] [IsScalarTower A K F]
    {m : ℕ} (t : A) (β : F)
    (hβpow : β ^ m = algebraMap K F (algebraMap A K t)) :
    pureRadicalAdjoinRootToField t β hβpow
      (AdjoinRoot.root (X ^ m - C t)) = β := by
  simp [pureRadicalAdjoinRootToField]

/-- The canonical pure-radical root map makes the generated field its
fraction field.

The fraction-field assertion is proved inside the theorem.  It is not an
input: fractions in the root algebra form an intermediate field containing
both `K` and `β`, hence all of `F`. -/
theorem isFractionRing_adjoinRoot_of_pureRadical
    {A : Type u} {K : Type v} {F : Type w}
    [CommRing A] [IsDomain A]
    [Field K] [Field F]
    [Algebra A K] [IsFractionRing A K]
    [Algebra K F] [Algebra A F] [IsScalarTower A K F]
    [FiniteDimensional K F]
    {m : ℕ} (hm : 0 < m) (t : A) (β : F)
    (hdegree : Module.finrank K F = m)
    (hβpow : β ^ m = algebraMap K F (algebraMap A K t))
    (hgen : IntermediateField.adjoin K {β} = ⊤) :
    let φ := pureRadicalAdjoinRootToField t β hβpow
    letI : Algebra (AdjoinRoot (X ^ m - C t)) F :=
      φ.toRingHom.toAlgebra
    IsFractionRing (AdjoinRoot (X ^ m - C t)) F := by
  let p : A[X] := X ^ m - C t
  let R := AdjoinRoot p
  have hm0 : m ≠ 0 := hm.ne'
  have hpMonic : p.Monic := Polynomial.monic_X_pow_sub_C t hm0
  have hβintK : IsIntegral K β := IsIntegral.of_finite K β
  have hminDegree : (minpoly K β).natDegree = m := by
    have h := IntermediateField.adjoin.finrank hβintK
    rw [hgen] at h
    calc
      (minpoly K β).natDegree = Module.finrank K F := by
        simpa only [IntermediateField.finrank_top'] using h.symm
      _ = m := hdegree
  have hpMapRoot :
      Polynomial.aeval β (p.map (algebraMap A K)) = 0 := by
    simp [p, hβpow]
  have hminDvd : minpoly K β ∣ p.map (algebraMap A K) :=
    minpoly.dvd K β hpMapRoot
  have hpMapEq : p.map (algebraMap A K) = minpoly K β := by
    apply Polynomial.eq_of_monic_of_dvd_of_natDegree_le
      (minpoly.monic hβintK) (hpMonic.map (algebraMap A K)) hminDvd
    have hpMapDegree : (p.map (algebraMap A K)).natDegree = m := by
      simp [p]
    rw [hpMapDegree, hminDegree]
  let φ : R →ₐ[A] F :=
    pureRadicalAdjoinRootToField t β hβpow
  have hφInjective : Function.Injective φ := by
    rw [RingHom.injective_iff_ker_eq_bot]
    apply le_antisymm
    · intro z hz
      have hzmap : φ z = 0 := RingHom.mem_ker.mp hz
      have hz0 : z = 0 := by
        induction z using AdjoinRoot.induction_on with
        | _ q =>
            change q.eval₂ (Algebra.ofId A F) β = 0 at hzmap
            rw [AdjoinRoot.mk_eq_zero]
            apply (Polynomial.map_dvd_map (algebraMap A K)
              (IsFractionRing.injective A K) hpMonic).mp
            rw [hpMapEq]
            apply minpoly.dvd K β
            rw [Polynomial.aeval_def, Polynomial.eval₂_map,
              ← IsScalarTower.algebraMap_eq A K F]
            exact hzmap
      simpa only [Ideal.mem_bot] using hz0
    · exact bot_le
  let : Algebra R F := φ.toRingHom.toAlgebra
  let : IsScalarTower A R F :=
    IsScalarTower.of_algebraMap_eq fun a ↦ (φ.commutes a).symm
  have hRF : Function.Injective (algebraMap R F) := by
    exact hφInjective
  let : IsDomain R := hRF.isDomain _
  let : FaithfulSMul R F :=
    (faithfulSMul_iff_algebraMap_injective R F).mpr hRF
  have hAR : Function.Injective (algebraMap A R) := by
    intro a b hab
    apply IsFractionRing.injective A K
    apply (algebraMap K F).injective
    calc
      algebraMap K F (algebraMap A K a) = algebraMap A F a :=
        (IsScalarTower.algebraMap_apply A K F a).symm
      _ = algebraMap R F (algebraMap A R a) :=
        IsScalarTower.algebraMap_apply A R F a
      _ = algebraMap R F (algebraMap A R b) := by rw [hab]
      _ = algebraMap A F b :=
        (IsScalarTower.algebraMap_apply A R F b).symm
      _ = algebraMap K F (algebraMap A K b) :=
        IsScalarTower.algebraMap_apply A K F b
  let fractionSubfield : Subfield F :=
    { carrier := {z | ∃ x y : R, y ≠ 0 ∧
          z = algebraMap R F x / algebraMap R F y}
      zero_mem' := ⟨0, 1, one_ne_zero, by simp⟩
      one_mem' := ⟨1, 1, one_ne_zero, by simp⟩
      add_mem' := by
        rintro z w ⟨a, b, hb, rfl⟩ ⟨c, d, hd, rfl⟩
        refine ⟨a * d + c * b, b * d, mul_ne_zero hb hd, ?_⟩
        rw [map_add, map_mul, map_mul, map_mul]
        calc
          algebraMap R F a / algebraMap R F b +
              algebraMap R F c / algebraMap R F d =
              (algebraMap R F a * algebraMap R F d +
                algebraMap R F b * algebraMap R F c) /
                (algebraMap R F b * algebraMap R F d) :=
            div_add_div _ _
              ((map_ne_zero_iff (algebraMap R F) hRF).2 hb)
              ((map_ne_zero_iff (algebraMap R F) hRF).2 hd)
          _ = (algebraMap R F a * algebraMap R F d +
                algebraMap R F c * algebraMap R F b) /
                (algebraMap R F b * algebraMap R F d) := by ring
      neg_mem' := by
        rintro z ⟨a, b, hb, rfl⟩
        exact ⟨-a, b, hb, by rw [map_neg, neg_div]⟩
      mul_mem' := by
        rintro z w ⟨a, b, hb, rfl⟩ ⟨c, d, hd, rfl⟩
        refine ⟨a * c, b * d, mul_ne_zero hb hd, ?_⟩
        rw [map_mul, map_mul]
        exact div_mul_div_comm _ _ _ _
      inv_mem' := by
        rintro z ⟨a, b, hb, rfl⟩
        by_cases ha : a = 0
        · exact ⟨0, 1, one_ne_zero, by simp [ha]⟩
        · refine ⟨b, a, ha, ?_⟩
          rw [inv_div]
          }
  have hKmem (k : K) : algebraMap K F k ∈ fractionSubfield := by
    obtain ⟨a, b, hb, hk⟩ := IsFractionRing.div_surjective A k
    refine ⟨algebraMap A R a, algebraMap A R b,
      (map_ne_zero_iff (algebraMap A R) hAR).2 ?_, ?_⟩
    · exact nonZeroDivisors.ne_zero hb
    · calc
        algebraMap K F k =
            algebraMap K F
              (algebraMap A K a / algebraMap A K b) := by rw [hk]
        _ = algebraMap A F a / algebraMap A F b := by
          rw [map_div₀, IsScalarTower.algebraMap_apply A K F,
            IsScalarTower.algebraMap_apply A K F]
        _ = algebraMap R F (algebraMap A R a) /
            algebraMap R F (algebraMap A R b) := by
          rw [IsScalarTower.algebraMap_apply A R F,
            IsScalarTower.algebraMap_apply A R F]
  have hβmem : β ∈ fractionSubfield := by
    refine ⟨AdjoinRoot.root p, 1, one_ne_zero, ?_⟩
    change β = φ (AdjoinRoot.root p) / φ 1
    rw [map_one, div_one]
    exact (pureRadicalAdjoinRootToField_root t β hβpow).symm
  let E : IntermediateField K F :=
    fractionSubfield.toIntermediateField hKmem
  have hEtop : E = ⊤ := by
    apply top_unique
    rw [← hgen, IntermediateField.adjoin_le_iff]
    intro z hz
    rw [Set.mem_singleton_iff.mp hz]
    exact hβmem
  have hsurjective : ∀ z : F, ∃ x y : R,
      z = algebraMap R F x / algebraMap R F y := by
    intro z
    have hz : z ∈ E := by rw [hEtop]; trivial
    change z ∈ fractionSubfield at hz
    obtain ⟨x, y, _hy, hxy⟩ := hz
    exact ⟨x, y, hxy⟩
  exact IsFractionRing.of_field R F hsurjective

/-- A normal pure-radical root algebra is canonically the integral closure in
the generated fraction field.  The equivalence sends the radical root to the
prescribed field generator. -/
theorem exists_adjoinRoot_algEquiv_integralClosure_of_pureRadical
    {A : Type u} {K : Type v} {F : Type w}
    [CommRing A] [IsDomain A]
    [Field K] [Field F]
    [Algebra A K] [IsFractionRing A K]
    [Algebra K F] [Algebra A F] [IsScalarTower A K F]
    [FiniteDimensional K F]
    {m : ℕ} (hm : 0 < m) (t : A) (β : F)
    (hdegree : Module.finrank K F = m)
    (hβpow : β ^ m = algebraMap K F (algebraMap A K t))
    (hgen : IntermediateField.adjoin K {β} = ⊤)
    [IsIntegrallyClosed (AdjoinRoot (X ^ m - C t))] :
    ∃ e : AdjoinRoot (X ^ m - C t) ≃ₐ[A] integralClosure A F,
      algebraMap (integralClosure A F) F
        (e (AdjoinRoot.root (X ^ m - C t))) = β := by
  let p : A[X] := X ^ m - C t
  let R := AdjoinRoot p
  let φ : R →ₐ[A] F :=
    pureRadicalAdjoinRootToField t β hβpow
  let : Algebra R F := φ.toRingHom.toAlgebra
  let : IsFractionRing R F :=
    isFractionRing_adjoinRoot_of_pureRadical
      hm t β hdegree hβpow hgen
  let : IsDomain R := (IsFractionRing.injective R F).isDomain _
  let : IsScalarTower A R F :=
    IsScalarTower.of_algebraMap_eq fun a ↦ (φ.commutes a).symm
  have hpMonic : p.Monic :=
    Polynomial.monic_X_pow_sub_C t hm.ne'
  let : Module.Finite A R := hpMonic.finite_adjoinRoot
  let : Algebra.IsIntegral A R := Algebra.IsIntegral.of_finite A R
  let e : R ≃ₐ[A] integralClosure A F :=
    IsIntegralClosure.equiv A R F (integralClosure A F)
  refine ⟨e, ?_⟩
  rw [IsIntegralClosure.algebraMap_equiv]
  change φ (AdjoinRoot.root p) = β
  exact pureRadicalAdjoinRootToField_root t β hβpow

end EtaleFundamentalGroups.Kummer
