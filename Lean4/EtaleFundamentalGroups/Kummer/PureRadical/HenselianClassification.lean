/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import EtaleFundamentalGroups.Kummer.PureRadical.IntermediateField

/-!
# Pure-radical classification over a Henselian local base

The abstract intermediate-field theorem needs to know that the relevant
roots of unity in the radical field already lie in the base field.  This
file produces that input from the integral local model used in the
one-divisor Abhyankar argument: a Henselian base, an integral normal local
algebra with the same residue field, and its fraction field.
-/

noncomputable section

namespace EtaleFundamentalGroups.Kummer

open Polynomial

universe u v w x

/-- A root of unity in the fraction field of an integral normal local
extension with unchanged residue field comes from the fraction field of the
Henselian base.

The unit condition on `n` makes `X ^ n - 1` separable at every root.  The
root is first pulled into the integral closure, its residue is lifted by
Hensel's lemma, and uniqueness of a simple root in the target local domain
identifies the two lifts. -/
theorem rootOfUnity_mem_fractionBase_of_henselian_of_residue_bijective
    {A : Type u} {B : Type v} {K : Type w} {L : Type x}
    [CommRing A] [CommRing B] [IsDomain B]
    [HenselianLocalRing A] [IsLocalRing B]
    [Field K] [Field L]
    [Algebra A B] [Algebra A K] [Algebra B L] [Algebra K L]
    [Algebra A L] [IsScalarTower A B L] [IsScalarTower A K L]
    [IsFractionRing B L] [IsIntegrallyClosed B]
    [Algebra.IsIntegral A B] [IsLocalHom (algebraMap A B)]
    {n : ℕ} (hnUnit : IsUnit (n : A))
    (hresidue : Function.Bijective
      (IsLocalRing.ResidueField.map (algebraMap A B)))
    (ζ : L) (hζpow : ζ ^ n = 1) :
    ζ ∈ Set.range (algebraMap K L) := by
  have hn : n ≠ 0 := by
    intro hn
    subst n
    simp at hnUnit
  let f : A[X] := X ^ n - C 1
  have hfMonic : f.Monic := Polynomial.monic_X_pow_sub_C 1 hn
  have hζIntegral : IsIntegral A ζ := by
    refine ⟨f, hfMonic, ?_⟩
    simp [f, hζpow]
  let b : B := IsIntegralClosure.mk' B ζ hζIntegral
  have hbL : algebraMap B L b = ζ := by
    exact IsIntegralClosure.algebraMap_mk' B ζ hζIntegral
  have hbpow : b ^ n = 1 := by
    apply IsFractionRing.injective B L
    rw [map_pow, hbL, hζpow, map_one]
  let residueMap := IsLocalRing.ResidueField.map (algebraMap A B)
  obtain ⟨a₀, ha₀⟩ :=
    hresidue.2 (IsLocalRing.residue B b)
  have ha₀pow : a₀ ^ n = 1 := by
    apply hresidue.1
    calc
      residueMap (a₀ ^ n) = residueMap a₀ ^ n := map_pow _ _ _
      _ = IsLocalRing.residue B b ^ n := by rw [ha₀]
      _ = IsLocalRing.residue B (b ^ n) := (map_pow _ _ _).symm
      _ = 1 := by rw [hbpow, map_one]
      _ = residueMap 1 := (map_one _).symm
  have ha₀ne : a₀ ≠ 0 := by
    intro ha₀zero
    rw [ha₀zero, zero_pow hn] at ha₀pow
    exact zero_ne_one ha₀pow
  have hnResidue : (n : IsLocalRing.ResidueField A) ≠ 0 := by
    simpa using
      (IsLocalRing.residue_ne_zero_iff_isUnit (n : A)).2 hnUnit
  have hfRootResidue : Polynomial.aeval a₀ f = 0 := by
    simp [f, ha₀pow]
  have hfDerivativeResidue : Polynomial.aeval a₀ f.derivative ≠ 0 := by
    simpa [f, Polynomial.derivative_X_pow] using
      mul_ne_zero hnResidue (pow_ne_zero (n - 1) ha₀ne)
  have hHensel := ((HenselianLocalRing.TFAE A).out 1 2).mp
    (inferInstance : HenselianLocalRing A)
  obtain ⟨a, haRoot, haResidue⟩ :=
    hHensel f hfMonic a₀ hfRootResidue hfDerivativeResidue
  have hbUnit : IsUnit b := by
    rw [isUnit_iff_exists_inv]
    refine ⟨b ^ (n - 1), ?_⟩
    rw [← pow_succ', Nat.sub_add_cancel (Nat.pos_of_ne_zero hn), hbpow]
  have hresidueB :
      IsLocalRing.residue B (algebraMap A B a) =
        IsLocalRing.residue B b := by
    rw [← IsLocalRing.ResidueField.map_residue, haResidue, ha₀]
  have hnotUnit : ¬ IsUnit (b - algebraMap A B a) := by
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit]
    simp [hresidueB]
  have hbRoot : (f.map (algebraMap A B)).eval b = 0 := by
    simp [f, hbpow]
  have hmapRoot :
      (f.map (algebraMap A B)).eval (algebraMap A B a) = 0 := by
    simpa [Polynomial.eval_map] using
      congrArg (algebraMap A B) (Polynomial.IsRoot.def.mp haRoot)
  have hbDerivativeUnit :
      IsUnit ((f.map (algebraMap A B)).derivative.eval b) := by
    simpa [f, Polynomial.derivative_map, Polynomial.derivative_X_pow] using
      (hnUnit.map (algebraMap A B)).mul (hbUnit.pow (n - 1))
  have hbEq : b = algebraMap A B a := by
    exact IsLocalRing.eq_of_eval_eq_zero_of_not_isUnit_sub
      hbRoot hmapRoot hnotUnit hbDerivativeUnit
  refine ⟨algebraMap A K a, ?_⟩
  calc
    algebraMap K L (algebraMap A K a) = algebraMap A L a :=
      (IsScalarTower.algebraMap_apply A K L a).symm
    _ = algebraMap B L (algebraMap A B a) := by
      rw [IsScalarTower.algebraMap_apply A B L]
    _ = algebraMap B L b := by rw [hbEq]
    _ = ζ := hbL

/-- Henselian integral-model form of the pure-radical intermediate-field
classification.  The roots-of-unity hypothesis of the abstract theorem is
produced from the normal local integral model and its unchanged residue
field. -/
theorem exists_intermediateField_eq_adjoin_pow_of_henselian_pureRadical
    {A : Type u} {B : Type v} {K : Type w} {L : Type x}
    [CommRing A] [CommRing B] [IsDomain B]
    [HenselianLocalRing A] [IsLocalRing B]
    [Field K] [Field L]
    [Algebra A B] [Algebra A K] [Algebra B L] [Algebra K L]
    [Algebra A L] [IsScalarTower A B L] [IsScalarTower A K L]
    [IsFractionRing B L] [IsIntegrallyClosed B]
    [Algebra.IsIntegral A B] [IsLocalHom (algebraMap A B)]
    [FiniteDimensional K L]
    (α : L) (hα : α ≠ 0)
    (hpow : α ^ Module.finrank K L ∈ Set.range (algebraMap K L))
    (hgen : IntermediateField.adjoin K {α} = ⊤)
    (hdegreeUnit : IsUnit (Module.finrank K L : A))
    (hresidue : Function.Bijective
      (IsLocalRing.ResidueField.map (algebraMap A B)))
    (F : IntermediateField K L) :
    ∃ d : ℕ, d ∣ Module.finrank K L ∧
      F = IntermediateField.adjoin K {α ^ d} := by
  apply exists_intermediateField_eq_adjoin_pow_of_pureRadical
    α hα hpow hgen
  intro ζ hζpow
  exact rootOfUnity_mem_fractionBase_of_henselian_of_residue_bijective
    hdegreeUnit hresidue ζ hζpow

end EtaleFundamentalGroups.Kummer
