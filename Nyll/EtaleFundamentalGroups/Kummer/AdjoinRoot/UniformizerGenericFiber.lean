/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.FieldTheory.Separable
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Etale.Basic
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.TensorProduct.Basic
import Nyll.EtaleFundamentalGroups.Kummer.AdjoinRoot.FormallyEtale
import Nyll.EtaleFundamentalGroups.Kummer.Radicals.Explicit
import Nyll.EtaleFundamentalGroups.Kummer.UnitAbsorption.HigherRadical
import Nyll.EtaleFundamentalGroups.Kummer.UnitAbsorption.HigherRadicalActualFactor
import Nyll.SchemeTheory.RingTheory.GenericFiber.Finite

/-!
# Fraction-field coordinates of a uniformizer root

For a DVR `R` and a prime element `π`, the actual integral root algebra
`B = R[X] / (X ^ n - π)` is a domain. Its fraction field is identified,
as an algebra over `Frac(R)`, with the root algebra of the same equation
over `Frac(R)`. The comparison sends the formal root to the image of the
original integral root, and its algebra structure extends the original
coefficient map through `R → B → Frac(B)`.

Consequently `Frac(B)` has degree `n` over `Frac(R)` and is separable when
`n` is a unit in `R`. No extension field, irreducibility over the fraction
field, or comparison of coefficient maps is supplied as a hypothesis.

This provides the generic-field coordinates for the DVR calculation in
Stacks Project, Example 58.31.4 (tag `0EYF`). The residue and ramification
index calculations are in `UniformizerRamification` and `ReducedBoundary`.
https://stacks.math.columbia.edu/tag/0EYF
-/

noncomputable section

namespace EtaleFundamentalGroups.Kummer

open Polynomial
open scoped TensorProduct

universe u

/-- The literal root algebra over the base fraction field is the fraction
field of the integral root algebra, with its original coefficient map. -/
def uniformizerRootFractionEquiv
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {n : ℕ} (hn : 0 < n) (π : R) (hπ : Prime π) :
    let B := AdjoinRoot (X ^ n - C π)
    let : IsDomain B := isDomain_adjoinRoot_X_pow_sub_C_of_prime hn π hπ
    let : Module.FaithfullyFlat R B := faithfullyFlat_adjoinRoot_X_pow_sub_C hn π
    let : Algebra (FractionRing R) (FractionRing B) :=
      FractionRing.liftAlgebra R (FractionRing B)
    AdjoinRoot (X ^ n - C (algebraMap R (FractionRing R) π)) ≃ₐ[FractionRing R]
      FractionRing B := by
  intro B hdomain hflat hfieldAlgebra
  have : Module.Finite R B := (Polynomial.monic_X_pow_sub_C π hn.ne').finite_adjoinRoot
  have : IsScalarTower R (FractionRing R) (FractionRing B) :=
    FractionRing.isScalarTower_liftAlgebra R (FractionRing B)
  let eRoot : (FractionRing R ⊗[R] B) ≃ₐ[FractionRing R]
      AdjoinRoot (X ^ n - C (algebraMap R (FractionRing R) π)) :=
    (adjoinRootBaseChangeAlgEquiv (S := FractionRing R) (X ^ n - C π)).trans
      (AdjoinRoot.algEquivOfEq (FractionRing R) _ _ (by
        rw [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C]))
  exact eRoot.symm.trans
    (finiteGenericFiberAlgEquiv (R := R) (C := B)
      (K := FractionRing R) (E := FractionRing B))

/-- The field-coordinate comparison retains the actual integral root. -/
theorem uniformizerRootFractionEquiv_root
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {n : ℕ} (hn : 0 < n) (π : R) (hπ : Prime π) :
    let B := AdjoinRoot (X ^ n - C π)
    let : IsDomain B := isDomain_adjoinRoot_X_pow_sub_C_of_prime hn π hπ
    let : Module.FaithfullyFlat R B := faithfullyFlat_adjoinRoot_X_pow_sub_C hn π
    let : Algebra (FractionRing R) (FractionRing B) :=
      FractionRing.liftAlgebra R (FractionRing B)
    uniformizerRootFractionEquiv hn π hπ
        (AdjoinRoot.root (X ^ n - C (algebraMap R (FractionRing R) π))) =
      algebraMap B (FractionRing B) (AdjoinRoot.root (X ^ n - C π)) := by
  intro B hdomain hflat hfieldAlgebra
  have : Module.Finite R B := (Polynomial.monic_X_pow_sub_C π hn.ne').finite_adjoinRoot
  have : IsScalarTower R (FractionRing R) (FractionRing B) :=
    FractionRing.isScalarTower_liftAlgebra R (FractionRing B)
  let eRoot : (FractionRing R ⊗[R] B) ≃ₐ[FractionRing R]
      AdjoinRoot (X ^ n - C (algebraMap R (FractionRing R) π)) :=
    (adjoinRootBaseChangeAlgEquiv (S := FractionRing R) (X ^ n - C π)).trans
      (AdjoinRoot.algEquivOfEq (FractionRing R) _ _ (by
        rw [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C]))
  have hroot : eRoot (1 ⊗ₜ[R] AdjoinRoot.root (X ^ n - C π)) =
      AdjoinRoot.root (X ^ n - C (algebraMap R (FractionRing R) π)) := by
    simp only [eRoot, AlgEquiv.trans_apply]
    rw [adjoinRootBaseChangeAlgEquiv_tmul_root (A := R) (S := FractionRing R)
      (X ^ n - C π), AdjoinRoot.algEquivOfEq_root]
  change finiteGenericFiberAlgEquiv (R := R) (C := B)
    (K := FractionRing R) (E := FractionRing B)
      (eRoot.symm (AdjoinRoot.root (X ^ n - C (algebraMap R (FractionRing R) π)))) = _
  rw [← hroot, AlgEquiv.symm_apply_apply, finiteGenericFiberAlgEquiv_tmul,
    map_one, one_mul]

/-- The fraction field of a positive uniformizer-root algebra is a finite
separable extension of degree `n` when `n` is a unit in the DVR. -/
theorem uniformizerRoot_fractionField_finiteSeparable_degree
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {n : ℕ} (hn : 0 < n) (hnUnit : IsUnit (n : R)) (π : R) (hπ : Prime π) :
    let B := AdjoinRoot (X ^ n - C π)
    let : IsDomain B := isDomain_adjoinRoot_X_pow_sub_C_of_prime hn π hπ
    let : Module.FaithfullyFlat R B := faithfullyFlat_adjoinRoot_X_pow_sub_C hn π
    let : Algebra (FractionRing R) (FractionRing B) :=
      FractionRing.liftAlgebra R (FractionRing B)
    Module.Finite (FractionRing R) (FractionRing B) ∧
      Algebra.IsSeparable (FractionRing R) (FractionRing B) ∧
        Module.finrank (FractionRing R) (FractionRing B) = n := by
  intro B hdomain hflat hfieldAlgebra
  let K := FractionRing R
  let E := FractionRing B
  let D := AdjoinRoot (X ^ n - C (algebraMap R K π))
  let e : D ≃ₐ[K] E := uniformizerRootFractionEquiv hn π hπ
  have hmonic : (X ^ n - C (algebraMap R K π)).Monic :=
    Polynomial.monic_X_pow_sub_C (algebraMap R K π) hn.ne'
  have : Module.Finite K D := hmonic.finite_adjoinRoot
  have : Module.Finite K E := Module.Finite.equiv e.toLinearEquiv
  have hπK : IsUnit (algebraMap R K π) := by
    apply isUnit_iff_ne_zero.mpr
    simpa only [map_zero] using (IsFractionRing.injective R K).ne hπ.ne_zero
  have : Algebra.FormallyEtale K D :=
    formallyEtale_adjoinRoot_X_pow_sub_C hn
      (by simpa only [map_natCast] using hnUnit.map (algebraMap R K)) hπK
  have : Algebra.FormallyEtale K E := Algebra.FormallyEtale.of_equiv e
  refine ⟨inferInstance, (Algebra.FormallyEtale.iff_isSeparable K E).mp inferInstance, ?_⟩
  rw [← e.toLinearEquiv.finrank_eq,
    Module.finrank_eq_card_basis (AdjoinRoot.powerBasisAux' hmonic),
    Fintype.card_fin, Polynomial.natDegree_X_pow_sub_C]

end EtaleFundamentalGroups.Kummer
