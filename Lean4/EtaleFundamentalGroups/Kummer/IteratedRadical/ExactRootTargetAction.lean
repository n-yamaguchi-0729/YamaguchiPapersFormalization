/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Kummer.Henselian.UniformizerDecomposition
import EtaleFundamentalGroups.Kummer.IteratedRadical.TargetAction
import EtaleFundamentalGroups.Kummer.SelectedRoot.Exact.FixedTensorComponentBijective

/-!
# A full iterated-radical action from one exact final root

The roots already adjoined in an iterated-radical prefix have canonical
images in every algebra over that prefix.  Thus the only new coordinate
needed for one further stage is its final root.  At the exact ramification
index, that root is produced inside a fixed generic tensor component and is
pulled back to the target field by the exact-unit-factor component
comparison.

Appending these coordinates gives one action of the entire root cover on a
single target field.  Exponent-one stages need no separate branch: their
canonical prefix coordinates satisfy the same power equation.

This is a conditional assembly leaf.  In the selected-prefix application,
the raw localized DVR theorem supplies the prefix map and valued extension,
but not the finite valuation-ring extension or the strict-Henselian exact
root input used below.  Those data must come from the later chosen-factor or
filtered-descent bridge; they are not consequences of completion alone.
-/

noncomputable section

open scoped TensorProduct

namespace EtaleFundamentalGroups.Kummer

open Polynomial
open ValuationTheory.DiscreteValuationField
open ValuationTheory.DiscreteValuationField.ValuedExtension

universe uA uK uV uF uL uW

/-- One new target root extends all canonical prefix roots to a simultaneous
action of the `Fin.snoc` cover on the same target.

This is the finite-stage consumer for a descended exact-root factor.  It is
independent of how the last root was produced: a filtered finite-etale stage,
a fixed tensor component, or any other source can supply `z` and `hz`.
Exponent-one prefix stages are retained literally through their canonical
distinguished roots. -/
theorem exists_iteratedRadicalTargetAction_of_prefix_and_lastRoot
    {A : Type uA} {S : Type uL}
    [CommRing A] [IsDomain A]
    [CommRing S] [Algebra A S] [FaithfulSMul A S]
    {r : ℕ} (n : Fin r → ℕ) (a : Fin r → A)
    (hn : ∀ i, 0 < n i)
    [Algebra (iteratedRadical A r n a) S]
    [IsScalarTower A (iteratedRadical A r n a) S]
    (N : ℕ) (hN : 0 < N) (y : A)
    (z : S) (hz : z ^ N = algebraMap A S y)
    [IsDomain
      (iteratedRadical A (r + 1) (Fin.snoc n N) (Fin.snoc a y))] :
    let nFull : Fin (r + 1) → ℕ := Fin.snoc n N
    let aFull : Fin (r + 1) → A := Fin.snoc a y
    ∃ (x : Fin (r + 1) → S)
        (hx : ∀ i, x i ^ nFull i = algebraMap A S (aFull i)),
      Function.Injective
          (iteratedRadicalTargetAlgHom nFull aFull x hx) ∧
        (∀ i : Fin r,
          x i.castSucc =
            algebraMap (iteratedRadical A r n a) S
              (iteratedRadicalRoot A n a i)) ∧
        x (Fin.last r) = z := by
  dsimp only
  let nFull : Fin (r + 1) → ℕ := Fin.snoc n N
  let aFull : Fin (r + 1) → A := Fin.snoc a y
  let prefixRoot : Fin r → S := fun i ↦
    algebraMap (iteratedRadical A r n a) S
      (iteratedRadicalRoot A n a i)
  let xFull : Fin (r + 1) → S := Fin.snoc prefixRoot z
  have hnFull : ∀ i, 0 < nFull i := by
    intro i
    refine Fin.lastCases ?_ (fun j ↦ ?_) i
    · simpa [nFull] using hN
    · simpa [nFull] using hn j
  have hxFull : ∀ i,
      xFull i ^ nFull i = algebraMap A S (aFull i) := by
    intro i
    refine Fin.lastCases ?_ (fun j ↦ ?_) i
    · simpa [xFull, nFull, aFull] using hz
    · simp only [xFull, nFull, aFull, prefixRoot, Fin.snoc_castSucc]
      rw [← map_pow, iteratedRadicalRoot_pow]
      exact
        (IsScalarTower.algebraMap_apply A
          (iteratedRadical A r n a) S (a j)).symm
  refine ⟨xFull, hxFull, ?_, ?_, ?_⟩
  · exact
      iteratedRadicalTargetAlgHom_injective
        nFull aFull hnFull xFull hxFull
  · intro i
    simp [xFull, prefixRoot]
  · simp [xFull]

/-- An algebra over the one-step exact root ring supplies the last coordinate
needed by `exists_iteratedRadicalTargetAction_of_prefix_and_lastRoot`.

This is the application shape for a finite stage returned by filtered
descent: the stage's structure map from the exact root ring produces the new
root, while its already supplied prefix algebra retains every earlier
coordinate in the same stage. -/
theorem exists_iteratedRadicalTargetAction_of_prefix_and_lastRootAlgebra
    {A : Type uA} {S : Type uL}
    [CommRing A] [IsDomain A]
    [CommRing S] [Algebra A S] [FaithfulSMul A S]
    {r : ℕ} (n : Fin r → ℕ) (a : Fin r → A)
    (hn : ∀ i, 0 < n i)
    [Algebra (iteratedRadical A r n a) S]
    [IsScalarTower A (iteratedRadical A r n a) S]
    (N : ℕ) (hN : 0 < N) (y : A)
    [Algebra (AdjoinRoot (X ^ N - C y)) S]
    [IsScalarTower A (AdjoinRoot (X ^ N - C y)) S]
    [IsDomain
      (iteratedRadical A (r + 1) (Fin.snoc n N) (Fin.snoc a y))] :
    let nFull : Fin (r + 1) → ℕ := Fin.snoc n N
    let aFull : Fin (r + 1) → A := Fin.snoc a y
    ∃ (x : Fin (r + 1) → S)
        (hx : ∀ i, x i ^ nFull i = algebraMap A S (aFull i)),
      Function.Injective
          (iteratedRadicalTargetAlgHom nFull aFull x hx) ∧
        (∀ i : Fin r,
          x i.castSucc =
            algebraMap (iteratedRadical A r n a) S
              (iteratedRadicalRoot A n a i)) := by
  let Rn := AdjoinRoot (X ^ N - C y)
  let z : S := algebraMap Rn S (AdjoinRoot.root (X ^ N - C y))
  have hz : z ^ N = algebraMap A S y := by
    calc
      z ^ N = algebraMap Rn S
          (AdjoinRoot.root (X ^ N - C y) ^ N) :=
        (map_pow (algebraMap Rn S)
          (AdjoinRoot.root (X ^ N - C y)) N).symm
      _ = algebraMap Rn S (algebraMap A Rn y) := by
        rw [adjoinRoot_root_pow, AdjoinRoot.algebraMap_eq]
      _ = algebraMap A S y :=
        (IsScalarTower.algebraMap_apply A Rn S y).symm
  obtain ⟨x, hx, hinjective, hprefix, -⟩ :=
    exists_iteratedRadicalTargetAction_of_prefix_and_lastRoot
      n a hn N hN y z hz
  exact ⟨x, hx, hinjective, hprefix⟩

/-- The exact ramification-index radical has a root in the target field.

The distinguished root is first taken in a canonical component of
`Froot ⊗[K] L`.  A target uniformizer and its unit decomposition produce
`HigherRadicalUnitFactorData`; the exact-root comparison then makes the
canonical right map `L → component` surjective, so the component root can
be pulled back to `L` itself. -/
theorem exists_targetRoot_of_exactRamificationIndex
    {K : Type uK} {Froot : Type uF} {L : Type uL}
    [Field K] [Field Froot] [Field L]
    [Algebra K Froot] [Algebra K L]
    (base : DVF.{uK, uV} K) (target : DVF.{uL, uW} L)
    [base.valuation.HasExtension target.valuation]
    [CharZero base.residueField]
    [Module.Finite base.valuationSubring target.valuationSubring]
    (varpi : base.valuationSubring)
    (hvarpi : base.valuation.IsUniformizer (varpi : K))
    (N : ℕ) (hExact : ramificationIndex base target = N)
    [Algebra (AdjoinRoot (X ^ N - C varpi)) Froot]
    [IsFractionRing (AdjoinRoot (X ^ N - C varpi)) Froot]
    [Algebra base.valuationSubring Froot]
    [IsScalarTower base.valuationSubring
      (AdjoinRoot (X ^ N - C varpi)) Froot]
    [IsScalarTower base.valuationSubring K Froot]
    [HenselianLocalRing (AdjoinRoot (X ^ N - C varpi))]
    [IsSepClosed
      (IsLocalRing.ResidueField (AdjoinRoot (X ^ N - C varpi)))] :
    ∃ x : L, x ^ N = algebraMap K L (varpi : K) := by
  subst N
  let V := base.valuationSubring
  let e := ramificationIndex base target
  let : IsDiscreteValuationRing V :=
    base.valuationSubring_isDiscreteValuationRing
  let : IsFractionRing V K := base.valuationSubring_isFractionRing
  have he : 0 < e := ramificationIndex_pos_of_moduleFinite base target
  have hvarpiPrime : Prime varpi :=
    dvfUniformizer_prime base varpi hvarpi
  let m := genericTensorMaximalIdeal (K := K) (K' := Froot) (L := L)
  let : m.IsMaximal := genericTensorMaximalIdeal_isMaximal
  let P := GenericTensorFieldComponent m
  let : Algebra L P := genericTensorFieldComponentRightAlgebra m
  let : IsScalarTower K L P :=
    genericTensorFieldComponent_right_isScalarTower m
  let : SMul V P :=
    (pureRadicalFractionFieldGenericTensorComponentBaseAlgebra
      (N := e) varpi m).toSMul
  let : Algebra V P :=
    pureRadicalFractionFieldGenericTensorComponentBaseAlgebra
      (N := e) varpi m
  let : IsScalarTower V K P :=
    pureRadicalFractionFieldGenericTensorComponentBase_isScalarTower
      (N := e) varpi m
  obtain ⟨pi, hpi⟩ := target.exists_uniformizer
  obtain ⟨unit, hdecomp⟩ :=
    exists_unit_mul_target_uniformizer_pow_eq_base_uniformizer_image_of_dvf
      base target hvarpi hpi
  let rootP : P :=
    pureRadicalFractionFieldGenericTensorComponentRoot
      (N := e) varpi m
  let j : P →ₐ[L] AlgebraicClosure L :=
    pureRadicalFractionFieldGenericTensorComponentEmbedding
      he varpi hvarpiPrime m
  let beta : AlgebraicClosure L := j rootP
  have hbetaPow : beta ^ e =
      algebraMap K (AlgebraicClosure L) (varpi : K) :=
    fixedTensorComponentEmbeddedRoot_pow
      base he varpi hvarpiPrime m
  obtain ⟨factor⟩ :=
    higherRadicalUnitFactorData
      base target varpi hvarpi pi unit hpi hdecomp
      e (dvd_refl e) beta hbetaPow
  have hbij : Function.Bijective (algebraMap L P) :=
    pureRadicalFractionFieldGenericTensorComponent_rightAlgebraMap_bijective_of_exactUnitFactor
      (K := K) (Froot := Froot) (L := L)
      base target varpi hvarpi pi m factor
  obtain ⟨x, hx⟩ := hbij.2 rootP
  refine ⟨x, ?_⟩
  apply (algebraMap L P).injective
  have hrootP : rootP ^ e = algebraMap V P varpi :=
    pureRadicalFractionFieldGenericTensorComponentRoot_pow
      (K := K) varpi m
  calc
    algebraMap L P (x ^ e) = (algebraMap L P x) ^ e :=
      map_pow (algebraMap L P) x e
    _ = rootP ^ e := by rw [hx]
    _ = algebraMap V P varpi := hrootP
    _ = algebraMap K P (varpi : K) := rfl
    _ = algebraMap L P (algebraMap K L (varpi : K)) :=
      IsScalarTower.algebraMap_apply K L P (varpi : K)

/-- A supplied prefix algebra and one exact final root produce the simultaneous action
of the full `Fin.snoc` root cover on one target field.

Every prefix coordinate is the image of its distinguished root.  This
includes inactive exponent-one stages without a case split.  The final
coordinate is sourced by `exists_targetRoot_of_exactRamificationIndex`, and
domainhood of the full root ring makes the resulting action injective. -/
theorem exists_iteratedRadicalTargetAction_of_prefix_and_exactLastRoot
    {A : Type uA} {K : Type uK} {Froot : Type uF} {L : Type uL}
    [CommRing A] [IsDomain A]
    [Field K] [Field Froot] [Field L]
    [Algebra A K] [Algebra K Froot] [Algebra K L] [Algebra A L]
    [IsScalarTower A K L] [FaithfulSMul A L]
    {r : ℕ} (n : Fin r → ℕ) (a : Fin r → A)
    (hn : ∀ i, 0 < n i)
    [Algebra (iteratedRadical A r n a) L]
    [IsScalarTower A (iteratedRadical A r n a) L]
    (base : DVF.{uK, uV} K) (target : DVF.{uL, uW} L)
    [base.valuation.HasExtension target.valuation]
    [CharZero base.residueField]
    [Module.Finite base.valuationSubring target.valuationSubring]
    (varpi : base.valuationSubring)
    (hvarpi : base.valuation.IsUniformizer (varpi : K))
    (N : ℕ) (hExact : ramificationIndex base target = N)
    (y : A)
    (hy : algebraMap A L y = algebraMap K L (varpi : K))
    [Algebra (AdjoinRoot (X ^ N - C varpi)) Froot]
    [IsFractionRing (AdjoinRoot (X ^ N - C varpi)) Froot]
    [Algebra base.valuationSubring Froot]
    [IsScalarTower base.valuationSubring
      (AdjoinRoot (X ^ N - C varpi)) Froot]
    [IsScalarTower base.valuationSubring K Froot]
    [HenselianLocalRing (AdjoinRoot (X ^ N - C varpi))]
    [IsSepClosed
      (IsLocalRing.ResidueField (AdjoinRoot (X ^ N - C varpi)))]
    [IsDomain
      (iteratedRadical A (r + 1) (Fin.snoc n N) (Fin.snoc a y))] :
    let nFull : Fin (r + 1) → ℕ := Fin.snoc n N
    let aFull : Fin (r + 1) → A := Fin.snoc a y
    ∃ (x : Fin (r + 1) → L)
        (hx : ∀ i, x i ^ nFull i = algebraMap A L (aFull i)),
      Function.Injective
          (iteratedRadicalTargetAlgHom nFull aFull x hx) ∧
        (∀ i : Fin r,
          x i.castSucc =
            algebraMap (iteratedRadical A r n a) L
              (iteratedRadicalRoot A n a i)) := by
  dsimp only
  let nFull : Fin (r + 1) → ℕ := Fin.snoc n N
  let aFull : Fin (r + 1) → A := Fin.snoc a y
  have hN : 0 < N := by
    rw [← hExact]
    exact ramificationIndex_pos_of_moduleFinite base target
  obtain ⟨z, hz⟩ :=
    exists_targetRoot_of_exactRamificationIndex
      (K := K) (Froot := Froot) (L := L)
      base target varpi hvarpi N hExact
  let prefixRoot : Fin r → L := fun i ↦
    algebraMap (iteratedRadical A r n a) L
      (iteratedRadicalRoot A n a i)
  let xFull : Fin (r + 1) → L := Fin.snoc prefixRoot z
  have hnFull : ∀ i, 0 < nFull i := by
    intro i
    refine Fin.lastCases ?_ (fun j ↦ ?_) i
    · simpa [nFull] using hN
    · simpa [nFull] using hn j
  have hxFull : ∀ i,
      xFull i ^ nFull i = algebraMap A L (aFull i) := by
    intro i
    refine Fin.lastCases ?_ (fun j ↦ ?_) i
    · simpa [xFull, nFull, aFull] using hz.trans hy.symm
    · simp only [xFull, nFull, aFull, prefixRoot, Fin.snoc_castSucc]
      rw [← map_pow, iteratedRadicalRoot_pow]
      exact
        (IsScalarTower.algebraMap_apply A
          (iteratedRadical A r n a) L (a j)).symm
  refine ⟨xFull, hxFull, ?_, ?_⟩
  · exact
      iteratedRadicalTargetAlgHom_injective
        nFull aFull hnFull xFull hxFull
  · intro i
    simp [xFull, prefixRoot]

end EtaleFundamentalGroups.Kummer

end
