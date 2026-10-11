/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.Yamaguchi26AbfaithfulGalois.Kummer.Concrete.MixedCharPrimeToCyclotomicDetection
import Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.CyclotomicIntermediateField
import Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.MixedCharCompleteExtension
import Nyll.ProCGroups.FiniteGroups.PrimeOrderHom
import Mathlib.Algebra.Algebra.Tower
import Mathlib.Algebra.CharP.Algebra
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.Perfect

/-!
# Faithful mod-p action outside the dyadic quadratic case

The cyclotomic field and its complete discrete valuation are constructed
from the base field. The logarithmic detection theorem then applies with
no auxiliary field or representation data in the public statement.
-/

namespace ClassFieldTower.Martinet.Shafarevich

open KummerTheory ValuationTheory.DiscreteValuationField

-- Abstracting the closure keeps a single F-algebra on the chosen intermediate
-- field. The only new algebra is the composite F/K/E structure.
private theorem exists_nontrivial_primeDegree_H1Action_in_closure
    {F K Ω : Type*} [Field F] [Field K] [Field Ω]
    [Algebra F K] [Algebra K Ω] [IsAlgClosure K Ω] [IsGalois F K] [CharZero F]
    (vF : _root_.Valuation F (WithZero (Multiplicative ℤ)))
    [Valuation.IsCompleteDiscrete vF]
    (p r : ℕ) [Fact p.Prime] [Fact r.Prime]
    [CharP (IsLocalRing.ResidueField vF.valuationSubring) p]
    (hprime : r ≠ p ∨ p ≠ 2) (hdegree : Module.finrank F K = r) :
    ∃ τ : Gal(K/F), relativeGaloisH1Action (n := p) F K τ ≠ 1 := by
  have : FiniteDimensional F K :=
    FiniteDimensional.of_finrank_pos (hdegree.symm ▸ (Fact.out : r.Prime).pos)
  have : CharZero K := charZero_of_injective_algebraMap (algebraMap F K).injective
  obtain ⟨E, hE⟩ := exists_cyclotomic_intermediateField K Ω p
  have : IsCyclotomicExtension {p} K E := hE
  let : Algebra F E := Algebra.compHom E (algebraMap F K)
  have : IsScalarTower F K E := IsScalarTower.of_algebraMap_eq' rfl
  have : FiniteDimensional K E := IsCyclotomicExtension.finiteDimensional {p} K E
  have : FiniteDimensional F E := FiniteDimensional.trans F K E
  obtain ⟨vE, hcomplete, hext, hres⟩ :=
    ValuedExtension.exists_complete_valuation_of_finite_separable_of_residueChar
      (E := E) vF p
  have : Valuation.IsCompleteDiscrete vE := hcomplete
  have : vF.HasExtension vE := hext
  exact exists_nontrivial_relativeH1Action_of_cyclotomic_tower
    E vF vE p r hprime hdegree (hres := hres)

/-- A prime-degree Galois extension of a complete discretely valued field
of mixed characteristic has faithful mod-p action outside the dyadic
quadratic case. No finite generation or residue-field finiteness
assumption is required. -/
theorem faithful_relativeH1Action_of_complete_mixedChar_prime_degree
    {F K : Type*} [Field F] [Field K] [Algebra F K] [IsGalois F K] [CharZero F]
    (vF : _root_.Valuation F (WithZero (Multiplicative ℤ)))
    [Valuation.IsCompleteDiscrete vF]
    (p r : ℕ) [Fact p.Prime] [Fact r.Prime]
    [CharP (IsLocalRing.ResidueField vF.valuationSubring) p]
    (hprime : r ≠ p ∨ p ≠ 2) (hdegree : Module.finrank F K = r) :
    Function.Injective (relativeGaloisH1Action (n := p) F K) := by
  have : FiniteDimensional F K :=
    FiniteDimensional.of_finrank_pos (hdegree.symm ▸ (Fact.out : r.Prime).pos)
  obtain ⟨τ, hτ⟩ := exists_nontrivial_primeDegree_H1Action_in_closure
    (Ω := AlgebraicClosure K) vF p r hprime hdegree
  have hcard : Nat.card Gal(K/F) = r :=
    (IsGalois.card_aut_eq_finrank F K).trans hdegree
  apply (ProCGroups.FiniteStepSolvableQuotients.injective_iff_ne_one_of_prime_card
    (relativeGaloisH1Action (n := p) F K) (hcard.symm ▸ (Fact.out : r.Prime))).mpr
  intro h
  exact hτ (DFunLike.congr_fun h τ)

/-- The original prime-to-p-degree theorem is a specialization. -/
theorem faithful_relativeH1Action_of_complete_mixedChar_primeTo_degree
    {F K : Type*} [Field F] [Field K] [Algebra F K] [IsGalois F K] [CharZero F]
    (vF : _root_.Valuation F (WithZero (Multiplicative ℤ)))
    [Valuation.IsCompleteDiscrete vF]
    (p r : ℕ) [Fact p.Prime] [Fact r.Prime]
    [CharP (IsLocalRing.ResidueField vF.valuationSubring) p]
    (hrp : r ≠ p) (hdegree : Module.finrank F K = r) :
    Function.Injective (relativeGaloisH1Action (n := p) F K) := by
  exact faithful_relativeH1Action_of_complete_mixedChar_prime_degree
    vF p r (Or.inl hrp) hdegree

end ClassFieldTower.Martinet.Shafarevich
