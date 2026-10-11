/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.Yamaguchi26AbfaithfulGalois.Kummer.Concrete.MixedCharCyclotomicDetection
import Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.CyclotomicIntermediateField
import Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.MixedCharCompleteExtension
import Nyll.ProCGroups.FiniteGroups.PrimeOrderHom
import Mathlib.Algebra.Algebra.Tower
import Mathlib.Algebra.CharP.Algebra
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.Perfect
import Mathlib.NumberTheory.Cyclotomic.Basic

/-!
# Faithful prime-power H¹ action over a complete mixed-characteristic base

Both cyclotomic fields are constructed in an actual algebraic closure.
A complete integer-valued extension valuation and its residue characteristic
are generated from the base. The two-branch detection then gives a nontrivial
action, which is faithful because the original Galois group has prime order.
-/

namespace ClassFieldTower.Martinet.Shafarevich

open KummerTheory ValuationTheory.DiscreteValuationField

-- The only new data instances are the single composite F-algebra on E and
-- its F/K/E tower. Constructing L inside E reuses canonical intermediate-field
-- instances; no F-algebra on the ambient closure is installed. The peak is
-- fifteen field/algebra/tower structures. Residue-field transport stays in
-- the separate two-field valuation source.
-- Keep the field construction abstract in Ω. On the concrete AlgebraicClosure K,
-- its lower-base algebra instance would introduce a second F-module on E.
private theorem exists_nontrivial_H1Action_in_closure
    {F K Ω : Type*} [Field F] [Field K] [Field Ω]
    [Algebra F K] [Algebra K Ω] [IsAlgClosure K Ω] [Normal F K] [CharZero F]
    (vF : _root_.Valuation F (WithZero (Multiplicative ℤ)))
    [Valuation.IsCompleteDiscrete vF] (p : ℕ) [Fact p.Prime]
    [CharP (IsLocalRing.ResidueField vF.valuationSubring) p]
    (hdegree : Module.finrank F K = p) :
    ∃ s : ℕ, 1 ≤ s ∧ ∃ τ : Gal(K/F),
      relativeGaloisH1Action (n := p ^ s) F K τ ≠ 1 := by
  have hp : p.Prime := Fact.out
  have : FiniteDimensional F K :=
    FiniteDimensional.of_finrank_pos (hdegree.symm ▸ hp.pos)
  have : CharZero K := charZero_of_injective_algebraMap (algebraMap F K).injective
  obtain ⟨E, hE⟩ := exists_cyclotomic_intermediateField K Ω p
  have : IsCyclotomicExtension {p} K E := hE
  let : Algebra F E := Algebra.compHom E (algebraMap F K)
  have : IsScalarTower F K E := IsScalarTower.of_algebraMap_eq' rfl
  have : FiniteDimensional K E := IsCyclotomicExtension.finiteDimensional {p} K E
  have : FiniteDimensional F E := FiniteDimensional.trans F K E
  have hextension : ∃ vE : _root_.Valuation E (WithZero (Multiplicative ℤ)),
      Valuation.IsCompleteDiscrete vE ∧ vF.HasExtension vE ∧
        CharP (IsLocalRing.ResidueField vE.valuationSubring) p :=
    ValuedExtension.exists_complete_valuation_of_finite_separable_of_residueChar vF p
  obtain ⟨vE, hcomplete, hext, hres⟩ := hextension
  have : Valuation.IsCompleteDiscrete vE := hcomplete
  have : vF.HasExtension vE := hext
  obtain ⟨ζ, hζ⟩ := IsCyclotomicExtension.exists_isPrimitiveRoot K E
    (Set.mem_singleton p) hp.ne_zero
  let L : IntermediateField F E := IntermediateField.adjoin F {ζ}
  have : IsCyclotomicExtension {p} F L :=
    hζ.intermediateField_adjoin_isCyclotomicExtension F
  exact exists_nontrivial_relativeH1Action_of_prime_degree_cyclotomic_tower
    (L := L) E vF vE p hdegree (hres := hres)

/-- A prime-degree Galois extension of a complete discretely valued field of
mixed characteristic has faithful H¹ action at some positive p-power level.
No auxiliary field, extension valuation, root bound or action comparison is
an input to this theorem. -/
theorem exists_faithful_relativeH1Action_of_complete_mixedChar_prime_degree
    {F K : Type*} [Field F] [Field K] [Algebra F K] [IsGalois F K] [CharZero F]
    (vF : _root_.Valuation F (WithZero (Multiplicative ℤ)))
    [Valuation.IsCompleteDiscrete vF]
    (p : ℕ) [Fact p.Prime]
    [CharP (IsLocalRing.ResidueField vF.valuationSubring) p]
    (hdegree : Module.finrank F K = p) :
    ∃ s : ℕ, 1 ≤ s ∧ Function.Injective (relativeGaloisH1Action (n := p ^ s) F K) := by
  have hp : p.Prime := Fact.out
  have : FiniteDimensional F K :=
    FiniteDimensional.of_finrank_pos (hdegree.symm ▸ hp.pos)
  obtain ⟨s, hs, τ, hτ⟩ :=
    exists_nontrivial_H1Action_in_closure (Ω := AlgebraicClosure K) vF p hdegree
  have hcard : Nat.card Gal(K/F) = p :=
    (IsGalois.card_aut_eq_finrank F K).trans hdegree
  refine ⟨s, hs, (ProCGroups.FiniteStepSolvableQuotients.injective_iff_ne_one_of_prime_card
    (relativeGaloisH1Action (n := p ^ s) F K) (hcard.symm ▸ hp)).mpr ?_⟩
  intro h
  exact hτ (DFunLike.congr_fun h τ)

end ClassFieldTower.Martinet.Shafarevich
