/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.GaloisCohomology.Kummer.Concrete.DescendedCharacterAction
import Nyll.GaloisCohomology.Kummer.Concrete.AbsoluteContinuousCharacterAction
import Nyll.Yamaguchi26AbfaithfulGalois.Kummer.Concrete.MixedCharInvariantKummerTrace
import Nyll.Yamaguchi26AbfaithfulGalois.Kummer.Concrete.MixedCharMovingRootDetection
import Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.CyclotomicGaloisCard
import Nyll.ValuedFieldTheory.LocalField.Analytic.LogExpSeries.InverseEstimates
import Mathlib.Algebra.CharP.IntermediateField
import Mathlib.Algebra.Group.End
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Instances.ZMod

/-!
# Nontrivial H¹ action from both cyclotomic branches

The positive branch descends the actual invariant Kummer trace. Triviality
of the lower action would fix that same trace, contradicting its construction.
The other branch uses the logarithmic minimum argument. The common last
root level and the branch split are generated internally.
-/

namespace ClassFieldTower.Martinet.Shafarevich

open KummerTheory
open LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation

-- This helper separates character descent from the two-cyclotomic-field setup.
-- Reversing the action uses its proved group law, not a comparison of chosen lifts.

private theorem characterAction_fixed_of_trivial_lowerH1Action
    {F K Ω : Type*} [Field F] [Field K] [Field Ω]
    [Algebra F K] [Algebra K Ω] [IsAlgClosure K Ω] [CharZero K]
    (E : IntermediateField K Ω) [FiniteDimensional K E] [Normal K E]
    (n : ℕ) (hdegree : (Module.finrank K E).Coprime n)
    (f : Gal(AlgebraicClosure E/E) →ₜ* Multiplicative (ZMod n))
    (hinv : ∀ δ : Gal(E/K), absoluteContinuousCharacterAction (K := E)
      (A := Multiplicative (ZMod n)) δ.toRingEquiv f = f)
    (τ : Gal(K/F)) (υ : E ≃+* E)
    (hυ : ∀ x : K, υ (algebraMap K E x) = algebraMap K E (τ x))
    (hτ : relativeGaloisH1Action (n := n) F K τ = 1) :
    absoluteContinuousCharacterAction (K := E)
      (A := Multiplicative (ZMod n)) υ f = f := by
  have hforward : ∀ (δ : Gal(E/K)) (σ : Gal(AlgebraicClosure E/E)),
      f (absoluteGaloisConjugate δ.toRingEquiv σ) = f σ := by
    intro δ σ
    have h := DFunLike.congr_fun (hinv δ.symm) σ
    change f (absoluteGaloisConjugate δ.toRingEquiv σ) = f σ at h
    exact h
  let a : RingAut E →* MulAut (Gal(AlgebraicClosure E/E) →ₜ* Multiplicative (ZMod n)) :=
    absoluteContinuousCharacterAction (K := E) (A := Multiplicative (ZMod n))
  have hback : a υ⁻¹ f = f := by
    apply ContinuousMonoidHom.ext
    intro σ
    change f (absoluteGaloisConjugate υ σ) = f σ
    exact absoluteCharacter_invariant_of_trivial_lowerH1Action
      E n hdegree f hforward τ υ hυ hτ σ
  rw [map_inv] at hback
  have h := congrArg (a υ) hback
  rw [MulAut.apply_inv_self] at h
  exact h.symm

-- Conservatively, five fields, six algebras and two towers give thirteen
-- supplied data structures. The proof adds only three distinct propositions:
-- finite dimensionality over F and K, and Galoisness over K.
/-- For the actual prime-degree normal extension, cyclotomic fields and
complete extension valuation, some positive p-power H¹ action is nontrivial.
The last root level and both sides of the roots-downstairs split are internal. -/
theorem exists_nontrivial_relativeH1Action_of_prime_degree_cyclotomic_tower
    {F K L Ω : Type*} [Field F] [Field K] [Field L] [Field Ω]
    [Algebra F K] [Algebra K Ω] [IsAlgClosure K Ω] [CharZero K]
    (E : IntermediateField K Ω)
    [Algebra F L] [Algebra F E] [Algebra L E]
    [IsScalarTower F K E] [IsScalarTower F L E] [Normal F K]
    (vF : _root_.Valuation F (WithZero (Multiplicative ℤ)))
    (vE : _root_.Valuation E (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete vF]
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete vE]
    [vF.HasExtension vE]
    (p : ℕ) [Fact p.Prime]
    [hres : CharP (IsLocalRing.ResidueField vE.valuationSubring) p]
    [IsCyclotomicExtension {p} F L] [IsCyclotomicExtension {p} K E]
    (hdegree : Module.finrank F K = p) :
    ∃ s : ℕ, 1 ≤ s ∧ ∃ τ : Gal(K/F),
      relativeGaloisH1Action (n := p ^ s) F K τ ≠ 1 := by
  have hp : p.Prime := Fact.out
  have : FiniteDimensional F K :=
    FiniteDimensional.of_finrank_pos (hdegree.symm ▸ hp.pos)
  have : FiniteDimensional K E := IsCyclotomicExtension.finiteDimensional {p} K E
  have : IsGalois K E := IsCyclotomicExtension.isGalois {p} K E
  obtain ⟨s, hmu, _hmax, _hnext, hpositive⟩ :=
    exists_lastLevel_invariant_moved_cyclotomicKummerTrace F K L E p hdegree
      (completeDVFOfWithZeroValuation vE).toDVF
      (hres := by change CharP (IsLocalRing.ResidueField vE.valuationSubring) p; exact hres)
  refine ⟨s + 1, Nat.succ_le_succ (Nat.zero_le s), ?_⟩
  by_cases hdown : ∀ ξ : E, ξ ^ (p ^ (s + 1)) = 1 → ξ ∈ Set.range (algebraMap L E)
  · obtain ⟨τ, T, hT, hmoved⟩ := hpositive hdown
    let τlower : Gal(K/F) := IntermediateField.restrictRestrictAlgEquivMapHom F K L E τ
    refine ⟨τlower, ?_⟩
    intro htrivial
    apply hmoved
    have hcop : (Module.finrank K E).Coprime p := by
      have hcard :=
        ValuationTheory.DiscreteValuationField.prime_coprime_cyclotomicGalois_natCard K E p
      rw [IsGalois.card_aut_eq_finrank K E] at hcard
      exact hcard.symm
    exact characterAction_fixed_of_trivial_lowerH1Action
      E (p ^ (s + 1)) (hcop.pow_right (s + 1)) T hT τlower τ.toRingEquiv
      (restrictRestrictAlgEquivMapHom_algebraMap F K L E τ) htrivial
  · exact exists_nontrivial_relativeH1Action_of_roots_not_in_cyclotomic_base
      E vF vE p s hmu hdown

end ClassFieldTower.Martinet.Shafarevich
