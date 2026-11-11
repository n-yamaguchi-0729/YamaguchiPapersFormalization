/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.Yamaguchi26AbfaithfulGalois.Kummer.Concrete.MixedCharAllPrimeCompleteDetection
public import Nyll.Yamaguchi26AbfaithfulGalois.Kummer.RelativeAbelianModPowerAction
public import Nyll.GaloisCohomology.Kummer.Concrete.AbsoluteH1Action
public import Nyll.GaloisCohomology.Kummer.Concrete.FixedSubgroupCharacterDescent
public import Nyll.GaloisCohomology.Kummer.Concrete.FixedSubgroupAbsoluteAction
public import Nyll.GaloisCohomology.Kummer.Concrete.FixedSubgroupTopology
public import Nyll.GaloisCohomology.Kummer.Concrete.GaloisClosureConjugation
public import Nyll.GaloisCohomology.Kummer.Concrete.FixedSubgroupConjugation
public import Nyll.GaloisCohomology.Kummer.Concrete.GaloisClosureCharacterConjugation
public import Nyll.GaloisCohomology.ProP.ResidualCharacterDetection
public import Nyll.ProCGroups.ProP.ContinuousH1
public import Nyll.ProCGroups.ProC.MaximalQuotients.ConjugationComparison
public import Nyll.ProCGroups.Abelian.TopologicalAbelianization
public import Nyll.ProCGroups.FiniteGroups.PGroupFormation
public import Mathlib.FieldTheory.Galois.Infinite
public import Mathlib.FieldTheory.Perfect
public import Mathlib.Topology.Instances.ZMod

/-!
# Complete mixed-characteristic detection on actual fixing subgroups

Faithful H¹ supplies a changed finite p-power character. The actual closure
comparison moves that character to the fixing subgroup, and its factorization
through the pro-p residual quotient detects the same ambient conjugation.
-/

@[expose] public section

namespace ClassFieldTower.Martinet.Shafarevich

open KummerTheory ClassFieldTower.ProP
open ProCGroups ProCGroups.ProC ProCGroups.Abelian

attribute [local instance] KummerTheory.fixingSubgroup_normal KummerTheory.closureOverIntermediate

-- The only new local instance is finite dimensionality, derived from the degree.
-- Normality and closure-over-intermediate are the existing canonical instances.
/-- An ambient automorphism outside a prime-degree fixing subgroup acts
nontrivially on the abelianization of that subgroup's actual pro-p residual
quotient over a complete mixed-characteristic discretely valued base. -/
theorem mixedChar_fixingSubgroup_residualAbelianization_conjugation_ne_one
    {F Ω : Type*} [Field F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] [CharZero F]
    (S : IntermediateField F Ω) [IsGalois F S]
    (vF : _root_.Valuation F (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete vF]
    (p : ℕ) [Fact p.Prime]
    [CharP (IsLocalRing.ResidueField vF.valuationSubring) p]
    {r : ℕ} [Fact r.Prime] (hdegree : Module.finrank F S = r)
    (g : Gal(Ω/F)) (hg : g ∉ S.fixingSubgroup) :
    (TopologicalAbelianization.congr
      (residualQuotientConjugationContinuousMulEquiv
        (FiniteGroupClass.pGroup_fullFormation p) S.fixingSubgroup
        (InfiniteGalois.fixingSubgroup_isClosed S) g)).toMulEquiv ≠ 1 := by
  classical
  have : FiniteDimensional F S :=
    FiniteDimensional.of_finrank_pos (hdegree.symm ▸ (Fact.out : r.Prime).pos)
  obtain ⟨s, _hs, hfaith⟩ :=
    exists_faithful_relativeH1Action_of_complete_mixedChar_prime_order vF p hdegree
  let τ : Gal(S/F) := g.restrictNormal S
  have hτ : τ ≠ 1 := by
    intro heq
    apply hg
    rw [← S.restrictNormalHom_ker]
    exact heq
  have hτinv : relativeGaloisH1Action (n := p ^ s) F S τ⁻¹ ≠ 1 := by
    intro heq
    exact (inv_ne_one.mpr hτ)
      (hfaith (heq.trans (map_one (relativeGaloisH1Action (n := p ^ s) F S)).symm))
  obtain ⟨f, σ₀, hvalue⟩ :=
    exists_changed_character_of_inverse_relativeH1Action_ne_one (p ^ s) τ hτinv
  let e : S.fixingSubgroup ≃ₜ* Gal(AlgebraicClosure S/S) :=
    (fixingSubgroupContinuousEquiv S).trans (absoluteGaloisClosureEquiv S Ω)
  let χ : S.fixingSubgroup →ₜ* Multiplicative (ZMod (p ^ s)) :=
    fixingSubgroupAbsoluteCharacter S f
  let x : S.fixingSubgroup := e.symm σ₀
  have hconj : χ (MulAut.conjNormal g x) = f (absoluteGaloisConjugate τ.toRingEquiv σ₀) := by
    change f (absoluteGaloisClosureEquiv S Ω
      (S.fixingSubgroupEquiv (MulAut.conjNormal g x))) =
        f (absoluteGaloisConjugate τ.toRingEquiv σ₀)
    rw [fixingSubgroupEquiv_conjNormal,
      absoluteGaloisClosureEquiv_character_conjugation]
    change f (absoluteGaloisConjugate τ.toRingEquiv (e (e.symm σ₀))) =
      f (absoluteGaloisConjugate τ.toRingEquiv σ₀)
    rw [ContinuousMulEquiv.apply_symm_apply]
  have hx : χ x = f σ₀ := by
    change f (e (e.symm σ₀)) = f σ₀
    rw [ContinuousMulEquiv.apply_symm_apply]
  have hχ : χ (MulAut.conjNormal g x) ≠ χ x := by
    rw [hconj, hx]
    exact hvalue
  exact residualAbelianization_conjugation_ne_one_of_cyclicCharacter_ne
    p s S.fixingSubgroup (InfiniteGalois.fixingSubgroup_isClosed S) g χ x hχ

end ClassFieldTower.Martinet.Shafarevich
