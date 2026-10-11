/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.Yamaguchi26AbfaithfulGalois.Kummer.Concrete.MixedCharCyclotomicRootFixing
import Nyll.GaloisCohomology.Kummer.Concrete.MovingRootOfUnity
import Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.NormalCyclotomicTower
import Mathlib.Algebra.Ring.CharZero
import Mathlib.FieldTheory.Perfect
import Mathlib.RingTheory.Finiteness.Basic

/-!
# Detection when a prime-power root does not descend

The upper extension is Galois by its actual splitting-field construction.
A root outside the lower cyclotomic field is moved by a Galois automorphism.
Its restriction cannot act trivially on H¹, since the logarithmic minimum
argument would then fix that same root.
-/

namespace ClassFieldTower.Martinet.Shafarevich

open KummerTheory

-- The supplied data are the same thirteen structures as in RootFixing.
-- The proof adds only finite-dimensionality, normality, characteristic, and
-- Galois propositions. In particular it introduces no alternate algebra tower.
/-- If the selected prime-power roots do not all descend to the lower
cyclotomic field, the actual lower H¹ action is nontrivial. -/
theorem exists_nontrivial_relativeH1Action_of_roots_not_in_cyclotomic_base
    {F K L Ω : Type*} [Field F] [Field K] [Field L] [Field Ω]
    [Algebra F K] [Algebra K Ω] [IsAlgClosure K Ω] [CharZero K]
    (E : IntermediateField K Ω)
    [Algebra F L] [Algebra F E] [Algebra L E]
    [IsScalarTower F K E] [IsScalarTower F L E]
    [FiniteDimensional F K] [Normal F K]
    (vF : _root_.Valuation F (WithZero (Multiplicative ℤ)))
    (vE : _root_.Valuation E (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete vF]
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete vE]
    [vF.HasExtension vE]
    (p : ℕ) [Fact p.Prime] [CharP (IsLocalRing.ResidueField vE.valuationSubring) p]
    [IsCyclotomicExtension {p} F L] [IsCyclotomicExtension {p} K E]
    (s : ℕ) (hmu : (primitiveRoots (p ^ (s + 1)) E).Nonempty)
    (hnot : ¬ ∀ ζ : E, ζ ^ (p ^ (s + 1)) = 1 →
      ζ ∈ Set.range (algebraMap L E)) :
    ∃ τ : Gal(K/F), relativeGaloisH1Action (n := p ^ (s + 1)) F K τ ≠ 1 := by
  have : FiniteDimensional K E := IsCyclotomicExtension.finiteDimensional {p} K E
  have : FiniteDimensional F E := FiniteDimensional.trans F K E
  have : FiniteDimensional L E := Module.Finite.of_restrictScalars_finite F L E
  have : Normal F E := ValuationTheory.DiscreteValuationField.normal_cyclotomic_tower F K E p
  have : CharZero L := (algebraMap L E).charZero
  have : IsGalois L E :=
    { to_normal := Normal.tower_top_of_normal F L E
      to_isSeparable := inferInstance }
  let m : ℕ+ := ⟨p ^ (s + 1), pow_pos (Fact.out : p.Prime).pos (s + 1)⟩
  obtain ⟨ζ, τupper, hζ, hmoved⟩ :=
    exists_moving_primitiveRoot_of_not_all_roots_in_base L E m hmu hnot
  refine ⟨IntermediateField.restrictRestrictAlgEquivMapHom F K L E τupper, ?_⟩
  intro htrivial
  exact hmoved (trivial_relativeH1Action_fixes_primePower_roots
    E vF vE p s hmu τupper htrivial ζ hζ.pow_eq_one)

end ClassFieldTower.Martinet.Shafarevich
