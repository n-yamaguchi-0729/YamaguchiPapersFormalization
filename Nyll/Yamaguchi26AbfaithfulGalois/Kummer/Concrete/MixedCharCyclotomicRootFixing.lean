/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.Yamaguchi26AbfaithfulGalois.Kummer.Concrete.MixedCharCyclotomicPowerWitness
import Nyll.GaloisCohomology.Kummer.Concrete.SemilinearRestriction
import Nyll.Yamaguchi26AbfaithfulGalois.Analytic.MixedCharCyclotomicEigenUnit
import Nyll.Yamaguchi26AbfaithfulGalois.Analytic.MixedCharPrincipalUnitPowerWitnessDecrease
import Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.HenselianAutomorphismValuation
import Mathlib.Algebra.CharP.IntermediateField

/-!
# Trivial cohomological action fixes prime-power roots

The minimal logarithmic eigenvector and its eigenunit are generated from
the two cyclotomic extensions. A trivial lower H¹ action produces an actual
power witness. If its bounded exponent differs from one, its logarithm is
another eigenvector of strictly smaller valuation, contradicting that minimum.
-/

namespace ClassFieldTower.Martinet.Shafarevich

open KummerTheory LocalFieldTheory.DiscreteValuationField
open LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation

-- Six Algebra structures (including the canonical K-algebra E), two towers,
-- and five fields give thirteen data structures. The proof adds only two
-- finite-dimensionality propositions and ordinary bundled valuation data.
/-- An upper automorphism fixing the lower cyclotomic field fixes every
root at the selected prime-power level if its restriction acts trivially
on the lower H¹. The logarithmic minimum is constructed inside the proof. -/
theorem trivial_relativeH1Action_fixes_primePower_roots
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
    (τupper : Gal(E/L))
    (hτ : relativeGaloisH1Action (n := p ^ (s + 1)) F K
      (IntermediateField.restrictRestrictAlgEquivMapHom F K L E τupper) = 1) :
    ∀ ζ : E, ζ ^ (p ^ (s + 1)) = 1 → τupper ζ = ζ := by
  have : FiniteDimensional K E := IsCyclotomicExtension.finiteDimensional {p} K E
  have : FiniteDimensional F E := FiniteDimensional.trans F K E
  obtain ⟨b, u, hbeigen, hlog, hueigen, hminimal⟩ :=
    exists_minimal_cyclotomic_log_eigenunit (K := L) (L := K) vF vE p
  obtain ⟨a, ha, hroots, y, hy⟩ :=
    exists_cyclotomic_power_witness_of_trivial_lowerH1Action
      E vE p s hmu u hueigen
      (IntermediateField.restrictRestrictAlgEquivMapHom F K L E τupper)
      τupper.toRingEquiv
      (restrictRestrictAlgEquivMapHom_algebraMap F K L E τupper) hτ
  have hval (x : E) : vE (τupper x) = vE x := by
    let base : ValuationTheory.DiscreteValuationField.CompleteDVF F :=
      { ValueGroup := WithZero (Multiplicative ℤ), valuation := vF }
    let target : ValuationTheory.DiscreteValuationField.DVF E :=
      { ValueGroup := WithZero (Multiplicative ℤ), valuation := vE }
    exact base.toHenselianDVF.valuation_algEquiv_eq target (τupper.restrictScalars F) x
  have haone : a = 1 := by
    by_contra haone
    obtain ⟨c, z, hceigen, hclog, hstrict⟩ :=
      exists_smaller_characterEigenvector_log_of_power_witness vE p τupper hval
        b u hlog
        (fun γ : L ≃ₐ[F] L => padicIntToFieldOfMixedChar vE p
          (primeCyclotomicTeichmullerCharacter F L p γ : ℤ_[p]))
        hbeigen a s ha haone y hy
    exact (not_lt_of_ge (hminimal c hceigen ⟨z, hclog⟩)) hstrict
  intro ζ hζ
  change τupper.toRingEquiv ζ = ζ
  rw [hroots ζ hζ, haone, pow_one]

end ClassFieldTower.Martinet.Shafarevich
