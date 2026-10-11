/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import GaloisCohomology.Kummer.Concrete.AbsoluteH1Action
import ProCGroups.Abelian.AbelianModPower
import ValuedFieldTheory.Valuation.DiscreteValuationField.Basic
import Yamaguchi26AbfaithfulGalois.GroupTheory.SigmaFaithful
import Mathlib.FieldTheory.AbsoluteGaloisGroup
import Mathlib.FieldTheory.Galois.Profinite
import Yamaguchi26AbfaithfulGalois.Kummer.RelativeAbelianModPowerAction

import Yamaguchi26AbfaithfulGalois.Kummer.MixedCharacteristicPrimeDetection
import Yamaguchi26AbfaithfulGalois.Kummer.PrimeDegreeReduction
import Yamaguchi26AbfaithfulGalois.Kummer.FiniteGaloisPrimeDegreeReduction

/-!
# Mixed-characteristic discrete valuations

Theorem 3.6 (`thm:mixed-characteristic`) from Section 3 of
`AbfatifhulGalois.tex`. Its first assertion is stated on the actual
quotient `G_Lᵃᵇ/p`.
-/

namespace Yamaguchi26AbfaithfulGalois

open KummerTheory ValuationTheory.DiscreteValuationField ProCGroups.Abelian
open ProCGroups.FiniteStepSolvableQuotients

universe u v

/-- For each finite Galois extension of a mixed-characteristic discretely
valued field, the conjugation action on the mod-`p` abelianization is
faithful. Consequently its absolute Galois group is `p`-ab-faithful. -/
theorem mixed_characteristic_properties_3_6
    (K : Type u) [Field K] [CharZero K]
    (base : DVF.{u, v} K) (p : ℕ) [Fact p.Prime]
    [CharP base.residueField p] :
    (∀ (L : Type u) [Field L] [Algebra K L]
      [FiniteDimensional K L] [IsGalois K L],
      ∀ τ : Gal(L/K),
        (∀ z : abelianModPower Gal(AlgebraicClosure L/L) p,
          relativeGaloisAbelianModPowerTransform K L p τ z = z) → τ = 1) ∧
      IsSigmaAbFaithful {p} Gal(AlgebraicClosure K/K) := by
  have hdetect : ∀ (F E : Type u) [Field F] [Field E] [Algebra F E]
      [IsGalois F E] [CharZero F]
      (source : DVF.{u,v} F) [CharP source.residueField p]
      (r : ℕ) [Fact r.Prime], Module.finrank F E = r →
        ∃ τ : Gal(E/F), τ ≠ 1 ∧
          ∃ z : abelianModPower Gal(AlgebraicClosure E/E) p,
            relativeGaloisAbelianModPowerTransform F E p τ z ≠ z := by
    intro F E _ _ _ _ _ source _ r _ hdegree
    exact prime_order_detection_of_mixedChar source p r hdegree
  constructor
  · intro L _ _ _ _
    exact relativeGaloisAbelianModPowerTransform_faithful_of_primeDegree_detection
      p hdetect base L
  · exact isSigmaAbFaithful_of_primeDegree_detection p hdetect base

end Yamaguchi26AbfaithfulGalois
