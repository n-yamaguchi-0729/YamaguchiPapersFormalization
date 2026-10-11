/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Nyll.AlgebraicCurves.Valuations.FinitelyGeneratedMixedCharacteristic
import Nyll.Yamaguchi26AbfaithfulGalois.Theorem3Dot6MixedCharacteristic
import Nyll.Yamaguchi26AbfaithfulGalois.GroupTheory.SigmaOrdinary

/-!
# The characteristic-zero case of the earlier finitely generated field example

The mixed-characteristic valuation is constructed from finite generation.
-/

namespace Yamaguchi26AbfaithfulGalois

open ProCGroups.FiniteStepSolvableQuotients

universe u

/-- Finitely generated characteristic-zero fields are ab-faithful, by applying
Theorem 3.6 to a discrete valuation constructed from an affine integer model. -/
theorem finitelyGenerated_charZero_isAbFaithful
    (K : Type u) [Field K] [CharZero K] (hfg : Field.FG K) :
    IsAbFaithful Gal(AlgebraicClosure K/K) := by
  obtain ⟨p, hp, D, hD⟩ := FieldTheory.exists_mixedChar_DVF_of_fg K hfg
  have : Fact p.Prime := ⟨hp⟩
  have : CharP D.residueField p := hD
  exact IsSigmaAbFaithful.isAbFaithful
    (G := Gal(AlgebraicClosure K/K)) (sigma := {p})
    (mixed_characteristic_properties_3_6 K D p).2

end Yamaguchi26AbfaithfulGalois
