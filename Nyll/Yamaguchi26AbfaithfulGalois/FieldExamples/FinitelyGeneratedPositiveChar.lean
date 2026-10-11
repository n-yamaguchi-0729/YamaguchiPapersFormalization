/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/


import Nyll.Yamaguchi26AbfaithfulGalois.Kummer.FinitelyGeneratedPositiveCharacteristicDetection
import Nyll.Yamaguchi26AbfaithfulGalois.Kummer.PositiveCharacteristicPrimeDegreeReduction
import Nyll.Yamaguchi26AbfaithfulGalois.GroupTheory.SigmaOrdinary

/-!
# Positive-characteristic finitely generated fields are ab-faithful

Finite Galois automorphisms move discrete valuations, so local Artin--Schreier
characters detect the action on abelianization modulo the characteristic.
-/

namespace Yamaguchi26AbfaithfulGalois
open ProCGroups.FiniteStepSolvableQuotients
universe u

/-- An infinite finitely generated field of characteristic `p` is
`{p}`-ab-faithful, without any perfection hypothesis. -/
theorem finitelyGenerated_posChar_isSigmaAbFaithful
    (K : Type u) [Field K] [Infinite K] (p : ℕ) [Fact p.Prime] [CharP K p]
    (hfg : Field.FG K) : IsSigmaAbFaithful {p} Gal(AlgebraicClosure K/K) := by
  apply isSigmaAbFaithful_of_primeDegree_detection_fg_charP p ?_ hfg
  intro F E _ _ _ _ _ _ hF r _ hr
  exact prime_order_detection_of_fg_posChar p r hF hr

/-- The positive-characteristic ab-faithfulness assertion needed in Example
5.9(2), proved through discrete valuations and weak approximation. -/
theorem finitelyGenerated_posChar_isAbFaithful
    (K : Type u) [Field K] [Infinite K] (hfg : Field.FG K)
    (hchar : ringChar K ≠ 0) : IsAbFaithful Gal(AlgebraicClosure K/K) := by
  have : Fact (ringChar K).Prime :=
    ⟨(CharP.char_is_prime_or_zero K (ringChar K)).resolve_right hchar⟩
  exact IsSigmaAbFaithful.isAbFaithful
    (G := Gal(AlgebraicClosure K/K)) (sigma := {ringChar K})
    (finitelyGenerated_posChar_isSigmaAbFaithful K (ringChar K) hfg)
end Yamaguchi26AbfaithfulGalois
