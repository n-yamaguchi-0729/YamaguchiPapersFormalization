/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.Yamaguchi26AbfaithfulGalois.FieldExamples.FinitelyGeneratedCharZero
import Nyll.Yamaguchi26AbfaithfulGalois.FieldExamples.FinitelyGeneratedPositiveChar
import Mathlib.Algebra.CharP.Basic
import Mathlib.FieldTheory.Galois.Profinite

/-! # Ab-faithfulness of infinite finitely generated fields -/

namespace Yamaguchi26AbfaithfulGalois
open ProCGroups.FiniteStepSolvableQuotients
universe u

/-- Every infinite finitely generated field is ab-faithful. The positive-
characteristic case uses moving discrete valuations and local characters. -/
theorem finitelyGenerated_isAbFaithful
    (K : Type u) [Field K] [Infinite K] (hfg : Field.FG K) :
    IsAbFaithful Gal(AlgebraicClosure K/K) := by
  by_cases hchar : ringChar K = 0
  · have : CharP K 0 := hchar ▸ (inferInstance : CharP K (ringChar K))
    have : CharZero K := CharP.charP_to_charZero K
    exact finitelyGenerated_charZero_isAbFaithful K hfg
  · exact finitelyGenerated_posChar_isAbFaithful K hfg hchar

end Yamaguchi26AbfaithfulGalois
