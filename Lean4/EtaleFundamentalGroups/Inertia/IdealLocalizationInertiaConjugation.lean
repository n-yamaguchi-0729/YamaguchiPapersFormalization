/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Inertia.FiniteIdealTameCharacter
import EtaleFundamentalGroups.Inertia.NativeIdealInertiaConjugate
import ValuedFieldTheory.Ramification.HilbertRamification.RingInertiaCharacterConjugation

/-!
# Conjugation through inertia localization

Proves that the ideal-to-local inertia comparison preserves the conjugate induced by an element
of the original stabilizer.
-/

noncomputable section

namespace EtaleFundamentalGroups.Inertia

open RamificationTheory.HilbertRamification.DiscreteValuationRing
open scoped Pointwise

universe u v

/-- The actual localization-inertia comparison retains the literal conjugate
in the original stabilizer. No conjugation compatibility is assumed. -/
theorem idealLocalizationInertiaGroupMap_conjugate_value
    (B G : Type v) [CommRing B] [Group G] [MulSemiringAction G B]
    (Q : Ideal B) [Q.IsPrime]
    (d : MulAction.stabilizer G Q) (σ : Q.inertia G) :
    (idealLocalizationInertiaGroupMap B G Q).toFun
        (nativeIdealInertiaConjugate B G Q d σ) =
      ⟨d * ((idealLocalizationInertiaGroupMap B G Q).toFun σ).val * d⁻¹,
        (maximalIdeal_inertia_normal (Localization.AtPrime Q)
          (MulAction.stabilizer G Q)).conj_mem
          ((idealLocalizationInertiaGroupMap B G Q).toFun σ).val
          ((idealLocalizationInertiaGroupMap B G Q).toFun σ).property d⟩ := by
  apply Subtype.ext
  apply Subtype.ext
  exact nativeIdealInertiaConjugate_value B G Q d σ


end EtaleFundamentalGroups.Inertia

end
