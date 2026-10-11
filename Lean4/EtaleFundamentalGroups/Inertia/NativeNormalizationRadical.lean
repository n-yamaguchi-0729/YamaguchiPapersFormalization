/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import SchemeTheory.Normalization.SubalgebraPreimage
import SchemeTheory.CategoryTheory.CommAlgRingMap
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic

/-!
# Ambient integral radicals in the actual native subalgebra normalization

Literal membership in the subalgebra and the already proved ambient
integrality construct the actual normalization element. Its power equation
is inherited through the two subtype inclusions. No fraction-field tower
or chosen absolute prime is opened in this owner.
-/

noncomputable section

namespace EtaleFundamentalGroups.Inertia

open SchemeTheory

universe u v

variable {A : Type u} {Ω : Type v} [CommRing A] [CommRing Ω] [Algebra A Ω]

/-- An actual integral ambient element in the selected subalgebra gives
an element of its literal native normalization. -/
def nativeNormalizationElement
    (S : Subalgebra A Ω) (α : Ω) (hmem : α ∈ S) (hint : IsIntegral A α) :
    subalgebraNormalizationCommAlgCat S :=
  ⟨⟨α, hmem⟩, (isIntegral_algHom_iff S.val Subtype.val_injective).mp hint⟩

/-- The original radical equation holds in the native normalization with
its computed coefficient map. -/
theorem nativeNormalizationElement_pow
    (S : Subalgebra A Ω) (α : Ω) (hmem : α ∈ S) (hint : IsIntegral A α)
    (n : ℕ) (π : A) (hpow : α ^ n = algebraMap A Ω π) :
    (nativeNormalizationElement S α hmem hint) ^ n =
      commAlgCoefficientMap (subalgebraNormalizationCommAlgCat S) π := by
  apply Subtype.ext
  apply Subtype.ext
  exact hpow

end EtaleFundamentalGroups.Inertia

end
