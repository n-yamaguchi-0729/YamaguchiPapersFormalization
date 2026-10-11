/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Inertia.AffineNormalizationGeometricPoint
import Mathlib.RingTheory.Invariant.Galois

/-!
# The two actual Galois actions on an integral closure

The fraction-ring restriction used by ramification theory and the literal
restriction used by normalization geometry agree on the embedded integral
closure. The comparison follows by applying its injective inclusion into the
common field, where both automorphisms are the original field automorphism.
-/

noncomputable section

namespace EtaleFundamentalGroups.Inertia

universe u

variable (R K L : Type u) [CommRing R] [Field K] [Field L]
  [Algebra R K] [Algebra K L] [Algebra R L] [IsScalarTower R K L]
  [IsFractionRing R K] [Algebra.IsAlgebraic K L]

/-- Fraction-ring restriction and literal restriction define the same
homomorphism into the automorphisms of the integral closure. -/
theorem galRestrict_integralClosure_eq :
    (galRestrict R K L (integralClosure R L)).toMonoidHom =
      (integralClosureAutHom R L).comp (AlgEquiv.restrictScalarsHom R) := by
  apply MonoidHom.ext
  intro σ
  apply AlgEquiv.ext
  intro b
  apply Subtype.ext
  exact algebraMap_galRestrict_apply R σ b

/-- The normalization-ring action in ramification theory is the actual
restriction action on the same integral closure, with no choice of comparison. -/
theorem integralClosureGaloisAction_eq :
    IsIntegralClosure.MulSemiringAction R K L (integralClosure R L) =
      MulSemiringAction.compHom (integralClosure R L)
        ((integralClosureAutHom R L).comp (AlgEquiv.restrictScalarsHom R)) := by
  change MulSemiringAction.compHom (integralClosure R L)
    (galRestrict R K L (integralClosure R L)).toMonoidHom = _
  rw [galRestrict_integralClosure_eq R K L]

end EtaleFundamentalGroups.Inertia
