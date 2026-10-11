/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_Place_ramificationIndexAlong_comp.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Divisors.Correspondences
import Nyll.AlgebraicCurves.Places.Place_restrictAlong_restrictAlong

/-!
# Place ramification Index Along comp
-/

section ProofImplementation

namespace AlgebraicCurves.Places.Proofs.Place_ramificationIndexAlong_comp

open IsDedekindDomain AlgebraicCurve

theorem _root_.AlgebraicCurve.Place.ramificationIndexAlong_comp {K F F' F'' : Type*} [Field K]
  [Field F] [Field F'] [Field F''] [Algebra K F] [Algebra K F'] [Algebra K F''] (φ : F →ₐ[K] F') (χ
  : F' →ₐ[K] F'') (hφ : φ.toRingHom.IsIntegral) (hχ : χ.toRingHom.IsIntegral) (hχφ : (χ.comp
  φ).toRingHom.IsIntegral) (W : Place K F'') : Place.ramificationIndexAlong (χ.comp φ) W =
  Place.ramificationIndexAlong χ W * Place.ramificationIndexAlong φ (W.restrictAlong χ hχ) := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible
    (W.restrictAlong (χ.comp φ) hχφ).toValuationSubring
  have hπord : (W.restrictAlong (χ.comp φ) hχφ).ord
      ((π : (W.restrictAlong (χ.comp φ) hχφ).toValuationSubring) : F) = 1 :=
    (W.restrictAlong (χ.comp φ) hχφ).ord_coe_irreducible hπ
  set f : F := ((π : (W.restrictAlong (χ.comp φ) hχφ).toValuationSubring) : F) with hf
  have h1 : W.ord ((χ.comp φ) f) = (Place.ramificationIndexAlong (χ.comp φ) W : ℤ) := by
    rw [W.ord_restrictAlong (χ.comp φ) hχφ, hπord, mul_one]
  have h2 : W.ord ((χ.comp φ) f)
      = (Place.ramificationIndexAlong χ W : ℤ)
          * (Place.ramificationIndexAlong φ (W.restrictAlong χ hχ) : ℤ) := by
    rw [AlgHom.comp_apply, W.ord_restrictAlong χ hχ, (W.restrictAlong χ hχ).ord_restrictAlong φ hφ,
      AlgebraicCurve.Place.restrictAlong_restrictAlong φ χ hφ hχ hχφ, hπord, mul_one]
  exact_mod_cast h1.symm.trans h2
end AlgebraicCurves.Places.Proofs.Place_ramificationIndexAlong_comp
end ProofImplementation
