/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_Place_card_fiberOver_mul_ramificationIndex_mul_inertiaDeg.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Places.OverDVR
import Mathlib.FieldTheory.Galois.Basic
import Nyll.AlgebraicCurves.Places.Place_ramificationIndex_eq_of_restrict_eq
import Nyll.AlgebraicCurves.Places.Place_inertiaDeg_eq_of_restrict_eq
import Nyll.AlgebraicCurves.Places.Place_sum_ramificationIndex_mul_inertiaDeg_fiberOver

/-!
# Place card fiber Over mul ramification Index mul inertia Deg
-/

section ProofImplementation

namespace AlgebraicCurves.Places.Proofs.Place_card_fiberOver_mul_ramificationIndex_mul_inertiaDeg

noncomputable section
open _root_.AlgebraicCurve
open _root_.IsDedekindDomain
open scoped Pointwise

namespace AlgebraicCurve
open _root_.AlgebraicCurve
open _root_.AlgebraicCurve
namespace Place
open _root_.AlgebraicCurve.Place
open _root_.AlgebraicCurve.Place

variable {K F' M : Type*} [Field K] [Field F'] [Field M] [Algebra K F'] [Algebra K M]
  [Algebra F' M] [IsScalarTower K F' M]

end Place
end AlgebraicCurve

open _root_.AlgebraicCurve.Place AlgebraicCurve.Place in
theorem _root_.AlgebraicCurve.Place.card_fiberOver_mul_ramificationIndex_mul_inertiaDeg {K F' M :
  Type*} [Field K] [Field F'] [Field M]
    [Algebra K F'] [Algebra K M] [Algebra F' M] [IsScalarTower K F' M]
    [FiniteDimensional F' M] [IsGalois F' M] (w : Place K F') (W : Place K M)
    (hW : W.restrict F' = w) :
    (w.fiberOver M).card * (W.ramificationIndex F' * W.inertiaDeg F') = Module.finrank F' M := by
  have hsum := sum_ramificationIndex_mul_inertiaDeg_fiberOver (F' := M) w
  have hconst : ∀ W' ∈ w.fiberOver M,
      (W'.ramificationIndex F' : ℤ) * (W'.inertiaDeg F' : ℤ)
        = (W.ramificationIndex F' : ℤ) * (W.inertiaDeg F' : ℤ) := by
    intro W' hW'
    have h : W'.restrict F' = W.restrict F' :=
      (restrict_eq_of_mem_fiberOver w hW').trans hW.symm
    rw [Place.ramificationIndex_eq_of_restrict_eq W W' h, Place.inertiaDeg_eq_of_restrict_eq W W' h]
  rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul] at hsum
  exact_mod_cast hsum

end
end AlgebraicCurves.Places.Proofs.Place_card_fiberOver_mul_ramificationIndex_mul_inertiaDeg
end ProofImplementation
