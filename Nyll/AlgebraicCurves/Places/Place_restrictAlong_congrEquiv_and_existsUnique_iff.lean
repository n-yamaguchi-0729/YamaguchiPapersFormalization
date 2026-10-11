/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_Place_restrictAlong_congrEquiv_and_existsUnique_iff.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Places.Rational.Basic
import Nyll.AlgebraicCurves.Divisors.Correspondences

/-!
# Place restrict Along congr Equiv and exists Unique iff
-/

section ProofImplementation

namespace AlgebraicCurves.Places.Proofs.Place_restrictAlong_congrEquiv_and_existsUnique_iff

open AlgebraicCurve

theorem _root_.AlgebraicCurve.Place.restrictAlong_congrEquiv_and_existsUnique_iff
    {K E F F' : Type*} [Field K] [Field E] [Field F] [Field F'] [Algebra K E] [Algebra K F]
      [Algebra K F']
    (φ : E →ₐ[K] F) (hφ : φ.toRingHom.IsIntegral) (φ' : E →ₐ[K] F') (hφ' : φ'.toRingHom.IsIntegral)
    (e : F ≃+* F') (he : ∀ a : K, e (algebraMap K F a) = algebraMap K F' a)
    (hcomm : ∀ x : E, e (φ x) = φ' x) :
    (∀ w : Place K F, (Place.congrEquiv e he w).restrictAlong φ' hφ' = w.restrictAlong φ hφ) ∧
    (∀ s : Place K E, ∀ w' : Place K F', w'.restrictAlong φ' hφ' = s ↔
        ((Place.congrEquiv e he).symm w').restrictAlong φ hφ = s) ∧
    (∀ s : Place K E, (∃! w : Place K F, w.restrictAlong φ hφ = s) ↔
        (∃! w' : Place K F', w'.restrictAlong φ' hφ' = s)) := by
  classical
  have h1 : ∀ w : Place K F, (Place.congrEquiv e he w).restrictAlong φ' hφ' = w.restrictAlong φ hφ
    := by
    intro w
    apply Place.ext
    ext x
    change (e.symm : F' →+* F) (φ'.toRingHom x) ∈ w.toValuationSubring ↔ φ.toRingHom x ∈
      w.toValuationSubring
    rw [show φ'.toRingHom x = φ' x from rfl, show φ.toRingHom x = φ x from rfl, ← hcomm]
    change e.symm (e (φ x)) ∈ w.toValuationSubring ↔ φ x ∈ w.toValuationSubring
    rw [e.symm_apply_apply]
  have h2 : ∀ s : Place K E, ∀ w' : Place K F', w'.restrictAlong φ' hφ' = s ↔
      ((Place.congrEquiv e he).symm w').restrictAlong φ hφ = s := by
    intro s w'
    rw [← h1 ((Place.congrEquiv e he).symm w'), Equiv.apply_symm_apply]
  refine ⟨h1, h2, fun s => ?_⟩
  constructor
  · rintro ⟨w, hw, huniq⟩
    refine ⟨Place.congrEquiv e he w, by
      change Place.restrictAlong φ' hφ' (Place.congrEquiv e he w) = s; rw [h1]; exact hw,
      fun w' hw' => ?_⟩
    have := huniq ((Place.congrEquiv e he).symm w') ((h2 s w').mp hw')
    rw [← this, Equiv.apply_symm_apply]
  · rintro ⟨w', hw', huniq⟩
    refine ⟨(Place.congrEquiv e he).symm w', (h2 s w').mp hw', fun w hw => ?_⟩
    have := huniq (Place.congrEquiv e he w)
      (by change Place.restrictAlong φ' hφ' (Place.congrEquiv e he w) = s; rw [h1]; exact hw)
    rw [← this, Equiv.symm_apply_apply]

end AlgebraicCurves.Places.Proofs.Place_restrictAlong_congrEquiv_and_existsUnique_iff
end ProofImplementation
