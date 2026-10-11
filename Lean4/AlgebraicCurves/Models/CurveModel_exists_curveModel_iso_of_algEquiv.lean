/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_CurveModel_exists_curveModel_iso_of_algEquiv.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import AlgebraicCurves.Models.Basic
import AlgebraicCurves.Places.Rational.Basic

/-!
# Curve Model exists curve Model iso of alg Equiv
-/

section ProofImplementation

namespace AlgebraicCurves.Models.Proofs.CurveModel_exists_curveModel_iso_of_algEquiv

open CategoryTheory AlgebraicGeometry AlgebraicCurve

universe u v

theorem _root_.AlgebraicCurve.CurveModel.exists_curveModel_iso_of_algEquiv
    {K : Type u} [Field K] {L L' : Type v} [Field L] [Field L'] [Algebra K L] [Algebra K L']
    (e : L ≃ₐ[K] L') (M : AlgebraicCurve.CurveModel K L) :
    ∃ (M' : AlgebraicCurve.CurveModel K L') (f : M'.C ≅ M.C), f.hom ≫ M.toBase = M'.toBase := by
  have he : ∀ a : K, e.toRingEquiv (algebraMap K L a) = algebraMap K L' a := fun a => e.commutes a
  refine ⟨{ C := M.C
            toBase := M.toBase
            ffEquiv := e.symm.toRingEquiv.trans M.ffEquiv
            ffEquiv_algebraMap := fun a => ?_
            placeOfPoint := fun x => Place.congrRingEquiv e.toRingEquiv he (M.placeOfPoint x)
            placeOfPoint_bijective := (Place.congrEquiv e.toRingEquiv he).bijective.comp
              M.placeOfPoint_bijective
            range_stalk_eq := fun x => ?_
            finset_subset_affineOpen := M.finset_subset_affineOpen }, Iso.refl _, Category.id_comp
              _⟩
  · change M.ffEquiv (e.symm.toRingEquiv (algebraMap K L' a)) = _
    rw [show e.symm.toRingEquiv (algebraMap K L' a) = algebraMap K L a from e.symm.commutes a]
    exact M.ffEquiv_algebraMap a
  · have h := M.range_stalk_eq x
    ext y
    constructor
    · rintro ⟨s, rfl⟩
      change e.toRingEquiv.symm ((e.symm.toRingEquiv.trans M.ffEquiv).symm (algebraMap _ _ s)) ∈
        (M.placeOfPoint x).toValuationSubring
      have hs : M.ffEquiv.symm (algebraMap _ _ s) ∈ (M.placeOfPoint x).toValuationSubring.toSubring
        := by
        rw [← h]; exact ⟨s, rfl⟩
      rw [RingEquiv.symm_trans_apply]
      change e.symm (e.symm.symm (M.ffEquiv.symm (algebraMap _ _ s))) ∈ _
      rw [AlgEquiv.symm_symm, AlgEquiv.symm_apply_apply]
      exact hs
    · intro hy
      change e.toRingEquiv.symm y ∈ (M.placeOfPoint x).toValuationSubring at hy
      have hy' : e.toRingEquiv.symm y ∈ ((M.ffEquiv.symm : M.C.functionField ≃+* L).toRingHom.comp
          (algebraMap (M.C.presheaf.stalk x.1) M.C.functionField)).range := by
        rw [h]; exact hy
      obtain ⟨s, hs⟩ := hy'
      refine ⟨s, ?_⟩
      change (e.symm.toRingEquiv.trans M.ffEquiv).symm (algebraMap _ _ s) = y
      rw [RingEquiv.symm_trans_apply]
      change e.symm.symm (M.ffEquiv.symm (algebraMap _ _ s)) = y
      rw [show M.ffEquiv.symm (algebraMap _ _ s) = e.toRingEquiv.symm y from hs, AlgEquiv.symm_symm]
      exact e.apply_symm_apply y

end AlgebraicCurves.Models.Proofs.CurveModel_exists_curveModel_iso_of_algEquiv
end ProofImplementation
