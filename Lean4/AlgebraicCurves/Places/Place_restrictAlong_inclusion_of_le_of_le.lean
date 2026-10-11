/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_Place_restrictAlong_inclusion_of_le_of_le.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import AlgebraicCurves.Divisors.Correspondences

/-!
# Place restrict Along inclusion of le of le
-/

section ProofImplementation

namespace AlgebraicCurves.Places.Proofs.Place_restrictAlong_inclusion_of_le_of_le

open _root_.AlgebraicCurve

namespace AlgebraicCurve
open _root_.AlgebraicCurve
namespace Place
open _root_.AlgebraicCurve.Place
namespace ITransportSeam
open _root_.AlgebraicCurve.Place
open _root_.AlgebraicCurve

theorem restrictAlong_incl_incl {K E : Type*} [Field K] [Field E] [Algebra K E]
    {S T : IntermediateField K E} (h₁ : S ≤ T) (h₂ : T ≤ S)
    (hι₁ : (IntermediateField.inclusion h₁).toRingHom.IsIntegral) (hι₂ :
      (IntermediateField.inclusion h₂).toRingHom.IsIntegral)
    (W : Place K ↥S) :
    (W.restrictAlong (IntermediateField.inclusion h₂) hι₂).restrictAlong
      (IntermediateField.inclusion h₁) hι₁ = W := by
  apply Place.ext
  ext x
  exact (show IntermediateField.inclusion h₂ (IntermediateField.inclusion h₁ x) ∈
    W.toValuationSubring ↔ x ∈ W.toValuationSubring by
    rw [IntermediateField.inclusion_inclusion, IntermediateField.inclusion_self, AlgHom.id_apply])

theorem ramificationIndexAlong_incl_eq_one {K E : Type*} [Field K] [Field E] [Algebra K E]
    {S T : IntermediateField K E} (h₁ : S ≤ T) (h₂ : T ≤ S)
    (hι₁ : (IntermediateField.inclusion h₁).toRingHom.IsIntegral) (hι₂ :
      (IntermediateField.inclusion h₂).toRingHom.IsIntegral)
    (W' : Place K ↥T) : W'.ramificationIndexAlong (IntermediateField.inclusion h₁) = 1 := by
  classical
  set W := W'.restrictAlong (IntermediateField.inclusion h₁) hι₁ with hW
  have hWW' : W.restrictAlong (IntermediateField.inclusion h₂) hι₂ = W' := restrictAlong_incl_incl
    h₂ h₁ hι₂ hι₁ W'
  have e1 : ∀ f : ↥S, W'.ord (IntermediateField.inclusion h₁ f) =
      Place.ramificationIndexAlong (IntermediateField.inclusion h₁) W' * W.ord f :=
    fun f => Place.ord_restrictAlong _ hι₁ W' f
  have e2 : ∀ f' : ↥T, W.ord (IntermediateField.inclusion h₂ f') =
      Place.ramificationIndexAlong (K := K) (F := T) (F' := S)
        (IntermediateField.inclusion h₂) W * W'.ord f' := by
    intro f'
    have := Place.ord_restrictAlong _ hι₂ W f'
    rwa [hWW'] at this
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible W.toValuationSubring
  have hπ1 : W.ord (π : ↥S) = 1 := W.ord_coe_irreducible hπ
  have hprod : (Place.ramificationIndexAlong (K := K) (F := T) (F' := S)
      (IntermediateField.inclusion h₂) W : ℤ) *
      Place.ramificationIndexAlong (K := K) (F := S) (F' := T)
        (IntermediateField.inclusion h₁) W' = 1 := by
    have hh := e2 (IntermediateField.inclusion h₁ (π : ↥S))
    rw [IntermediateField.inclusion_inclusion, IntermediateField.inclusion_self, AlgHom.id_apply,
      hπ1, e1, hπ1, mul_one] at hh
    exact hh.symm
  have hone : (Place.ramificationIndexAlong (K := K) (F := S) (F' := T)
      (IntermediateField.inclusion h₁) W' : ℤ) = 1 := by
    have hnn1 : (0 : ℤ) ≤ Place.ramificationIndexAlong (K := K) (F := S) (F' := T)
      (IntermediateField.inclusion h₁) W' := Int.natCast_nonneg _
    rw [mul_comm] at hprod
    exact Int.eq_one_of_mul_eq_one_right hnn1 hprod
  exact_mod_cast hone

end AlgebraicCurve.Place.ITransportSeam

open AlgebraicCurve.Place.ITransportSeam in
theorem _root_.AlgebraicCurve.Place.restrictAlong_inclusion_of_le_of_le
    {K E : Type*} [Field K] [Field E] [Algebra K E]
    {S T : IntermediateField K E} (hST : S ≤ T) (hTS : T ≤ S)
    (h : (IntermediateField.inclusion hST).toRingHom.IsIntegral)
    (h' : (IntermediateField.inclusion hTS).toRingHom.IsIntegral) :
    (∀ w : Place K T, (w.restrictAlong (IntermediateField.inclusion hST) h).restrictAlong
      (IntermediateField.inclusion hTS) h' = w) ∧
    (∀ v : Place K S, (v.restrictAlong (IntermediateField.inclusion hTS) h').restrictAlong
      (IntermediateField.inclusion hST) h = v) ∧
    (∀ w : Place K T, w.ramificationIndexAlong
      (IntermediateField.inclusion hST : S →ₐ[K] T) = 1) ∧
    (∀ (w : Place K T) (f : S),
      (w.restrictAlong (IntermediateField.inclusion hST : S →ₐ[K] T) h).ord f =
        w.ord (IntermediateField.inclusion hST f)) := by
  refine ⟨fun w => restrictAlong_incl_incl hTS hST h' h w, fun v => restrictAlong_incl_incl hST hTS
    h h' v,
    fun w => ramificationIndexAlong_incl_eq_one hST hTS h h' w, fun w f => ?_⟩
  rw [Place.ord_restrictAlong _ h w f, ramificationIndexAlong_incl_eq_one hST hTS h h' w,
    Nat.cast_one, one_mul]
end AlgebraicCurves.Places.Proofs.Place_restrictAlong_inclusion_of_le_of_le
end ProofImplementation
