/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_CurveModel_ord_placeOfPoint_ffEquiv_symm_algebraMap_eq_one_of_maximalIdeal_eq_span.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Models.Basic

/-!
# Curve Model ord place Of Point ff Equiv symm algebra Map eq one of maximal Ideal eq span
-/

section ProofImplementation

namespace AlgebraicCurves.Models.Proofs
namespace CurveModel_ord_placeOfPoint_ffEquiv_symm_algebraMap_eq_one_of_maximalIdeal_eq_span

open CategoryTheory AlgebraicGeometry IsLocalRing

universe u v

end CurveModel_ord_placeOfPoint_ffEquiv_symm_algebraMap_eq_one_of_maximalIdeal_eq_span
end AlgebraicCurves.Models.Proofs

namespace AlgebraicCurve.CurveModel

universe u v

open _root_.AlgebraicCurves.Models.Proofs in
open CurveModel_ord_placeOfPoint_ffEquiv_symm_algebraMap_eq_one_of_maximalIdeal_eq_span in
open CategoryTheory AlgebraicGeometry IsLocalRing in
theorem ord_placeOfPoint_ffEquiv_symm_algebraMap_eq_one_of_maximalIdeal_eq_span
    {K : Type u} [Field K] {L : Type v} [Field L] [Algebra K L]
    (M : AlgebraicCurve.CurveModel K L) (x : closedPoints M.C) (g : M.C.presheaf.stalk x.1)
    (hg : IsLocalRing.maximalIdeal (M.C.presheaf.stalk x.1) = Ideal.span {g}) :
    (M.placeOfPoint x).ord (M.ffEquiv.symm (algebraMap (M.C.presheaf.stalk x.1) M.C.functionField
      g)) = 1 := by
  set V := (M.placeOfPoint x).toValuationSubring with hV
  set θ : M.C.presheaf.stalk x.1 →+* L :=
    (M.ffEquiv.symm : M.C.functionField ≃+* L).toRingHom.comp (algebraMap (M.C.presheaf.stalk x.1)
      M.C.functionField) with hθ_def
  have hθ : ∀ s, θ s = M.ffEquiv.symm (algebraMap (M.C.presheaf.stalk x.1) M.C.functionField s) :=
    fun s => rfl
  have hθ_inj : Function.Injective θ :=
    M.ffEquiv.symm.injective.comp (IsFractionRing.injective (M.C.presheaf.stalk x.1)
      M.C.functionField)
  have hrange : θ.range = V.toSubring := M.range_stalk_eq x
  have hmemV : ∀ s, θ s ∈ V := fun s => by
    have : θ s ∈ θ.range := ⟨s, rfl⟩
    rw [hrange] at this
    exact this
  set ψ : M.C.presheaf.stalk x.1 →+* V := θ.codRestrict V hmemV with hψ_def
  have hψ : ∀ s, ((ψ s : V) : L) = θ s := fun s => rfl
  have hψ_bij : Function.Bijective ψ := by
    refine ⟨fun a b hab => hθ_inj (by rw [← hψ, ← hψ, hab]), fun y => ?_⟩
    have hy : (y : L) ∈ θ.range := by rw [hrange]; exact y.2
    obtain ⟨s, hs⟩ := hy
    exact ⟨s, Subtype.ext (by rw [hψ, hs])⟩
  set ε : M.C.presheaf.stalk x.1 ≃+* V := RingEquiv.ofBijective ψ hψ_bij with hε_def
  have hε : ∀ s, ((ε s : V) : L) = θ s := fun s => rfl
  have hmax : IsLocalRing.maximalIdeal V = Ideal.span {ε g} := by
    have h1 : Ideal.map ε (IsLocalRing.maximalIdeal (M.C.presheaf.stalk x.1)) =
      IsLocalRing.maximalIdeal V := by
      have hM : (Ideal.map ε (IsLocalRing.maximalIdeal (M.C.presheaf.stalk x.1))).IsMaximal :=
        Ideal.map_isMaximal_of_equiv ε
      exact IsLocalRing.eq_maximalIdeal hM
    rw [← h1, hg, Ideal.map_span, Set.image_singleton]
  have hg0 : (ε g : V) ≠ 0 := by
    intro h0
    have hbot : IsLocalRing.maximalIdeal V = ⊥ := by rw [hmax, h0, Ideal.span_singleton_eq_bot]
    exact IsDiscreteValuationRing.not_a_field V hbot
  have hirr : Irreducible (ε g : V) :=
    IsDiscreteValuationRing.irreducible_of_span_eq_maximalIdeal (ε g) hg0 hmax
  rw [← hθ, ← hε]
  exact (M.placeOfPoint x).ord_coe_irreducible hirr
end AlgebraicCurve.CurveModel
end ProofImplementation
