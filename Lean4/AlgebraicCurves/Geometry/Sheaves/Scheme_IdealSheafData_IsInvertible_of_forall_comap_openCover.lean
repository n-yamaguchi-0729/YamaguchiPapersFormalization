/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_of_forall_comap_openCover.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Cover.Open
import Mathlib.Algebra.GroupWithZero.NonZeroDivisors
import Mathlib.RingTheory.Ideal.Maps
import AlgebraicCurves.RelativeDivisors.Cartier

/-!
# Scheme Ideal Sheaf Data Is Invertible of forall comap open Cover
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Sheaves.Proofs
namespace Scheme_IdealSheafData_IsInvertible_of_forall_comap_openCover

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

namespace INVLOCALCOVER

variable {W X : Scheme.{u}} (j : W ⟶ X) [IsOpenImmersion j] (I : X.IdealSheafData)

theorem image_basicOpen_eq (U : W.Opens) (f : Γ(W, U)) :
    j ''ᵁ (W.basicOpen f) = X.basicOpen ((j.appIso U).inv.hom f) := by
  have h1 : j ⁻¹ᵁ X.basicOpen ((j.appIso U).inv.hom f) = W.basicOpen f := by
    rw [Scheme.Hom.preimage_basicOpen, ← CommRingCat.comp_apply, Scheme.Hom.appIso_inv_app,
      Scheme.basicOpen_res]
    exact inf_eq_right.mpr (W.basicOpen_le f |>.trans (by simp))
  have h2 : X.basicOpen ((j.appIso U).inv.hom f) ≤ j.opensRange :=
    (X.basicOpen_le _).trans (Scheme.Hom.image_le_opensRange j U)
  rw [← h1, Scheme.Hom.image_preimage_eq_opensRange_inf, inf_eq_right.mpr h2]

theorem at_image (h : (I.comap j).IsInvertible) (w : W) :
    ∃ (U : X.affineOpens) (f : Γ(X, U)), j w ∈ X.basicOpen f ∧
      ∃ g ∈ nonZeroDivisors Γ(X, X.affineBasicOpen f), I.ideal (X.affineBasicOpen f) = Ideal.span
        {g} := by
  classical
  obtain ⟨U, f, hwf, g, hg, hIg⟩ := h w
  let U₀ : X.affineOpens := ⟨j ''ᵁ (U : W.Opens), U.2.image_of_isOpenImmersion j⟩
  let f' : Γ(X, (U₀ : X.Opens)) := (j.appIso U).inv.hom f
  let B : W.affineOpens := W.affineBasicOpen f
  let e := j.appIso (B : W.Opens)
  have himg : j ''ᵁ (B : W.Opens) = X.basicOpen f' := image_basicOpen_eq j U f
  have hU₁ : IsAffineOpen (j ''ᵁ (B : W.Opens)) := B.2.image_of_isOpenImmersion j
  have hdata : ∃ g' ∈ nonZeroDivisors Γ(X, j ''ᵁ (B : W.Opens)),
      I.ideal ⟨j ''ᵁ (B : W.Opens), hU₁⟩ = Ideal.span {g'} := by
    have hc : (I.comap j).ideal B = Ideal.comap e.inv.hom (I.ideal ⟨j ''ᵁ (B : W.Opens), hU₁⟩) :=
      Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion I j B
    have hsurj : Function.Surjective e.inv.hom := e.commRingCatIsoToRingEquiv.symm.surjective
    have hinj : Function.Injective e.inv.hom := e.commRingCatIsoToRingEquiv.symm.injective
    refine ⟨e.inv.hom g, ?_, ?_⟩
    · rw [mem_nonZeroDivisors_iff]
      refine ⟨fun a ha => ?_, fun a ha => ?_⟩
      · obtain ⟨b, rfl⟩ := hsurj a
        rw [← map_mul] at ha
        have hb : g * b = 0 := hinj (by rw [ha, map_zero])
        rw [(mem_nonZeroDivisors_iff.mp hg).1 b hb, map_zero]
      · obtain ⟨b, rfl⟩ := hsurj a
        rw [← map_mul] at ha
        have hb : b * g = 0 := hinj (by rw [ha, map_zero])
        rw [(mem_nonZeroDivisors_iff.mp hg).2 b hb, map_zero]
    · have := Ideal.map_comap_of_surjective e.inv.hom hsurj (I.ideal ⟨j ''ᵁ (B : W.Opens), hU₁⟩)
      rw [← hc, hIg, Ideal.map_span, Set.image_singleton] at this
      exact this.symm
  have heq : (⟨j ''ᵁ (B : W.Opens), hU₁⟩ : X.affineOpens) = X.affineBasicOpen f' := Subtype.ext himg
  refine ⟨U₀, f', ?_, ?_⟩
  · rw [← himg]; exact ⟨w, hwf, rfl⟩
  · rw [← heq]; exact hdata

theorem main {X : Scheme.{u}} (𝒰 : X.OpenCover) (I : X.IdealSheafData)
    (h : ∀ i, (I.comap (𝒰.f i)).IsInvertible) : I.IsInvertible := by
  intro x
  obtain ⟨i, w, rfl⟩ := 𝒰.exists_eq x
  exact at_image (𝒰.f i) I (h i) w

end INVLOCALCOVER

theorem _root_.AlgebraicGeometry.Scheme.IdealSheafData.IsInvertible.of_forall_comap_openCover
    {X : Scheme.{u}} (𝒰 : X.OpenCover) (I : X.IdealSheafData)
    (h : ∀ i, (I.comap (𝒰.f i)).IsInvertible) : I.IsInvertible :=
  INVLOCALCOVER.main 𝒰 I h
end Scheme_IdealSheafData_IsInvertible_of_forall_comap_openCover
end AlgebraicCurves.Geometry.Sheaves.Proofs
end ProofImplementation
