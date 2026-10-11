/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_exists_isUnit_appTop_eq_of_bijective_of_surjective_of_ker_le_maximalIdeal.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Batteries.Tactic.Init
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic

/-!
# exists is Unit app Top eq of bijective of surjective of ker le maximal Ideal
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Schemes.Proofs
namespace exists_isUnit_appTop_eq_of_bijective_of_surjective_of_ker_le_maximalIdeal

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem
  _root_.AlgebraicGeometry.exists_isUnit_appTop_eq_of_bijective_of_surjective_of_ker_le_maximalIdeal
    {B₁ B₀ : Type} [CommRing B₁] [IsLocalRing B₁] [CommRing B₀]
    (π : B₁ →+* B₀) (hπ : Function.Surjective π) (hI : RingHom.ker π ≤ IsLocalRing.maximalIdeal B₁)
    {X X₀ : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of B₁)) (f₀ : X₀ ⟶ Spec (CommRingCat.of B₀)) (g
      : X₀ ⟶ X)
    (hg : g ≫ f = f₀ ≫ Spec.map (CommRingCat.ofHom π))
    (_h₁ : Function.Bijective ((Scheme.ΓSpecIso (CommRingCat.of B₁)).inv ≫ f.appTop).hom)
    (h₀ : Function.Bijective ((Scheme.ΓSpecIso (CommRingCat.of B₀)).inv ≫ f₀.appTop).hom)
    (s : Γ(X₀, ⊤)) (hs : IsUnit s) :
    ∃ u : Γ(X, ⊤), IsUnit u ∧ g.appTop.hom u = s := by
  classical
  have hnat : ∀ c : B₁, g.appTop.hom (((Scheme.ΓSpecIso (CommRingCat.of B₁)).inv ≫ f.appTop).hom c)
    =
      ((Scheme.ΓSpecIso (CommRingCat.of B₀)).inv ≫ f₀.appTop).hom (π c) := by
    intro c
    have hN := congrArg (fun k => (k.hom) c) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom π))
    have hC := congrArg (fun k => (k.hom) ((Scheme.ΓSpecIso (CommRingCat.of B₁)).inv.hom c))
      (show f.appTop ≫ g.appTop = (Spec.map (CommRingCat.ofHom π)).appTop ≫ f₀.appTop from by
        rw [← Scheme.Hom.comp_appTop, hg, Scheme.Hom.comp_appTop])
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at hN hC ⊢
    rw [hC, ← hN]
    rfl
  let e₀ := RingEquiv.ofBijective ((Scheme.ΓSpecIso (CommRingCat.of B₀)).inv ≫ f₀.appTop).hom h₀
  obtain ⟨c₀, hc₀⟩ := h₀.2 s
  have hc₀u : IsUnit c₀ := by
    have h' : e₀.symm s = c₀ := e₀.injective (by rw [RingEquiv.apply_symm_apply]; exact hc₀.symm)
    exact h' ▸ hs.map e₀.symm
  obtain ⟨c, rfl⟩ := hπ c₀
  have hcu : IsUnit c := by
    by_contra hcu
    have hcm : c ∈ IsLocalRing.maximalIdeal B₁ := (IsLocalRing.mem_maximalIdeal c).mpr
      (mem_nonunits_iff.mpr hcu)
    obtain ⟨d₀, hd₀⟩ := hc₀u.exists_right_inv
    obtain ⟨d, rfl⟩ := hπ d₀
    have hk : c * d - 1 ∈ RingHom.ker π :=
      by rw [RingHom.mem_ker, map_sub, map_mul, map_one, hd₀, sub_self]
    have h1 : (1 : B₁) ∈ IsLocalRing.maximalIdeal B₁ := by
      have := Ideal.sub_mem _ (Ideal.mul_mem_right d _ hcm) (hI hk)
      rwa [sub_sub_cancel] at this
    exact (IsLocalRing.maximalIdeal.isMaximal B₁).ne_top (Ideal.eq_top_of_isUnit_mem _ h1
      isUnit_one)
  exact ⟨((Scheme.ΓSpecIso (CommRingCat.of B₁)).inv ≫ f.appTop).hom c, hcu.map _, by rw [hnat, hc₀]⟩
end exists_isUnit_appTop_eq_of_bijective_of_surjective_of_ker_le_maximalIdeal
end AlgebraicCurves.Geometry.Schemes.Proofs
end ProofImplementation
