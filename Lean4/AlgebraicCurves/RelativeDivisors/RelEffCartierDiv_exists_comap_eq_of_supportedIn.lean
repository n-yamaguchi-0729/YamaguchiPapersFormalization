/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_RelEffCartierDiv_exists_comap_eq_of_supportedIn.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import AlgebraicCurves.RelativeDivisors.RelEffCartierDiv
import AlgebraicCurves.RelativeDivisors.RelEffCartierDivSupportedIn

/-!
# Rel Eff Cartier Div exists comap eq of supported In
-/

section ProofImplementation

namespace AlgebraicCurves.RelativeDivisors.Proofs.RelEffCartierDiv_exists_comap_eq_of_supportedIn

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem _root_.AlgebraicGeometry.RelEffCartierDiv.exists_comap_eq_of_supportedIn
    {𝒳 S : Scheme.{u}} {c : 𝒳 ⟶ S} (U : 𝒳.Opens) {r : ℕ} {T : Scheme.{u}} {g : T ⟶ S}
    (D : RelEffCartierDiv c r g) (hD : D.SupportedIn U) :
    ∃ D' : RelEffCartierDiv (U.ι ≫ c) r g,
      D'.I = D.I.comap (pullback.map (U.ι ≫ c) g c g U.ι (𝟙 T) (𝟙 S) (by simp) (by simp)) := by
  set j := pullback.map (U.ι ≫ c) g c g U.ι (𝟙 T) (𝟙 S) (by simp) (by simp) with hj
  have hrange : Set.range ⇑j = (pullback.fst c g) ⁻¹' (U : Set 𝒳) := by
    rw [hj, Scheme.Pullback.range_map]
    simp [Scheme.Opens.range_ι]
  have hjsnd : j ≫ pullback.snd c g = pullback.snd (U.ι ≫ c) g := by
    rw [hj, pullback.lift_snd, Category.comp_id]
  set Z := D.I.subscheme with hZ
  let ι := D.I.subschemeι
  have hZU : ∀ z : Z, ι z ∈ Set.range ⇑j := by
    intro z
    rw [hrange, Set.mem_preimage]
    have hz : ι z ∈ (D.I.support : Set ↥(pullback c g)) := by
      rw [← Scheme.IdealSheafData.range_subschemeι]; exact ⟨z, rfl⟩
    exact hD hz
  have : IsIso (pullback.snd j ι) := by
    refine isIso_of_isOpenImmersion_of_opensRange_eq_top _ ?_
    ext z
    simp only [Scheme.Hom.coe_opensRange, TopologicalSpace.Opens.coe_top, Set.mem_univ, iff_true]
    rw [Scheme.Pullback.range_snd]
    exact hZU z
  let e : (D.I.comap j).subscheme ⟶ Z := (D.I.comapIso j).hom ≫ pullback.snd j ι
  have : IsIso e := IsIso.comp_isIso
  have hfac : (D.I.comap j).subschemeι ≫ pullback.snd (U.ι ≫ c) g = e ≫ (ι ≫ pullback.snd c g) := by
    rw [← hjsnd, ← Scheme.IdealSheafData.comapIso_hom_fst]
    simp only [Category.assoc]
    rw [pullback.condition_assoc]
    rfl
  have := D.isFinite; have := D.flat; have := D.locallyOfFinitePresentation
  refine ⟨{ I := D.I.comap j
            isFinite := by rw [hfac]; infer_instance
            flat := by rw [hfac]; infer_instance
            locallyOfFinitePresentation := by rw [hfac]; infer_instance
            finrank_eq := fun t => by
              rw [hfac, Scheme.Hom.finrank_comp_left_of_isIso]
              exact D.finrank_eq t }, rfl⟩
end AlgebraicCurves.RelativeDivisors.Proofs.RelEffCartierDiv_exists_comap_eq_of_supportedIn
end ProofImplementation
