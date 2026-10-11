/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_RelEffCartierDiv_exists_supportedIn_comap_eq_of_isSeparated.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Nyll.AlgebraicCurves.RelativeDivisors.RelEffCartierDiv
import Nyll.AlgebraicCurves.RelativeDivisors.RelEffCartierDivSupportedIn

/-!
# Rel Eff Cartier Div exists supported In comap eq of is Separated
-/

section ProofImplementation

namespace AlgebraicCurves.RelativeDivisors.Proofs
namespace RelEffCartierDiv_exists_supportedIn_comap_eq_of_isSeparated

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem _root_.AlgebraicGeometry.RelEffCartierDiv.exists_supportedIn_comap_eq_of_isSeparated
    {𝒳 S : Scheme.{u}} {c : 𝒳 ⟶ S} [IsSeparated c] (U : 𝒳.Opens) {r : ℕ} {T : Scheme.{u}} {g : T ⟶
      S}
    (D : RelEffCartierDiv (U.ι ≫ c) r g) :
    ∃ D' : RelEffCartierDiv c r g, D'.SupportedIn U ∧
      D'.I.comap (pullback.map (U.ι ≫ c) g c g U.ι (𝟙 T) (𝟙 S) (by simp) (by simp)) = D.I ∧
      D'.I = D.I.map (pullback.map (U.ι ≫ c) g c g U.ι (𝟙 T) (𝟙 S) (by simp) (by simp)) := by
  set j := pullback.map (U.ι ≫ c) g c g U.ι (𝟙 T) (𝟙 S) (by simp) (by simp) with hj
  have hrange : Set.range ⇑j = (pullback.fst c g) ⁻¹' (U : Set 𝒳) := by
    rw [hj, Scheme.Pullback.range_map]
    simp [Scheme.Opens.range_ι]
  have hjsnd : j ≫ pullback.snd c g = pullback.snd (U.ι ≫ c) g := by
    rw [hj, pullback.lift_snd, Category.comp_id]
  have := D.isFinite; have := D.flat; have := D.locallyOfFinitePresentation
  set f := D.I.subschemeι ≫ j with hf
  have hfin : IsFinite f := by
    have h2 : IsFinite (f ≫ pullback.snd c g) := by
      rw [hf, Category.assoc, hjsnd]; infer_instance
    exact MorphismProperty.of_postcomp (W := @IsFinite) f (pullback.snd c g) (inferInstance :
      IsSeparated _) h2
  have hci : IsClosedImmersion f := by
    rw [IsClosedImmersion.iff_isFinite_and_mono]
    exact ⟨hfin, by rw [hf]; exact mono_comp _ _⟩
  have : IsIso f.toImage := inferInstance
  have hfac : f.imageι ≫ pullback.snd c g = inv f.toImage ≫ (D.I.subschemeι ≫ pullback.snd (U.ι ≫
    c) g) := by
    rw [IsIso.eq_inv_comp, ← Category.assoc, Scheme.Hom.toImage_imageι, hf, Category.assoc, hjsnd]
  refine ⟨{ I := f.ker
            isFinite := by change IsFinite (f.imageι ≫ _); rw [hfac]; infer_instance
            flat := by change Flat (f.imageι ≫ _); rw [hfac]; infer_instance
            locallyOfFinitePresentation := by
              change LocallyOfFinitePresentation (f.imageι ≫ _); rw [hfac]; infer_instance
            finrank_eq := fun t => by
              change (f.imageι ≫ pullback.snd c g).finrank t = r
              rw [hfac, Scheme.Hom.finrank_comp_left_of_isIso]
              exact D.finrank_eq t }, ?_, ?_, rfl⟩
  · intro x hx
    change x ∈ (f.ker.support : Set ↥(pullback c g)) at hx
    rw [Scheme.Hom.support_ker, f.isClosedEmbedding.isClosed_range.closure_eq] at hx
    obtain ⟨z, rfl⟩ := hx
    change (pullback.fst c g) (f z) ∈ (U : Set 𝒳)
    rw [← Set.mem_preimage, ← hrange, hf]
    exact ⟨D.I.subschemeι z, (Scheme.Hom.comp_apply _ _ z).symm⟩
  · change f.ker.comap j = D.I
    rw [← Scheme.IdealSheafData.ker_fst_of_isClosedImmersion]
    have hsurj : IsIso (pullback.snd j f) := by
      refine isIso_of_isOpenImmersion_of_opensRange_eq_top _ ?_
      ext z
      simp only [Scheme.Hom.coe_opensRange, TopologicalSpace.Opens.coe_top, Set.mem_univ, iff_true]
      rw [Scheme.Pullback.range_snd, hf]
      exact ⟨D.I.subschemeι z, (Scheme.Hom.comp_apply _ _ z).symm⟩
    have hfst : pullback.fst j f = pullback.snd j f ≫ D.I.subschemeι := by
      rw [← cancel_mono j, Category.assoc, ← hf]
      exact pullback.condition
    rw [hfst, Scheme.Hom.ker_comp_of_isIso, Scheme.IdealSheafData.ker_subschemeι]
end RelEffCartierDiv_exists_supportedIn_comap_eq_of_isSeparated
end AlgebraicCurves.RelativeDivisors.Proofs
end ProofImplementation
