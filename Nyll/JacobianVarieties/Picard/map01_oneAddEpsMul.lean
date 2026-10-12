/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_RelPicard_map01_oneAddEpsMul.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.JacobianVarieties.Picard.PicDualNumberDeformationClassSpec

/-!
# Naturality of the dual-number overlap unit
-/


section ProofImplementation

namespace JacobianVarieties.Picard.Proofs.S_AlgebraicGeometry_RelPicard_map01_oneAddEpsMul

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry NeronModelInfra
  AlgebraicGeometry.RelPicard AlgebraicGeometry.Scheme.TwoAffineOpenCover

theorem _root_.AlgebraicGeometry.RelPicard.map01_oneAddEpsMul
    {R : Type u} [CommRing R] {C C' : Scheme.{u}} {c : C ⟶ Spec (.of R)} {c' : C' ⟶ Spec (.of R)}
    {A : Type u} [CommRing A] [Algebra R A] {𝒱 : C.TwoAffineOpenCover} {𝒲 : C'.TwoAffineOpenCover}
    (f : HomOver (RingHom.id A) (𝒱.pullback c A) (pullback.snd c (specMap R A))
      (𝒲.pullback c' A) (pullback.snd c' (specMap R A)))
    (fε : HomOver (RingHom.id (DualNumber A))
      (𝒱.pullback c (DualNumber A)) (pullback.snd c (specMap R (DualNumber A)))
      (𝒲.pullback c' (DualNumber A)) (pullback.snd c' (specMap R (DualNumber A))))
    (hcomm : fε.hom ≫ (dualNumberThickening A 𝒱 c).hom = (dualNumberThickening A 𝒲 c').hom ≫ f.hom)
    (t : ((𝒱.pullback c A).cover (pullback.snd c (specMap R A))).A01) :
    fε.map01 (oneAddEpsMul A 𝒱 c t) = oneAddEpsMul A 𝒲 c' (f.map01 t) := by
  have key : ∀ {X' Y' : Scheme.{u}} (φ ψ : Y' ⟶ X') (_ : φ = ψ) (U : X'.Opens) (W : Y'.Opens)
      (e₁ : W ≤ φ ⁻¹ᵁ U) (e₂ : W ≤ ψ ⁻¹ᵁ U), φ.appLE U W e₁ = ψ.appLE U W e₂ := by
    rintro X' Y' φ ψ rfl U W e₁ e₂; rfl
  rw [oneAddEpsMul, oneAddEpsMul, map_add]
  congr 1
  · rw [HomOver.map01_apply]
    exact map_one (fε.hom.appLE _ _ fε.inf_le).hom
  · rw [HomOver.map01_apply]
    refine (map_mul (fε.hom.appLE _ _ fε.inf_le).hom _ _).trans ?_
    congr 1
    · exact fε.appLE_algebraMap fε.inf_le DualNumber.eps
    · have happ :
          (dualNumberThickening A 𝒱 c).hom.appLE _ _ (dualNumberThickening A 𝒱 c).inf_le ≫
              fε.hom.appLE _ _ fε.inf_le =
            f.hom.appLE _ _ f.inf_le ≫
              (dualNumberThickening A 𝒲 c').hom.appLE _ _ (dualNumberThickening A 𝒲 c').inf_le := by
        rw [Scheme.Hom.appLE_comp_appLE, Scheme.Hom.appLE_comp_appLE]
        exact key _ _ hcomm _ _ _ _
      exact congrArg
        (fun φ :
            Γ(Limits.pullback c (specMap R A), (𝒱.pullback c A).U0 ⊓ (𝒱.pullback c A).U1) ⟶
              Γ(Limits.pullback c' (specMap R (DualNumber A)),
                (𝒲.pullback c' (DualNumber A)).U0 ⊓ (𝒲.pullback c' (DualNumber A)).U1) =>
          φ.hom (show Γ(Limits.pullback c (specMap R A),
            (𝒱.pullback c A).U0 ⊓ (𝒱.pullback c A).U1) from t)) happ
end JacobianVarieties.Picard.Proofs.S_AlgebraicGeometry_RelPicard_map01_oneAddEpsMul
end ProofImplementation
