/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Albanese.LineBundleSumInvariance
import Nyll.AlgebraicCurves.RelativeDivisors.ChangeBase
import Nyll.AlgebraicCurves.RelativeDivisors.RelEffCartierDivFunctor
import Nyll.AlgebraicCurves.Geometry.Sheaves.IdealSheafModule
import Nyll.AlgebraicCurves.Geometry.Curves.SmoothProperCurveBase
import Nyll.AlgebraicCurves.Geometry.AbelianSchemes.GroupLaw.BaseChange
import Nyll.AlgebraicCurves.Geometry.Schemes.SchemeHomOverBaseChange
import Mathlib.AlgebraicGeometry.Geometrically.Integral

/-!
# Line-bundle invariance of sums over arbitrary field-valued test maps

The curve, target group, universal divisor, and sum morphism are base changed
along the same actual field-valued test map. The actual divisor equivalence
and its inverse-ideal-module comparison transport the line bundles.
Line-bundle invariance over the extended field then descends by projection
from the actual target pullback.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open NeronModelInfra GoodReductionJacobian

namespace JacobianVarieties.Albanese

/-- The sum morphism has the same value on linearly equivalent effective
divisors over any field-valued test map into the ground field. -/
theorem lift_comp_eq_of_lineBundle_iso_of_fieldMap
    {K : Type u} [Field K] {C B Y : Scheme.{u}}
    (c : C ⟶ Spec (CommRingCat.of K)) [IsProper c]
    [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    {r : ℕ} {y : Y ⟶ Spec (CommRingCat.of K)}
    {U : RelEffCartierDiv c r y} (hU : U.IsUniversal)
    {b : B ⟶ Spec (CommRingCat.of K)} [Smooth b] [IsProper b]
    [GeometricallyIntegral b] (G : RelativeGroupLaw K b) (sum : SchemeHomOver y b)
    (L : Type u) [Field L] (s : Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of K))
    (D₀ D₁ : RelEffCartierDiv c r s) (e : D₀.lineBundle ≅ D₁.lineBundle) :
    hU.lift D₀ ≫ sum.1 = hU.lift D₁ ≫ sum.1 := by
  have h : ∀ (E₀ E₁ : RelEffCartierDiv c r (𝟙 (Spec (CommRingCat.of L)) ≫ s)),
      (E₀.lineBundle ≅ E₁.lineBundle) →
      hU.lift E₀ ≫ sum.1 = hU.lift E₁ ≫ sum.1 := by
    intro E₀ E₁ eE
    let cL : pullback c s ⟶ Spec (CommRingCat.of L) := pullback.snd c s
    let bL : pullback b s ⟶ Spec (CommRingCat.of L) := pullback.snd b s
    let yL : pullback y s ⟶ Spec (CommRingCat.of L) := pullback.snd y s
    let E₀L : RelEffCartierDiv cL r (𝟙 (Spec (CommRingCat.of L))) :=
      (RelEffCartierDiv.changeBaseEquiv c s (𝟙 _) r).symm E₀
    let E₁L : RelEffCartierDiv cL r (𝟙 (Spec (CommRingCat.of L))) :=
      (RelEffCartierDiv.changeBaseEquiv c s (𝟙 _) r).symm E₁
    obtain ⟨e₀⟩ := RelEffCartierDiv.changeBaseEquiv_invModule_iso c s (𝟙 _) E₀
    obtain ⟨e₁⟩ := RelEffCartierDiv.changeBaseEquiv_invModule_iso c s (𝟙 _) E₁
    let eL : E₀L.lineBundle ≅ E₁L.lineBundle :=
      e₀.symm ≪≫
        (Scheme.Modules.pullback (pullbackLeftPullbackSndIso c s (𝟙 _)).hom).mapIso eE ≪≫ e₁
    let groupL : RelativeGroupLaw L bL := G.baseChange s
    let sumL : SchemeHomOver yL bL := fibreRestrictAlong s b y sum
    have hsumL : sumL.1 ≫ pullback.fst b s = pullback.fst y s ≫ sum.1 :=
      fibreRestrictAlong_coe_comp_fst s b y sum
    have hL : (hU.changeBase s).lift E₀L ≫ sumL.1 =
        (hU.changeBase s).lift E₁L ≫ sumL.1 :=
      lift_comp_eq_of_lineBundle_iso cL (hU.changeBase s) groupL sumL E₀L E₁L eL
    have hproj := congrArg (fun a : Spec (CommRingCat.of L) ⟶ pullback b s =>
      a ≫ pullback.fst b s) hL
    rw [Category.assoc, Category.assoc, hsumL, ← Category.assoc, ← Category.assoc,
      hU.changeBase_lift_fst s E₀L, hU.changeBase_lift_fst s E₁L] at hproj
    have h₀ : RelEffCartierDiv.changeBaseEquiv c s (𝟙 _) r E₀L = E₀ :=
      (RelEffCartierDiv.changeBaseEquiv c s (𝟙 _) r).apply_symm_apply E₀
    have h₁ : RelEffCartierDiv.changeBaseEquiv c s (𝟙 _) r E₁L = E₁ :=
      (RelEffCartierDiv.changeBaseEquiv c s (𝟙 _) r).apply_symm_apply E₁
    rw [h₀, h₁] at hproj
    exact hproj
  have h' : ∀ (E₀ E₁ : RelEffCartierDiv c r s), (E₀.lineBundle ≅ E₁.lineBundle) →
      hU.lift E₀ ≫ sum.1 = hU.lift E₁ ≫ sum.1 :=
    Eq.mp (congrArg (fun t : Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of K) =>
      ∀ (E₀ E₁ : RelEffCartierDiv c r t), (E₀.lineBundle ≅ E₁.lineBundle) →
        hU.lift E₀ ≫ sum.1 = hU.lift E₁ ≫ sum.1) (Category.id_comp s)) h
  exact h' D₀ D₁ e

end JacobianVarieties.Albanese
