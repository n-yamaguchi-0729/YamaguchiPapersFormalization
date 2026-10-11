/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_RelEffCartierDiv_isInvertible_I_of_supportedIn.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.AlgebraicGeometry.Restrict
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.CategoryTheory.Iso
import Mathlib.CategoryTheory.MorphismProperty.Basic
import Mathlib.CategoryTheory.MorphismProperty.Limits
import AlgebraicCurves.RelativeDivisors.RelEffCartierDivOfPoint
import AlgebraicCurves.RelativeDivisors.Cartier
import AlgebraicCurves.RelativeDivisors.RelEffCartierDivSupportedIn
import AlgebraicCurves.RelativeDivisors.RelEffCartierDivRestrict
import AlgebraicCurves.RelativeDivisors.RelEffCartierDiv_isInvertible_I
import AlgebraicCurves.Geometry.Sheaves.Scheme_IdealSheafData_IsInvertible_of_comap_of_support_subset_range

/-!
# Rel Eff Cartier Div is Invertible I of supported In
-/

section ProofImplementation

namespace AlgebraicCurves.RelativeDivisors.Proofs.RelEffCartierDiv_isInvertible_I_of_supportedIn
attribute [-instance] AlgebraicGeometry.RelEffCartierDiv.isIso_subschemeIota_snd_of_degree_one
  AlgebraicGeometry.isIso_ker_graphOver_subschemeIota_snd
  AlgebraicGeometry.isClosedImmersion_graphOver
attribute [-simp] AlgebraicGeometry.graphOver_fst_assoc
  AlgebraicGeometry.RelEffCartierDiv.toPoint_comp
  AlgebraicGeometry.RelEffCartierDiv.toPoint_comp_assoc AlgebraicGeometry.graphOver_fst
  AlgebraicGeometry.RelEffCartierDiv.ofPoint_I AlgebraicGeometry.graphOver_snd
  AlgebraicGeometry.graphOver_snd_assoc

universe u

namespace DInvSupported

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem isIso_top_ι (S : Scheme.{u}) : IsIso (⊤ : S.Opens).ι := by
  change IsIso S.topIso.hom
  infer_instance

theorem main
    {𝒞 S : Scheme.{u}} {f : 𝒞 ⟶ S} [IsSeparated f] (U : 𝒞.Opens) [SmoothOfRelativeDimension 1 (U.ι
      ≫ f)]
    {r : ℕ} {T : Scheme.{u}} {g : T ⟶ S} (D : RelEffCartierDiv f r g) (hD : D.SupportedIn U) :
    D.I.IsInvertible := by
  have := isIso_top_ι S
  let gV : T ⟶ (⊤ : S.Opens) := g ≫ inv (⊤ : S.Opens).ι
  have hg : gV ≫ (⊤ : S.Opens).ι = g := by simp [gV]
  have hUV : U ≤ f ⁻¹ᵁ (⊤ : S.Opens) := le_top
  have hres : f.resLE ⊤ U hUV ≫ (⊤ : S.Opens).ι = U.ι ≫ f := Scheme.Hom.resLE_comp_ι f hUV
  have : MorphismProperty.RespectsIso (@SmoothOfRelativeDimension.{u} 1) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have : SmoothOfRelativeDimension 1 (f.resLE ⊤ U hUV) := by
    rw [← MorphismProperty.cancel_right_of_respectsIso (@SmoothOfRelativeDimension 1) _ (⊤ :
      S.Opens).ι, hres]
    infer_instance
  have : IsSeparated (f.resLE ⊤ U hUV) := by
    rw [← MorphismProperty.cancel_right_of_respectsIso (@IsSeparated) _ (⊤ : S.Opens).ι, hres]
    infer_instance
  let D' := RelEffCartierDiv.restrictAlong f r ⊤ U hUV gV g hg D hD
  have hD' : (D.I.comap (RelEffCartierDiv.resProdMap f ⊤ U hUV gV g hg)).IsInvertible :=
    RelEffCartierDiv.isInvertible_I D'
  refine Scheme.IdealSheafData.IsInvertible.of_comap_of_support_subset_range
    (RelEffCartierDiv.resProdMap f ⊤ U hUV gV g hg) D.I ?_ hD'
  rw [RelEffCartierDiv.range_resProdMap]
  exact hD

end DInvSupported

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry in
theorem _root_.AlgebraicGeometry.RelEffCartierDiv.isInvertible_I_of_supportedIn
    {𝒞 S : Scheme.{u}} {f : 𝒞 ⟶ S} [IsSeparated f] (U : 𝒞.Opens) [SmoothOfRelativeDimension 1 (U.ι
      ≫ f)]
    {r : ℕ} {T : Scheme.{u}} {g : T ⟶ S} (D : RelEffCartierDiv f r g) (hD : D.SupportedIn U) :
    D.I.IsInvertible :=
  DInvSupported.main U D hD
end AlgebraicCurves.RelativeDivisors.Proofs.RelEffCartierDiv_isInvertible_I_of_supportedIn
end ProofImplementation

attribute [-instance] AlgebraicGeometry.RelEffCartierDiv.isClosedImmersion_subschemeι_resProdMap
  AlgebraicGeometry.RelEffCartierDiv.isOpenImmersion_resProdMap
  AlgebraicGeometry.RelEffCartierDiv.isIso_subschemeIota_snd_of_degree_one
  AlgebraicGeometry.isIso_ker_graphOver_subschemeIota_snd
  AlgebraicGeometry.isClosedImmersion_graphOver
attribute [-simp] AlgebraicGeometry.RelEffCartierDiv.restrictAlong_extendAlong
  AlgebraicGeometry.RelEffCartierDiv.extendAlong_I
  AlgebraicGeometry.RelEffCartierDiv.resProdMap_snd
  AlgebraicGeometry.RelEffCartierDiv.restrictAlong_I
  AlgebraicGeometry.RelEffCartierDiv.extendAlong_restrictAlong
  AlgebraicGeometry.RelEffCartierDiv.resProdMap_fst_assoc
  AlgebraicGeometry.RelEffCartierDiv.resProdMap_snd_assoc
  AlgebraicGeometry.RelEffCartierDiv.resProdMap_fst AlgebraicGeometry.graphOver_fst_assoc
  AlgebraicGeometry.RelEffCartierDiv.toPoint_comp
  AlgebraicGeometry.RelEffCartierDiv.toPoint_comp_assoc AlgebraicGeometry.graphOver_fst
  AlgebraicGeometry.RelEffCartierDiv.ofPoint_I AlgebraicGeometry.graphOver_snd
  AlgebraicGeometry.graphOver_snd_assoc
