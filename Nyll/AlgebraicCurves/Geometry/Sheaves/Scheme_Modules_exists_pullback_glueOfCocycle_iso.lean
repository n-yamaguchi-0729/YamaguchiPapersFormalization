/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_exists_pullback_glueOfCocycle_iso.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Nyll.SchemeTheory.Modules.TensorSections
import Nyll.AlgebraicCurves.Geometry.Sheaves.ModulesGlueOfCocycle
import Nyll.AlgebraicCurves.Geometry.Picard.Functor
import Nyll.SchemeTheory.Modules.PullbackLocalSection
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_exists_iso_glueOfCocycle_app_eq_glueFrame
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_IsFrameOn_pullbackLocalSection

/-!
# Scheme Modules exists pullback glue Of Cocycle iso
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Sheaves.Proofs.Scheme_Modules_exists_pullback_glueOfCocycle_iso
open _root_.PresheafOfModules.PullbackMonoidal in
attribute [-instance]
  SheafOfModules.isIso_ihomModelToIhom
  pullback_monoidal
  isIso_δ
  PresheafOfModules.pushforward_laxMonoidal
  isIso_η
  PresheafOfModules.free_monoidal
  PresheafOfModules.restrictScalars_laxMonoidal
  isIso_δ_gS
  PresheafOfModules.pullback_oplaxMonoidal
  instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb
  PresheafOfModules.pullback_monoidal'
  AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap
  AlgebraicGeometry.Scheme.Modules.pullback_monoidal
  AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization'
  AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap
  AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal
  AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap
  AlgebraicGeometry.Scheme.Modules.sheafifyPullback_lifting
attribute [-simp] PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom
  SheafOfModules.ihomSectionsEquivFamily_unit
  AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app
  AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right
  AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left
  AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply
  SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app
  AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply
  AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply
  AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply
  AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply
  PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app


open _root_.CategoryTheory
open _root_.Opposite
open _root_.TopologicalSpace
open _root_.CategoryTheory.MonoidalCategory
open _root_.AlgebraicGeometry


universe u

open AlgebraicGeometry.Scheme.Modules in
theorem _root_.AlgebraicGeometry.Scheme.Modules.exists_pullback_glueOfCocycle_iso
    {X X' : Scheme.{u}} (g : X' ⟶ X) {ι : Type u} {U : ι → X.Opens} (hU : ⨆ i, U i = ⊤)
    (c : Scheme.Modules.UnitCocycle U) :
    ∃ φ : (Scheme.Modules.pullback g).obj (Scheme.Modules.glueOfCocycle c) ≅
      Scheme.Modules.glueOfCocycle (c.comap g),
      ∀ i, φ.hom.app (g ⁻¹ᵁ U i) (Scheme.Modules.pullbackLocalSection g (Scheme.Modules.glueFrame c
        i)) =
        Scheme.Modules.glueFrame (c.comap g) i := by
  have hU' : ⨆ i, g ⁻¹ᵁ U i = ⊤ := by
    rw [← Scheme.Hom.preimage_iSup, hU]
    rfl
  let e : ∀ i, Γ((Scheme.Modules.pullback g).obj (glueOfCocycle c), g ⁻¹ᵁ U i) :=
    fun i => pullbackLocalSection g (glueFrame c i)
  have he : ∀ i, IsFrameOn (e i) (g ⁻¹ᵁ U i) := fun i => (isFrameOn_glueFrame c
    i).pullbackLocalSection g
  have htrans : ∀ i j,
      ((Scheme.Modules.pullback g).obj (glueOfCocycle c)).presheaf.map
          (homOfLE (inf_le_right : g ⁻¹ᵁ U i ⊓ g ⁻¹ᵁ U j ≤ g ⁻¹ᵁ U j)).op (e j) =
        (c.comap g).u i j •
          ((Scheme.Modules.pullback g).obj (glueOfCocycle c)).presheaf.map
            (homOfLE (inf_le_left : g ⁻¹ᵁ U i ⊓ g ⁻¹ᵁ U j ≤ g ⁻¹ᵁ U i)).op (e i) := by
    intro i j
    have h1 : ((Scheme.Modules.pullback g).obj (glueOfCocycle c)).presheaf.map
        (homOfLE (inf_le_right : g ⁻¹ᵁ U i ⊓ g ⁻¹ᵁ U j ≤ g ⁻¹ᵁ U j)).op (e j) =
        pullbackLocalSection g ((glueOfCocycle c).presheaf.map (homOfLE (inf_le_right : U i ⊓ U j ≤
          U j)).op
          (glueFrame c j)) :=
      map_homOfLE_pullbackLocalSection g (inf_le_right : U i ⊓ U j ≤ U j) (glueFrame c j)
    have h2 : ((Scheme.Modules.pullback g).obj (glueOfCocycle c)).presheaf.map
        (homOfLE (inf_le_left : g ⁻¹ᵁ U i ⊓ g ⁻¹ᵁ U j ≤ g ⁻¹ᵁ U i)).op (e i) =
        pullbackLocalSection g ((glueOfCocycle c).presheaf.map (homOfLE (inf_le_left : U i ⊓ U j ≤
          U i)).op
          (glueFrame c i)) :=
      map_homOfLE_pullbackLocalSection g (inf_le_left : U i ⊓ U j ≤ U i) (glueFrame c i)
    rw [h1, h2, map_glueFrame_eq_smul c i j, pullbackLocalSection_smul]
    rfl
  obtain ⟨φ, hφ⟩ := exists_iso_glueOfCocycle_app_eq_glueFrame hU' (c.comap g) e he htrans
  exact ⟨φ, hφ⟩
end AlgebraicCurves.Geometry.Sheaves.Proofs.Scheme_Modules_exists_pullback_glueOfCocycle_iso
end ProofImplementation

open _root_.PresheafOfModules.PullbackMonoidal in
attribute [-instance]
  AlgebraicGeometry.Scheme.Hom.opensMapFinal
  AlgebraicGeometry.RelPicard.RigidifiedLineBundle.setoid
  AlgebraicGeometry.RelPicard.RigidifiedLineBundle.instInhabited
  SheafOfModules.isIso_ihomModelToIhom
  pullback_monoidal
  isIso_δ
  PresheafOfModules.pushforward_laxMonoidal
  isIso_η
  PresheafOfModules.free_monoidal
  PresheafOfModules.restrictScalars_laxMonoidal
  isIso_δ_gS
  PresheafOfModules.pullback_oplaxMonoidal
  instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb
  PresheafOfModules.pullback_monoidal'
  AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap
  AlgebraicGeometry.Scheme.Modules.pullback_monoidal
  AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization'
  AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap
  AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal
  AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap
  AlgebraicGeometry.Scheme.Modules.sheafifyPullback_lifting
attribute [-simp] AlgebraicGeometry.RelPicard.RigidifiedLineBundle.mk.sizeOf_spec
  AlgebraicGeometry.RelPicard.RigidifiedLineBundle.mk.injEq
  PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom
  SheafOfModules.ihomSectionsEquivFamily_unit
  AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app
  AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right
  AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left
  AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply
  SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app
  AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply
  AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply
  AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply
  AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply
  PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app
