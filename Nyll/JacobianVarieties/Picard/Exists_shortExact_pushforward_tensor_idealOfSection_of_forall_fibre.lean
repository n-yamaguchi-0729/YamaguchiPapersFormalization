/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_RelPicard_exists_shortExact_pushforward_tensor_idealOfSection_of_forall_fibre.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Geometry.Picard.Functor
import Nyll.AlgebraicCurves.Geometry.Picard.AlgEquivZeroCut
import Nyll.AlgebraicCurves.Cohomology.Cech.TwoChartCechSectionsOf
import Nyll.AlgebraicCurves.Geometry.Curves.SmoothProperCurveFiniteMapData
import Nyll.AlgebraicCurves.Geometry.Sheaves.ModulesLocallyFreeOfRank
import Nyll.AlgebraicCurves.Geometry.Sheaves.ModulesDet
import Nyll.AlgebraicCurves.Geometry.Sheaves.IdealSheafModule
import Nyll.SchemeTheory.Modules.Monoidal
import Nyll.JacobianVarieties.Picard.ThetaBundle
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_shortExact_map_pushforward_of_forall_exists_surjective_app
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_surjective_app_sup_of_shortExact_of_locallyTrivial
import Nyll.AlgebraicCurves.Geometry.Schemes.Scheme_TwoAffineOpenCover_subsingleton_H1_sectionsOf_of_forall_field
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_exists_shortExact_ker_module_tensor_of_isClosedImmersion
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_isLocallyFreeOfRank_one_iff_isInvertible
import Nyll.AlgebraicCurves.Geometry.Schemes.Scheme_Hom_isInvertible_ker_of_comp_eq_id
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_IdealSheafData_IsInvertible_isInvertible_module
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_IsInvertible_tensor
import Nyll.AlgebraicCurves.Geometry.Schemes.Scheme_TwoAffineOpenCover_exists_isPullback_snd_specMap_algebraOfHom
import Nyll.AlgebraicCurves.Geometry.Schemes.Scheme_TwoAffineOpenCover_finiteType_algebraOfHom
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_exists_iso_pullback_of_isPullback
import Nyll.AlgebraicCurves.Geometry.Schemes.Scheme_TwoAffineOpenCover_exists_linearEquiv_sectionsOf_of_iso
import Nyll.AlgebraicCurves.Geometry.Curves.SmoothProperCurve_FiniteMapData_exists_baseChange
import Nyll.AlgebraicCurves.Geometry.Curves.SmoothProperCurve_FiniteMapData_finite_H0_H1_sectionsOf
import Nyll.SchemeTheory.Modules.OpenImmersionUnit

/-!
Construct the short exact pushforward sequence associated to an ideal of a section, using
fibre cohomology vanishing.
-/

section ProofImplementation

namespace JacobianVarieties.Picard.Proofs.SectionPushforwardExact
attribute [-instance]
  AlgebraicGeometry.OModulePresheaf.isScalarTower
  AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder
  AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype
  AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx
  AlgebraicGeometry.OModulePresheaf.addCommGroup
  AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx
  AlgebraicGeometry.OModulePresheaf.moduleSections
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx
  AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap
  AlgebraicGeometry.Scheme.Modules.pullback_monoidal
  AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization'
  AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap
  AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal
  AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap
  AlgebraicGeometry.Scheme.Modules.sheafifyPullback_lifting
  PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ
  PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η
  PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal
  PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal
open _root_.PresheafOfModules.PullbackMonoidal in
attribute [-instance]
  instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb
attribute [-instance]
  PresheafOfModules.pullback_monoidal' SheafOfModules.isIso_ihomModelToIhom
attribute [-simp]
  AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq
  AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec
  AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec
  AlgebraicGeometry.OModulePresheaf.mk.injEq
  AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right
  AlgebraicGeometry.Scheme.Modules.map_unitSection
  AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply
  AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero
  AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left
  AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ
  AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq
  AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U
  AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app
  AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply
  AlgebraicGeometry.OModulePresheaf.AffHom.comp_app
  AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec
  AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe
  AlgebraicGeometry.OModulePresheaf.AffHom.id_app
  AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec
  AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app
  AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec
  AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec
  AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq
  AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq
  AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply
  AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq
  AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app PresheafOfModules.freeεIso_hom_app
  PresheafOfModules.freeμIso_hom_app AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg
  AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero
  AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub
  AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add
  PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom
  SheafOfModules.ihomSectionsEquivFamily_unit
attribute [-simp]
  AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app
  AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right
  AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left
  AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily
  AlgebraicGeometry.Scheme.Modules.familyOfHom_app
  AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply
  AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply
  AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply
  AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply

universe u

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry
open _root_.AlgebraicGeometry.RelPicard
open _root_.NeronModelInfra
open _root_.CategoryTheory.MonoidalCategory
open _root_.AlgebraicGeometry.SmoothProperCurve
open _root_.Opposite
open _root_.TopologicalSpace

noncomputable section

namespace AlgebraicGeometry
open _root_.AlgebraicGeometry
namespace Scheme
open _root_.AlgebraicGeometry.Scheme
namespace Modules
open _root_.AlgebraicGeometry.Scheme.Modules
namespace PointSES
open _root_.AlgebraicGeometry.Scheme.Modules
open _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry

variable {X : Scheme.{u}}

theorem app_naturality {M N : X.Modules} (φ : M ⟶ N) {U V : X.Opens} (i : U ⟶ V) (m : Γ(M, V)) :
    N.presheaf.map i.op (φ.app V m) = φ.app U (M.presheaf.map i.op m) := by
  have h := PresheafOfModules.Hom.naturality φ.val i.op
  have h' := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom h) m
  simp only [ModuleCat.hom_comp, LinearMap.coe_comp] at h'
  exact h'.symm

theorem comp_app_apply {M N P : X.Modules} (φ : M ⟶ N) (ψ : N ⟶ P) (U : X.Opens) (m : Γ(M, U)) :
    (φ ≫ ψ).app U m = ψ.app U (φ.app U m) := rfl

theorem id_app_apply {M : X.Modules} (U : X.Opens) (m : Γ(M, U)) : (𝟙 M : M ⟶ M).app U m = m := rfl

/-- Restriction of sections of a sheaf of modules along an inclusion of open sets. -/
noncomputable abbrev rM (M : X.Modules) {V W : X.Opens} (h : V ≤ W) : Γ(M, W) → Γ(M, V) :=
  fun y => M.presheaf.map (homOfLE h).op y

theorem rM_rM (M : X.Modules) {V₁ V₂ V₃ : X.Opens} (h₂₁ : V₂ ≤ V₁) (h₃₂ : V₃ ≤ V₂) (y : Γ(M, V₁)) :
    rM M h₃₂ (rM M h₂₁ y) = rM M (h₃₂.trans h₂₁) y := by
  change (M.presheaf.map (homOfLE h₂₁).op ≫ M.presheaf.map (homOfLE h₃₂).op) y = _
  rw [← Functor.map_comp]; rfl

theorem rM_app {M N : X.Modules} (φ : M ⟶ N) {V W : X.Opens} (h : V ≤ W) (m : Γ(M, W)) :
    rM N h (φ.app W m) = φ.app V (rM M h m) :=
  app_naturality φ (homOfLE h) m

theorem rM_sub (M : X.Modules) {V W : X.Opens} (h : V ≤ W) (y z : Γ(M, W)) :
    rM M h (y - z) = rM M h y - rM M h z := map_sub _ _ _

theorem rM_neg (M : X.Modules) {V W : X.Opens} (h : V ≤ W) (y : Γ(M, W)) :
    rM M h (-y) = -rM M h y := map_neg _ _

theorem rM_refl (M : X.Modules) (V : X.Opens) (y : Γ(M, V)) : rM M (le_refl V) y = y := by
  change (M.presheaf.map (homOfLE (le_refl V)).op) y = y
  have hid : M.presheaf.map (homOfLE (le_refl V)).op = 𝟙 _ := by
    rw [show (homOfLE (le_refl V)).op = 𝟙 (op V) from Subsingleton.elim _ _]
    exact CategoryTheory.Functor.map_id _ _
  rw [hid]
  rfl

theorem rM_injective_of_eq (M : X.Modules) {V W : X.Opens} (h : V = W) :
    Function.Injective (rM M h.le) := by
  intro y z hyz
  have := congrArg (rM M h.ge) hyz
  rwa [rM_rM, rM_rM, rM_refl, rM_refl] at this

theorem hH1_of_iso {M N : X.Modules} (e : M ≅ N) (W₀ W₁ : X.Opens)
    (h : ∀ δ : Γ(N, W₀ ⊓ W₁), ∃ (a : Γ(N, W₀)) (b : Γ(N, W₁)),
      δ = rM N inf_le_left a - rM N inf_le_right b) :
    ∀ δ : Γ(M, W₀ ⊓ W₁), ∃ (a : Γ(M, W₀)) (b : Γ(M, W₁)),
      δ = M.presheaf.map (homOfLE inf_le_left).op a -
        M.presheaf.map (homOfLE inf_le_right).op b := by
  intro δ
  obtain ⟨a, b, hab⟩ := h (e.hom.app _ δ)
  refine ⟨e.inv.app _ a, e.inv.app _ b, ?_⟩
  have hδ : δ = e.inv.app _ (e.hom.app _ δ) := by
    rw [← comp_app_apply, e.hom_inv_id, id_app_apply]
  change δ = rM M inf_le_left (e.inv.app _ a) - rM M inf_le_right (e.inv.app _ b)
  rw [hδ, hab, map_sub, rM_app, rM_app]

section OpenImm

variable {X' : Scheme.{u}} (j : X' ⟶ X) [IsOpenImmersion j] (N : X.Modules)

/-- The unit of the pullback--pushforward adjunction along the open immersion. -/
noncomputable abbrev η :
    N ⟶ (Scheme.Modules.pushforward j).obj ((Scheme.Modules.pullback j).obj N) :=
  (Scheme.Modules.pullbackPushforwardAdjunction j).unit.app N

/-- Pull a section back along the open immersion using the adjunction unit. -/
noncomputable abbrev pull (V : X.Opens) (m : Γ(N, V)) :
    Γ((Scheme.Modules.pullback j).obj N, j ⁻¹ᵁ V) :=
  (η j N).app V m

omit [IsOpenImmersion j] in
theorem pull_sub (V : X.Opens) (m m' : Γ(N, V)) :
    pull j N V (m - m') = pull j N V m - pull j N V m' :=
  map_sub _ _ _

omit [IsOpenImmersion j] in
theorem pull_neg (V : X.Opens) (m : Γ(N, V)) : pull j N V (-m) = -pull j N V m := map_neg _ _

omit [IsOpenImmersion j] in
theorem map_pull {U V : X.Opens} (h : U ≤ V) (m : Γ(N, V)) :
    rM ((Scheme.Modules.pullback j).obj N) (show j ⁻¹ᵁ U ≤ j ⁻¹ᵁ V from fun _ hx => h hx) (pull j N
      V m)
      = pull j N U (rM N h m) := by
  rw [pull, pull, ← app_naturality (η j N) (homOfLE h) m]
  rfl

theorem pull_bijective (V : X.Opens) (hV : V ≤ j.opensRange) : Function.Bijective (pull j N V) :=
  Scheme.Modules.bijective_unit_app_of_le_opensRange j N V hV

theorem hH1_of_pullback (𝒲 : X'.TwoAffineOpenCover) {A : Type u} [CommRing A]
    (x' : X' ⟶ Spec (.of A))
    (hH1 : Subsingleton (𝒲.sectionsOf x' ((Scheme.Modules.pullback j).obj N)).H1) :
    ∀ δ : Γ(N, j ''ᵁ 𝒲.U0 ⊓ j ''ᵁ 𝒲.U1), ∃ (a : Γ(N, j ''ᵁ 𝒲.U0)) (b : Γ(N, j ''ᵁ 𝒲.U1)),
      δ = rM N inf_le_left a - rM N inf_le_right b := by
  have h0 : j ⁻¹ᵁ (j ''ᵁ 𝒲.U0) = 𝒲.U0 := j.preimage_image_eq _
  have h1 : j ⁻¹ᵁ (j ''ᵁ 𝒲.U1) = 𝒲.U1 := j.preimage_image_eq _
  have h01 : j ⁻¹ᵁ (j ''ᵁ 𝒲.U0 ⊓ j ''ᵁ 𝒲.U1) = 𝒲.U0 ⊓ 𝒲.U1 := by
    rw [Scheme.Hom.preimage_inf, h0, h1]
  have hW₀ : j ''ᵁ 𝒲.U0 ≤ j.opensRange := j.image_le_opensRange _
  have hW₁ : j ''ᵁ 𝒲.U1 ≤ j.opensRange := j.image_le_opensRange _
  intro δ
  have hz : (Submodule.Quotient.mk (rM ((Scheme.Modules.pullback j).obj N) h01.ge (pull j N _ δ)) :
      (𝒲.sectionsOf x' ((Scheme.Modules.pullback j).obj N)).H1) = 0 := Subsingleton.elim _ _
  have hzmem : rM ((Scheme.Modules.pullback j).obj N) h01.ge (pull j N _ δ) ∈
      LinearMap.range (𝒲.sectionsOf x' ((Scheme.Modules.pullback j).obj N)).cechDiff :=
    (Submodule.Quotient.mk_eq_zero (R := A)
      (M := (𝒲.sectionsOf x' ((Scheme.Modules.pullback j).obj N)).M01)
      (LinearMap.range (𝒲.sectionsOf x' ((Scheme.Modules.pullback j).obj N)).cechDiff)).mp hz
  obtain ⟨⟨s0, s1⟩, hs⟩ := hzmem
  rw [TwoChartCech.Sections.cechDiff_apply] at hs
  change rM ((Scheme.Modules.pullback j).obj N) inf_le_right s1 - rM ((Scheme.Modules.pullback
    j).obj N) inf_le_left s0
    = rM ((Scheme.Modules.pullback j).obj N) h01.ge (pull j N _ δ) at hs
  obtain ⟨a, ha⟩ := (pull_bijective j N _ hW₀).2 (rM ((Scheme.Modules.pullback j).obj N) h0.le s0)
  obtain ⟨b, hb⟩ := (pull_bijective j N _ hW₁).2 (rM ((Scheme.Modules.pullback j).obj N) h1.le s1)
  have hpa : pull j N _ (rM N (inf_le_left : j ''ᵁ 𝒲.U0 ⊓ j ''ᵁ 𝒲.U1 ≤ j ''ᵁ 𝒲.U0) a)
      = rM ((Scheme.Modules.pullback j).obj N)
          ((show j ⁻¹ᵁ (j ''ᵁ 𝒲.U0 ⊓ j ''ᵁ 𝒲.U1) ≤ j ⁻¹ᵁ (j ''ᵁ 𝒲.U0) from fun _ hx => hx.1).trans
            h0.le) s0 := by
    rw [← map_pull, ha]
    exact rM_rM ((Scheme.Modules.pullback j).obj N) h0.le
      (show j ⁻¹ᵁ (j ''ᵁ 𝒲.U0 ⊓ j ''ᵁ 𝒲.U1) ≤ j ⁻¹ᵁ (j ''ᵁ 𝒲.U0) from fun _ hx => hx.1) s0
  have hpb : pull j N _ (rM N (inf_le_right : j ''ᵁ 𝒲.U0 ⊓ j ''ᵁ 𝒲.U1 ≤ j ''ᵁ 𝒲.U1) b)
      = rM ((Scheme.Modules.pullback j).obj N)
          ((show j ⁻¹ᵁ (j ''ᵁ 𝒲.U0 ⊓ j ''ᵁ 𝒲.U1) ≤ j ⁻¹ᵁ (j ''ᵁ 𝒲.U1) from fun _ hx => hx.2).trans
            h1.le) s1 := by
    rw [← map_pull, hb]
    exact rM_rM ((Scheme.Modules.pullback j).obj N) h1.le
      (show j ⁻¹ᵁ (j ''ᵁ 𝒲.U0 ⊓ j ''ᵁ 𝒲.U1) ≤ j ⁻¹ᵁ (j ''ᵁ 𝒲.U1) from fun _ hx => hx.2) s1
  refine ⟨-a, -b, ?_⟩
  apply (pull_bijective j N _ (inf_le_left.trans hW₀)).1
  apply rM_injective_of_eq ((Scheme.Modules.pullback j).obj N) h01.symm
  rw [rM_neg N, rM_neg N, pull_sub, pull_neg, pull_neg, hpa, hpb, rM_sub, rM_neg, rM_neg]
  rw [rM_rM ((Scheme.Modules.pullback j).obj N)
      ((show j ⁻¹ᵁ (j ''ᵁ 𝒲.U0 ⊓ j ''ᵁ 𝒲.U1) ≤ j ⁻¹ᵁ (j ''ᵁ 𝒲.U0) from fun _ hx => hx.1).trans
        h0.le)
      h01.ge s0,
    rM_rM ((Scheme.Modules.pullback j).obj N)
      ((show j ⁻¹ᵁ (j ''ᵁ 𝒲.U0 ⊓ j ''ᵁ 𝒲.U1) ≤ j ⁻¹ᵁ (j ''ᵁ 𝒲.U1) from fun _ hx => hx.2).trans
        h1.le)
      h01.ge s1]
  rw [← hs]
  abel

end OpenImm

theorem opensRange_eq_preimage {X T X' W' : Scheme.{u}} (π : X ⟶ T) (π' : X' ⟶ W') (g' : X' ⟶ X)
    (j : W' ⟶ T)
    [IsOpenImmersion j] [IsOpenImmersion g'] (hcart : IsPullback g' π' π j) :
    g'.opensRange = π ⁻¹ᵁ j.opensRange := by
  apply le_antisymm
  · intro x hx
    obtain ⟨x', rfl⟩ := Scheme.Hom.mem_opensRange.mp hx
    change π.base (g'.base x') ∈ j.opensRange
    rw [Scheme.Hom.mem_opensRange]
    refine ⟨π'.base x', ?_⟩
    change (π' ≫ j).base x' = (g' ≫ π).base x'
    rw [hcart.w]
  · intro x hx
    change π.base x ∈ j.opensRange at hx
    obtain ⟨y, hy⟩ := Scheme.Hom.mem_opensRange.mp hx
    obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback x y hy.symm
    refine Scheme.Hom.mem_opensRange.mpr ⟨hcart.isoPullback.inv.base z, ?_⟩
    change (hcart.isoPullback.inv ≫ g').base z = x
    rw [hcart.isoPullback_inv_fst]
    exact hz

end AlgebraicGeometry.Scheme.Modules.PointSES

namespace AlgebraicGeometry
open _root_.AlgebraicGeometry
namespace RelPicard
open _root_.AlgebraicGeometry.RelPicard
namespace PointSES
open _root_.AlgebraicGeometry.RelPicard
open _root_.AlgebraicGeometry

open AlgebraicGeometry.Scheme.Modules.PointSES

theorem surjective_app_preimage
    (R : Type u) [CommRing R] [IsNoetherianRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of
      R))
    [IsProper c] [SmoothOfRelativeDimension 1 c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (h𝔉 : ∀ m₀ : ℕ, ∃ 𝔉 : SmoothProperCurve.FiniteMapData c ε, m₀ ≤ 𝔉.m)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType t]
    (L : (pullback c t).Modules) (hL : Scheme.Modules.IsInvertible L)
    (hfib : ∀ (k : Type u) [Field k] (s : Spec (CommRingCat.of k) ⟶ T)
      (𝒲 : (pullback (pullback.snd c t) s).TwoAffineOpenCover),
      Subsingleton (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s L)).H1)
    (S₀ : ShortComplex (pullback c t).Modules) (hS₀ : S₀.ShortExact) (e₁ : S₀.X₁ ≅ L)
    (W : T.Opens) (hW : IsAffineOpen W) :
    Function.Surjective (S₀.g.app ((pullback.snd c t) ⁻¹ᵁ W)) := by
  have htriv₁ : ∀ x : ↥(pullback c t), ∃ V : (pullback c t).Opens, x ∈ V ∧
      Nonempty ((Scheme.Modules.pullback V.ι).obj S₀.X₁ ≅ SheafOfModules.unit
        V.toScheme.ringCatSheaf) := by
    intro x
    obtain ⟨V, hx, ⟨e⟩⟩ := hL.exists_trivialization x
    exact ⟨V, hx, ⟨(Scheme.Modules.pullback V.ι).mapIso e₁ ≪≫ e⟩⟩
  let := Scheme.TwoAffineOpenCover.algebraOfHom t W
  have : Algebra.FiniteType R Γ(T, W) := Scheme.TwoAffineOpenCover.finiteType_algebraOfHom t W hW
  have : IsNoetherianRing Γ(T, W) := Algebra.FiniteType.isNoetherianRing R _
  obtain ⟨g', hcart, -⟩ := Scheme.TwoAffineOpenCover.exists_isPullback_snd_specMap_algebraOfHom c t
    W hW
  have : IsOpenImmersion g' := MorphismProperty.of_isPullback (P := @IsOpenImmersion) hcart.flip
    inferInstance
  obtain ⟨𝔉, -⟩ := h𝔉 0
  obtain ⟨𝔉A, -, -, -, -⟩ := 𝔉.exists_baseChange Γ(T, W)
  have hG : Scheme.Modules.IsInvertible ((Scheme.Modules.pullback g').obj L) := hL.pullback g'
  have hfin := 𝔉A.finite_H0_H1_sectionsOf ((Scheme.Modules.pullback g').obj L)
    hG.exists_trivialization
  have hH1 : Subsingleton ((𝔉A.twoAffineOpenCover.sectionsOf
      (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R Γ(T, W)))
      ((Scheme.Modules.pullback g').obj L)).H1) := by
    refine Scheme.TwoAffineOpenCover.subsingleton_H1_sectionsOf_of_forall_field
      (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R Γ(T, W))) 𝔉A.twoAffineOpenCover _
      hG.exists_trivialization hfin.2 ?_
    intro K _ _
    obtain ⟨φ, hφ, -, hmod⟩ := Scheme.Modules.exists_iso_pullback_of_isPullback (pullback.snd c t)
      (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R Γ(T, W))) g' hW.fromSpec hcart
      (Scheme.TwoAffineOpenCover.specMap Γ(T, W) K)
    obtain ⟨𝒱, -, -, -, ⟨e1⟩⟩ := Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso
      (fibreAt c t (Scheme.TwoAffineOpenCover.specMap Γ(T, W) K ≫ hW.fromSpec))
      (fibreAt c (Scheme.TwoAffineOpenCover.specMap R Γ(T, W)) (Scheme.TwoAffineOpenCover.specMap
        Γ(T, W) K))
      φ hφ
      (𝔉A.twoAffineOpenCover.pullback (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R Γ(T,
        W))) K)
      (fibreModule c (Scheme.TwoAffineOpenCover.specMap R Γ(T, W))
        (Scheme.TwoAffineOpenCover.specMap Γ(T, W) K)
        ((Scheme.Modules.pullback g').obj L))
      (fibreModule c t (Scheme.TwoAffineOpenCover.specMap Γ(T, W) K ≫ hW.fromSpec) L) (hmod L).some
    have := hfib K (Scheme.TwoAffineOpenCover.specMap Γ(T, W) K ≫ hW.fromSpec) 𝒱
    exact e1.symm.toEquiv.subsingleton
  have hH1X := hH1_of_pullback g' L 𝔉A.twoAffineOpenCover _ hH1
  have hH1S := hH1_of_iso e₁ _ _ hH1X
  have hsup : g' ''ᵁ 𝔉A.twoAffineOpenCover.U0 ⊔
      g' ''ᵁ 𝔉A.twoAffineOpenCover.U1 = (pullback.snd c t) ⁻¹ᵁ W := by
    have h1 : g' ''ᵁ 𝔉A.twoAffineOpenCover.U0 ⊔ g' ''ᵁ 𝔉A.twoAffineOpenCover.U1
        = g' ''ᵁ (𝔉A.twoAffineOpenCover.U0 ⊔ 𝔉A.twoAffineOpenCover.U1) := by
      apply TopologicalSpace.Opens.ext
      exact (Set.image_union g'.base _ _).symm
    rw [h1, 𝔉A.twoAffineOpenCover.sup_eq_top, Scheme.Hom.image_top_eq_opensRange,
      opensRange_eq_preimage _ _ _ _ hcart, hW.opensRange_fromSpec]
  rw [← hsup]
  exact Scheme.Modules.surjective_app_sup_of_shortExact_of_locallyTrivial S₀ hS₀ htriv₁ _ _
    (𝔉A.twoAffineOpenCover.isAffineOpen_U0.image_of_isOpenImmersion g')
    (𝔉A.twoAffineOpenCover.isAffineOpen_U1.image_of_isOpenImmersion g') hH1S

theorem main
    (R : Type u) [CommRing R] [IsNoetherianRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of
      R))
    [IsProper c] [SmoothOfRelativeDimension 1 c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (h𝔉 : ∀ m₀ : ℕ, ∃ 𝔉 : SmoothProperCurve.FiniteMapData c ε, m₀ ≤ 𝔉.m)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType t]
    (p : T ⟶ pullback c t) (hp : p ≫ pullback.snd c t = 𝟙 T)
    (F : (pullback c t).Modules) (hF : Scheme.Modules.IsInvertible F) (n : ℕ)
    (hfib : ∀ (k : Type u) [Field k] (s : Spec (CommRingCat.of k) ⟶ T)
      (𝒲 : (pullback (pullback.snd c t) s).TwoAffineOpenCover),
      Subsingleton (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s (F ⊗ p.ker.module))).H1 ∧
        Module.finrank k (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s (F ⊗ p.ker.module))).H0 =
          n) :
    ∃ S : ShortComplex T.Modules, S.ShortExact ∧
      Nonempty (S.X₁ ≅ (Scheme.Modules.pushforward (pullback.snd c t)).obj (F ⊗ p.ker.module)) ∧
      Nonempty (S.X₂ ≅ (Scheme.Modules.pushforward (pullback.snd c t)).obj F) ∧
      Nonempty (S.X₃ ≅ (Scheme.Modules.pullback p).obj F) := by
  have : IsSeparated (pullback.snd c t) := inferInstance
  have hstable : MorphismProperty.IsStableUnderBaseChange
      (fun {X Y : Scheme.{u}} (f : X ⟶ Y) => SmoothOfRelativeDimension 1 f) :=
    smoothOfRelativeDimension_isStableUnderBaseChange 1
  have : SmoothOfRelativeDimension 1 (pullback.snd c t) :=
    hstable.of_isPullback (IsPullback.of_hasPullback c t) inferInstance
  have : IsClosedImmersion p := by
    have : IsClosedImmersion (p ≫ pullback.snd c t) := by rw [hp]; infer_instance
    exact IsClosedImmersion.of_comp p (pullback.snd c t)
  have hI : Scheme.Modules.IsInvertible p.ker.module :=
    (Scheme.Hom.isInvertible_ker_of_comp_eq_id p hp).isInvertible_module
  have hFI : Scheme.Modules.IsInvertible (F ⊗ p.ker.module) := hF.tensor hI
  obtain ⟨S₀, hS₀, ⟨e₁⟩, ⟨e₂⟩, ⟨e₃⟩⟩ :=
    Scheme.Modules.exists_shortExact_ker_module_tensor_of_isClosedImmersion p F
    ((Scheme.Modules.isLocallyFreeOfRank_one_iff_isInvertible F).mpr hF)
  let e₁' : S₀.X₁ ≅ F ⊗ p.ker.module := e₁ ≪≫ β_ _ _
  refine ⟨S₀.map (Scheme.Modules.pushforward (pullback.snd c t)), ?_,
    ⟨(Scheme.Modules.pushforward (pullback.snd c t)).mapIso e₁'⟩,
    ⟨(Scheme.Modules.pushforward (pullback.snd c t)).mapIso e₂⟩,
    ⟨(Scheme.Modules.pushforward (pullback.snd c t)).mapIso e₃ ≪≫
      (Scheme.Modules.pushforwardComp p (pullback.snd c t)).app _ ≪≫
      (Scheme.Modules.pushforwardCongr hp).app _ ≪≫ (Scheme.Modules.pushforwardId T).app _⟩⟩
  refine Scheme.Modules.shortExact_map_pushforward_of_forall_exists_surjective_app _ S₀ hS₀ ?_
  intro U y hyU
  obtain ⟨W, hW, hyW, hWU⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp T.isBasis_affineOpens hyU
  exact ⟨W, hyW, hWU, surjective_app_preimage R c ε h𝔉 t (F ⊗ p.ker.module) hFI
    (fun k _ s 𝒲 => (hfib k s 𝒲).1) S₀ hS₀ e₁' W hW⟩

end AlgebraicGeometry.RelPicard.PointSES
end
end JacobianVarieties.Picard.Proofs.SectionPushforwardExact

namespace AlgebraicGeometry.RelPicard
noncomputable section

open _root_.JacobianVarieties.Picard.Proofs.SectionPushforwardExact
universe u
open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry
open _root_.AlgebraicGeometry.RelPicard
open _root_.NeronModelInfra
open _root_.CategoryTheory.MonoidalCategory
open _root_.AlgebraicGeometry.SmoothProperCurve
open _root_.Opposite
open _root_.TopologicalSpace

open _root_.JacobianVarieties.Picard.Proofs in
open SectionPushforwardExact.AlgebraicGeometry.RelPicard.PointSES in
theorem exists_shortExact_pushforward_tensor_idealOfSection_of_forall_fibre
    (R : Type u) [CommRing R] [IsNoetherianRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of
      R))
    [IsProper c] [SmoothOfRelativeDimension 1 c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (h𝔉 : ∀ m₀ : ℕ, ∃ 𝔉 : SmoothProperCurve.FiniteMapData c ε, m₀ ≤ 𝔉.m)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType t]
    (p : T ⟶ pullback c t) (hp : p ≫ pullback.snd c t = 𝟙 T)
    (F : (pullback c t).Modules) (hF : Scheme.Modules.IsInvertible F) (n : ℕ)
    (hfib : ∀ (k : Type u) [Field k] (s : Spec (CommRingCat.of k) ⟶ T)
      (𝒲 : (pullback (pullback.snd c t) s).TwoAffineOpenCover),
      Subsingleton (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s (F ⊗ p.ker.module))).H1 ∧
        Module.finrank k (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s (F ⊗ p.ker.module))).H0 =
          n) :
    ∃ S : ShortComplex T.Modules, S.ShortExact ∧
      Nonempty (S.X₁ ≅ (Scheme.Modules.pushforward (pullback.snd c t)).obj (F ⊗ p.ker.module)) ∧
      Nonempty (S.X₂ ≅ (Scheme.Modules.pushforward (pullback.snd c t)).obj F) ∧
      Nonempty (S.X₃ ≅ (Scheme.Modules.pullback p).obj F) :=
  main R c ε h𝔉 t p hp F hF n hfib

end
end AlgebraicGeometry.RelPicard
end ProofImplementation

attribute [-instance]
  AlgebraicGeometry.OModulePresheaf.isScalarTower
  AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder
  AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype
  AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx
  AlgebraicGeometry.OModulePresheaf.addCommGroup
  AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx
  AlgebraicGeometry.OModulePresheaf.moduleSections
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx
  AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap
  AlgebraicGeometry.Scheme.Modules.pullback_monoidal
  AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization'
  AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap
  AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal
  AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap
  AlgebraicGeometry.Scheme.Modules.sheafifyPullback_lifting
  PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ
  PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η
  PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal
  PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal
open _root_.PresheafOfModules.PullbackMonoidal in
attribute [-instance]
  instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb
attribute [-instance]
  PresheafOfModules.pullback_monoidal' SheafOfModules.isIso_ihomModelToIhom
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instNeg
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulInt
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAddCommGroup
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAdd
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSub
open _root_.AlgebraicGeometry.Scheme.IdealSheafData.IdealHom in
attribute [-instance]
  instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop
open _root_.AlgebraicGeometry.Scheme.IdealSheafData.IdealHom in
attribute [-instance]
  instSMulCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop
attribute [-instance]
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulNat
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instZero
  AlgebraicGeometry.SmoothOfRelativeDimension.fiberToSpecResidueField
attribute [-instance]
  AlgebraicGeometry.SmoothOfRelativeDimension.pullback_snd
  AlgebraicGeometry.SmoothOfRelativeDimension.pullback_fst
  AlgebraicGeometry.SmoothOfRelativeDimension.smooth_one
  AlgebraicGeometry.SmoothProperCurve.isIntegral_pullback_Spec_field
  AlgebraicGeometry.IsProper.fiberToSpecResidueField
attribute [-simp]
  AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app
  AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right
  AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left
  AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily
  AlgebraicGeometry.Scheme.Modules.familyOfHom_app
  AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply
  AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply
  AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply
  AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.sub_app
  AlgebraicGeometry.Scheme.IdealSheafData.sres_sresTop
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.add_app
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.sizeOf_spec
  AlgebraicGeometry.Scheme.IdealSheafData.coe_resLE
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.smul_app
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_ofLE_app
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.ideal_range
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zero_app
  AlgebraicGeometry.Scheme.IdealSheafData.sres_sres
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.comp_app
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.neg_app
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.id_app
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_mulRight_app
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.nsmul_app
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.injEq
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zsmul_app
  AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_snd
  AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_fst
