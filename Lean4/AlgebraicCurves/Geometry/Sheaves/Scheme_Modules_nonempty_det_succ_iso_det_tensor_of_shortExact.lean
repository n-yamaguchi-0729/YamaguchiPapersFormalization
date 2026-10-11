/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_nonempty_det_succ_iso_det_tensor_of_shortExact.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import AlgebraicCurves.Geometry.Sheaves.ModulesDet
import AlgebraicCurves.Geometry.Sheaves.ModulesLocallyFreeOfRank
import AlgebraicCurves.Geometry.Picard.Functor
import SchemeTheory.Modules.Monoidal
import AlgebraicCurves.Geometry.Sheaves.ModulesWedge
import AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_epi_whiskerRight_wedgeVec_of_shortExact
import AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_isZero_exteriorPower_of_isLocallyFreeOfRank
import AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_isInvertible_det_of_isLocallyFreeOfRank
import AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_IsInvertible_tensor
import AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_IsInvertible_isIso_of_locallySurjective
import AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_Hom_epi_iff_locallySurjective

/-!
# Determinants in a short exact sequence

For a locally free short exact complex with an invertible quotient, the determinant
of the middle term is the determinant of the first term tensored with the quotient.
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Sheaves.Proofs
namespace Scheme_Modules_nonempty_det_succ_iso_det_tensor_of_shortExact
open _root_.PresheafOfModules.PullbackMonoidal in
attribute [-instance]
  PresheafOfModules.PullbackMonoidal.pullback_monoidal
  PresheafOfModules.PullbackMonoidal.isIso_δ
  PresheafOfModules.pushforward_laxMonoidal
  PresheafOfModules.PullbackMonoidal.isIso_η
  PresheafOfModules.free_monoidal
  PresheafOfModules.restrictScalars_laxMonoidal
  PresheafOfModules.PullbackMonoidal.isIso_δ_gS
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
attribute [-simp] PresheafOfModules.pushforwardCongr_inv_app_app_apply
    PresheafOfModules.pushforwardNatTrans_app_app_apply
    PresheafOfModules.pushforwardCongr_hom_app_app_apply PresheafOfModules.freeεIso_hom_app
    PresheafOfModules.freeμIso_hom_app

universe u

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory

theorem _root_.AlgebraicGeometry.Scheme.Modules.nonempty_det_succ_iso_det_tensor_of_shortExact
    {X : Scheme.{u}} {n : ℕ} (S : ShortComplex X.Modules) (hS : S.ShortExact)
    (h₁ : Scheme.Modules.IsLocallyFreeOfRank n S.X₁) (h₂ : Scheme.Modules.IsLocallyFreeOfRank (n +
        1) S.X₂)
    (h₃ : Scheme.Modules.IsInvertible S.X₃) :
    Nonempty (Scheme.Modules.det (n + 1) S.X₂ ≅ Scheme.Modules.det n S.X₁ ⊗ S.X₃) := by
  have := hS.epi_g
  let D : X.Modules := Scheme.Modules.det n S.X₁
  let ψ : D ⊗ S.X₂ ⟶ Scheme.Modules.det (n + 1) S.X₂ :=
    ((Scheme.Modules.exteriorPower X n).map S.f ▷ S.X₂) ≫ Scheme.Modules.wedgeVec n S.X₂
  have hzero : (D ◁ S.f) ≫ ψ = 0 := by
    have hnat : (D ◁ S.f) ≫ ψ =
        Scheme.Modules.wedgeVec n S.X₁ ≫ (Scheme.Modules.exteriorPower X (n + 1)).map S.f := by
      simp only [ψ, D, ← Category.assoc, ← MonoidalCategory.tensorHom_def',
        Scheme.Modules.wedgeVec_naturality]
    have hZ := AlgebraicGeometry.Scheme.Modules.isZero_exteriorPower_of_isLocallyFreeOfRank h₁
        (Nat.lt_succ_self n)
    rw [hnat, hZ.eq_of_tgt (Scheme.Modules.wedgeVec n S.X₁) 0, zero_comp]
  let G : X.Modules ⥤ X.Modules := tensorLeft D
  have hGf : G.map S.f = D ◁ S.f := rfl
  let hc : IsColimit (CokernelCofork.ofπ (G.map (cokernel.π S.f))
      (show G.map S.f ≫ G.map (cokernel.π S.f) = 0 by rw [← G.map_comp, cokernel.condition,
          G.map_zero]) :
        CokernelCofork (G.map S.f)) :=
    isColimitOfHasCokernelOfPreservesColimit G S.f
  let φ' : G.obj (cokernel S.f) ⟶ Scheme.Modules.det (n + 1) S.X₂ :=
    hc.desc (CokernelCofork.ofπ ψ (by rw [hGf]; exact hzero))
  have hφ' : G.map (cokernel.π S.f) ≫ φ' = ψ := hc.fac _ WalkingParallelPair.one
  let e₃ := IsColimit.coconePointUniqueUpToIso hS.exact.gIsCokernel (cokernelIsCokernel S.f)
  have he₃ : S.g ≫ e₃.hom = cokernel.π S.f := by
    simpa using IsColimit.comp_coconePointUniqueUpToIso_hom hS.exact.gIsCokernel (cokernelIsCokernel
        S.f)
      WalkingParallelPair.one
  let φ : D ⊗ S.X₃ ⟶ Scheme.Modules.det (n + 1) S.X₂ := (D ◁ e₃.hom) ≫ φ'
  have hfac : (D ◁ S.g) ≫ φ = ψ := by
    simp only [φ, ← MonoidalCategory.whiskerLeft_comp_assoc, he₃]
    exact hφ'
  have hψ : Epi ψ := AlgebraicGeometry.Scheme.Modules.epi_whiskerRight_wedgeVec_of_shortExact S hS
      h₁ h₃
  have : Epi φ := epi_of_epi_fac hfac
  have hDL : Scheme.Modules.IsInvertible (D ⊗ S.X₃) :=
    (AlgebraicGeometry.Scheme.Modules.isInvertible_det_of_isLocallyFreeOfRank h₁).tensor h₃
  have hE : Scheme.Modules.IsInvertible (Scheme.Modules.det (n + 1) S.X₂) :=
    AlgebraicGeometry.Scheme.Modules.isInvertible_det_of_isLocallyFreeOfRank h₂
  have : IsIso φ := AlgebraicGeometry.Scheme.Modules.IsInvertible.isIso_of_locallySurjective hDL hE
      φ
    ((AlgebraicGeometry.Scheme.Modules.Hom.epi_iff_locallySurjective φ).mp inferInstance)
  exact ⟨(asIso φ).symm⟩
end Scheme_Modules_nonempty_det_succ_iso_det_tensor_of_shortExact
end AlgebraicCurves.Geometry.Sheaves.Proofs
end ProofImplementation
