/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_nonempty_mul_invModule_iso_tensor.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import AlgebraicCurves.Geometry.Sheaves.IdealSheafModule
import AlgebraicCurves.Geometry.Picard.Functor
import AlgebraicCurves.RelativeDivisors.Cartier
import SchemeTheory.Modules.PresheafInternalHom
import SchemeTheory.Modules.SheafificationMonoidal
import SchemeTheory.Modules.Monoidal
import AlgebraicCurves.Geometry.Sheaves.Scheme_IdealSheafData_IsInvertible_isInvertible_module
import AlgebraicCurves.Geometry.Sheaves.Scheme_IdealSheafData_IsInvertible_nonempty_mul_module_iso_tensor
import AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_IsInvertible_tensor
import AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_IsInvertible_dual
import AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_IsInvertible_dual_tensor

/-!
# Inverse modules of products of invertible ideal sheaves

The inverse module of a product of invertible ideal sheaves is identified with
the tensor product of their inverse modules.
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Sheaves.Proofs
namespace Scheme_IdealSheafData_IsInvertible_nonempty_mul_invModule_iso_tensor
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
attribute [-simp] PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app

universe u

open _root_.CategoryTheory
open _root_.CategoryTheory.MonoidalCategory
namespace AlgebraicGeometry
open _root_.AlgebraicGeometry
namespace Scheme
open _root_.AlgebraicGeometry.Scheme
namespace Modules
open _root_.AlgebraicGeometry.Scheme.Modules
namespace InverseUnique
open _root_.AlgebraicGeometry.Scheme.Modules
open _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry

open _root_.CategoryTheory
open _root_.CategoryTheory.MonoidalCategory

/-- The canonical isomorphism between two tensor inverses of the same object. -/
noncomputable def inverseUnique {C : Type*} [Category C] [MonoidalCategory C] [BraidedCategory C]
    {L M M' : C} (e : L ⊗ M ≅ 𝟙_ C) (e' : L ⊗ M' ≅ 𝟙_ C) : M ≅ M' :=
  (λ_ M).symm ≪≫ (e'.symm ⊗ᵢ Iso.refl M) ≪≫ (β_ L M' ⊗ᵢ Iso.refl M) ≪≫ α_ M' L M ≪≫
    (Iso.refl M' ⊗ᵢ e) ≪≫ ρ_ M'

end AlgebraicGeometry.Scheme.Modules.InverseUnique

open _root_.AlgebraicGeometry AlgebraicGeometry _root_.AlgebraicGeometry.Scheme.Modules
    AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.InverseUnique
    AlgebraicGeometry.Scheme.IdealSheafData in
theorem
  _root_.AlgebraicGeometry.Scheme.IdealSheafData.IsInvertible.nonempty_mul_invModule_iso_tensor {X :
  AlgebraicGeometry.Scheme.{u}} {I J : X.IdealSheafData}
    (hI : I.IsInvertible) (hJ : J.IsInvertible) :
    Nonempty ((I * J).invModule ≅ I.invModule ⊗ J.invModule) := by
  obtain ⟨e⟩ := IsInvertible.nonempty_mul_module_iso_tensor hI hJ
  have hA : Scheme.Modules.IsInvertible (I * J).module := IsInvertible.isInvertible_module (hI.mul
      hJ)
  have hB : Scheme.Modules.IsInvertible (I.module ⊗ J.module) :=
    (IsInvertible.isInvertible_module hI).tensor (IsInvertible.isInvertible_module hJ)
  obtain ⟨eA⟩ := (Scheme.Modules.IsInvertible.dual hA).2
  obtain ⟨eB⟩ := (Scheme.Modules.IsInvertible.dual hB).2
  have eB' : (I * J).module ⊗ Scheme.Modules.dual (I.module ⊗ J.module) ≅ 𝟙_ X.Modules :=
    (e ⊗ᵢ Iso.refl _) ≪≫ eB
  obtain ⟨e11⟩ := Scheme.Modules.IsInvertible.dual_tensor (IsInvertible.isInvertible_module hI)
    (IsInvertible.isInvertible_module hJ)
  exact ⟨inverseUnique eA eB' ≪≫ e11⟩
end Scheme_IdealSheafData_IsInvertible_nonempty_mul_invModule_iso_tensor
end AlgebraicCurves.Geometry.Sheaves.Proofs
end ProofImplementation
