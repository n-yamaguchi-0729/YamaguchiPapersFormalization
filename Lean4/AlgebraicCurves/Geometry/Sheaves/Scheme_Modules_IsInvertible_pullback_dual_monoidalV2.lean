/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_IsInvertible_pullback_dual_monoidalV2.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Iso
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Monoidal.Braided.Basic
import Mathlib.CategoryTheory.Monoidal.Functor
import AlgebraicCurves.Geometry.Picard.Functor
import SchemeTheory.Modules.PresheafInternalHom
import AlgebraicCurves.Foundations.Algebra.SheafOfModules_MonoidalV2
import AlgebraicCurves.Geometry.Sheaves.ModulesPullbackMonoidalV2
import SchemeTheory.Modules.PresheafPullbackMonoidal
import AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_IsInvertible_dual_monoidalV2

/-!
# Scheme Modules Is Invertible pullback dual monoidal V2
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Sheaves.Proofs
namespace Scheme_Modules_IsInvertible_pullback_dual_monoidalV2

universe u


open _root_.CategoryTheory
open _root_.CategoryTheory.MonoidalCategory


namespace AlgebraicGeometry

export _root_.AlgebraicGeometry (Scheme.Modules.pullback Scheme Scheme.Modules
  Scheme.Modules.IsInvertible Scheme.Modules.dual Scheme.Modules.pullbackTensorUnitObjIso
  Scheme.Modules.IsInvertible.dual_monoidalV2)

namespace Scheme

export _root_.AlgebraicGeometry.Scheme (Modules.pullback Modules Modules.IsInvertible Modules.dual
  Modules.pullbackTensorUnitObjIso Modules.IsInvertible.dual_monoidalV2)

namespace Modules

export _root_.AlgebraicGeometry.Scheme.Modules (pullback IsInvertible dual pullbackTensorUnitObjIso
  IsInvertible.dual_monoidalV2)

namespace InverseUnique

open _root_.AlgebraicGeometry.Scheme.Modules
open _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry



open _root_.CategoryTheory
open _root_.CategoryTheory.MonoidalCategory


/--
The isomorphism between two tensor inverses of the same object, constructed using the braiding
and the specified evaluations.
-/
noncomputable def inverseUnique {C : Type*} [Category C] [MonoidalCategory C] [BraidedCategory C]
    {L M M' : C} (e : L ⊗ M ≅ 𝟙_ C) (e' : L ⊗ M' ≅ 𝟙_ C) : M ≅ M' :=
  (λ_ M).symm ≪≫ (e'.symm ⊗ᵢ Iso.refl M) ≪≫ (β_ L M' ⊗ᵢ Iso.refl M) ≪≫ α_ M' L M ≪≫
    (Iso.refl M' ⊗ᵢ e) ≪≫ ρ_ M'

end AlgebraicGeometry.Scheme.Modules.InverseUnique

open _root_.AlgebraicGeometry in
open Scheme_Modules_IsInvertible_pullback_dual_monoidalV2.AlgebraicGeometry.Scheme.Modules in
open InverseUnique in
theorem _root_.AlgebraicGeometry.Scheme.Modules.IsInvertible.pullback_dual_monoidalV2
    {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y) {L : Y.Modules}
    (hL : AlgebraicGeometry.Scheme.Modules.IsInvertible L) :
    Nonempty ((AlgebraicGeometry.Scheme.Modules.pullback f).obj
        (AlgebraicGeometry.Scheme.Modules.dual L) ≅
      AlgebraicGeometry.Scheme.Modules.dual ((AlgebraicGeometry.Scheme.Modules.pullback f).obj L))
        := by
  obtain ⟨eL⟩ := (Scheme.Modules.IsInvertible.dual_monoidalV2 hL).2
  obtain ⟨e'⟩ := (Scheme.Modules.IsInvertible.dual_monoidalV2 (hL.pullback f)).2
  let e : (Scheme.Modules.pullback f).obj L ⊗ (Scheme.Modules.pullback f).obj (Scheme.Modules.dual
    L) ≅
      𝟙_ X.Modules :=
    Functor.Monoidal.μIso (Scheme.Modules.pullback f) L (Scheme.Modules.dual L) ≪≫
      (Scheme.Modules.pullback f).mapIso eL ≪≫ Scheme.Modules.pullbackTensorUnitObjIso f
  exact ⟨inverseUnique e e'⟩
end AlgebraicCurves.Geometry.Sheaves.Proofs.Scheme_Modules_IsInvertible_pullback_dual_monoidalV2
end ProofImplementation

open PresheafOfModules.PullbackMonoidal in
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
