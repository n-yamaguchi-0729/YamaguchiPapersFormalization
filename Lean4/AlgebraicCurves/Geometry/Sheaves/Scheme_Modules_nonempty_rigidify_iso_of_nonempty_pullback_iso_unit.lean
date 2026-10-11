/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Anthropic FLT source material is identified by code comparison;
the exact source-file correspondence remains unresolved.
Upstream repository: https://github.com/anthropics/fermats-last-theorem
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Adjunction.Mates
import SchemeTheory.Modules.Monoidal
import AlgebraicCurves.Geometry.Sheaves.ModulesRigidify
import SchemeTheory.Modules.PullbackMonoidal

/-!
# Scheme Modules nonempty rigidify iso of nonempty pullback iso unit
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Sheaves.Proofs
namespace Scheme_Modules_nonempty_rigidify_iso_of_nonempty_pullback_iso_unit

universe u


open _root_.CategoryTheory
open _root_.CategoryTheory.MonoidalCategory
open _root_.AlgebraicGeometry


theorem _root_.AlgebraicGeometry.Scheme.Modules.nonempty_rigidify_iso_of_nonempty_pullback_iso_unit
    {T P : Scheme.{u}} (σ : T ⟶ P) (q : P ⟶ T) (L : P.Modules)
    (hσL : Nonempty ((Scheme.Modules.pullback σ).obj L ≅ 𝟙_ T.Modules)) :
    Nonempty (Scheme.Modules.rigidify σ q L ≅ L) := by
  obtain ⟨e⟩ := hσL
  let u : ihom (𝟙_ T.Modules) ≅ 𝟭 T.Modules :=
    conjugateIsoEquiv (ihom.adjunction (𝟙_ T.Modules)) Adjunction.id (leftUnitorNatIso
      T.Modules).symm
  let d : Scheme.Modules.dual ((Scheme.Modules.pullback σ).obj L) ≅ 𝟙_ T.Modules :=
    Scheme.Modules.dualMapIso e ≪≫ u.app (𝟙_ T.Modules)
  refine ⟨?_⟩
  rw [Scheme.Modules.rigidify_def]
  exact whiskerLeftIso L ((Scheme.Modules.pullback q).mapIso d ≪≫
    Scheme.Modules.pullbackTensorUnitObjIso q) ≪≫ ρ_ L
end Scheme_Modules_nonempty_rigidify_iso_of_nonempty_pullback_iso_unit
end AlgebraicCurves.Geometry.Sheaves.Proofs
end ProofImplementation

open _root_.PresheafOfModules.PullbackMonoidal in
attribute [-instance]
  AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap
  AlgebraicGeometry.Scheme.Modules.pullback_monoidal
  AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization'
  AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap
  AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal
  AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap
  AlgebraicGeometry.Scheme.Modules.sheafifyPullback_lifting
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
attribute [-simp] PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app
