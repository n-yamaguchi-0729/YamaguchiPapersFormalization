/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_IsLocallyFreeOfRank_of_forall_exists_opens.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
import AlgebraicCurves.Geometry.Sheaves.ModulesLocallyFreeOfRank

/-!
# Local freeness from an open cover

Pullback to open subschemes identifies the local trivializations used to establish a fixed rank.
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Sheaves.Proofs
namespace Scheme_Modules_IsLocallyFreeOfRank_of_forall_exists_opens

universe u
open _root_.CategoryTheory
open _root_.AlgebraicGeometry
open _root_.Opposite
open _root_.AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry
open _root_.AlgebraicGeometry
namespace Scheme
open _root_.AlgebraicGeometry.Scheme
namespace Modules
open _root_.AlgebraicGeometry.Scheme.Modules
open _root_.AlgebraicGeometry.Scheme.Modules
open _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry

theorem opensMap_final' {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (TopologicalSpace.Opens.map f.base).Final :=
  CategoryTheory.final_of_representablyFlat _

/-- The canonical free-module pullback identification along the final map of open-set sites. -/
noncomputable def pullbackFreeIso' {X Y : Scheme.{u}} (f : X ⟶ Y) (I : Type u) :
    (Scheme.Modules.pullback f).obj (SheafOfModules.free.{u} I) ≅ SheafOfModules.free.{u} I :=
  let : (TopologicalSpace.Opens.map f.base).Final := opensMap_final' f
  let : (SheafOfModules.pushforward.{u} f.toRingCatSheafHom).IsRightAdjoint :=
    (Scheme.Modules.pullbackPushforwardAdjunction f).isRightAdjoint
  SheafOfModules.pullbackObjFreeIso f.toRingCatSheafHom I
end AlgebraicGeometry.Scheme.Modules

open _root_.AlgebraicGeometry AlgebraicGeometry in
theorem _root_.AlgebraicGeometry.Scheme.Modules.IsLocallyFreeOfRank.of_forall_exists_opens {X :
  Scheme.{u}} {n : ℕ} {M : X.Modules}
    (h : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
      Scheme.Modules.IsLocallyFreeOfRank n ((Scheme.Modules.pullback U.ι).obj M)) :
    Scheme.Modules.IsLocallyFreeOfRank n M := by
  refine ⟨fun x => ?_⟩
  obtain ⟨U, hxU, hU⟩ := h x
  obtain ⟨V, hxV, ⟨e⟩⟩ := hU.exists_trivialization ⟨x, hxU⟩
  refine ⟨U.ι ''ᵁ V, ⟨⟨x, hxU⟩, hxV, rfl⟩, ⟨?_⟩⟩
  let i := U.ι.isoImage V
  have hi : i.inv ≫ V.ι ≫ U.ι = (U.ι ''ᵁ V).ι := U.ι.isoImage_inv_ι V
  exact (pullbackCongr hi.symm).app M ≪≫
    ((pullbackComp i.inv (V.ι ≫ U.ι)).symm.app M) ≪≫
    (Scheme.Modules.pullback i.inv).mapIso
      (((pullbackComp V.ι U.ι).symm.app M) ≪≫ (Scheme.Modules.pullback V.ι).mapIso (Iso.refl _) ≪≫
          e) ≪≫
    AlgebraicGeometry.Scheme.Modules.pullbackFreeIso' i.inv _
end Scheme_Modules_IsLocallyFreeOfRank_of_forall_exists_opens
end AlgebraicCurves.Geometry.Sheaves.Proofs
end ProofImplementation
