/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_bijective_app_of_forall_isAffineOpen.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.Algebra.Category.Ring.Colimits
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.Topology.Sheaves.Functors
import Mathlib.Topology.Sheaves.Stalks

/-!
# bijective app of forall is Affine Open
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Schemes.Proofs.bijective_app_of_forall_isAffineOpen

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

open TopologicalSpace Opposite

namespace SheafGlueGC3

open TopCat TopCat.Presheaf

theorem stalkFunctor_map_surjective_of_isBasis {X : TopCat.{u}} {B : Set (Opens X)} (hB :
  Opens.IsBasis B)
    {F G : X.Presheaf CommRingCat.{u}} {α : F ⟶ G} (hα : ∀ U ∈ B, Function.Surjective (α.app (op
      U))) (x : X) :
    Function.Surjective ((stalkFunctor _ x).map α) := by
  intro t
  obtain ⟨U, hxU, hU, t, rfl⟩ := exists_mem_germ_eq_of_isBasis hB G x t
  obtain ⟨s, rfl⟩ := hα U hU t
  exact ⟨F.germ U x hxU s, by rw [stalkFunctor_map_germ_apply]⟩

end SheafGlueGC3

theorem _root_.AlgebraicGeometry.bijective_app_of_forall_isAffineOpen {X B : Scheme.{u}} (p : X ⟶ B)
    (h : ∀ U : B.Opens, IsAffineOpen U → Function.Bijective (p.app U)) (U : B.Opens) :
    Function.Bijective (p.app U) := by
  let F : TopCat.Sheaf CommRingCat.{u} B.carrier := B.sheaf
  let G : TopCat.Sheaf CommRingCat.{u} B.carrier := (TopCat.Sheaf.pushforward _ p.base).obj X.sheaf
  let f : F ⟶ G := ⟨p.c⟩
  have key := TopCat.Presheaf.app_bijective_of_stalkFunctor_map_bijective f U (fun x _ =>
    ⟨TopCat.Presheaf.stalkFunctor_map_injective_of_isBasis B.isBasis_affineOpens
        (fun V hV => (h V hV).1) x,
     SheafGlueGC3.stalkFunctor_map_surjective_of_isBasis B.isBasis_affineOpens
        (fun V hV => (h V hV).2) x⟩)
  exact key
end AlgebraicCurves.Geometry.Schemes.Proofs.bijective_app_of_forall_isAffineOpen
end ProofImplementation
