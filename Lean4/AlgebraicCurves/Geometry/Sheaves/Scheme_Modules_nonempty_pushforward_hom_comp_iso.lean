/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_nonempty_pushforward_hom_comp_iso.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Adjunction.Unique
import Mathlib.CategoryTheory.Equivalence

/-!
# Scheme Modules nonempty pushforward hom comp iso
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Sheaves.Proofs.Scheme_Modules_nonempty_pushforward_hom_comp_iso

universe u

open CategoryTheory AlgebraicGeometry

namespace PushIso

variable {X Y : Scheme.{u}} (φ : X ≅ Y)

/-- The equivalence of module sheaves induced by pushforward along the scheme isomorphism `φ`. -/
noncomputable def pushEquiv : X.Modules ≌ Y.Modules :=
  CategoryTheory.Equivalence.mk (Scheme.Modules.pushforward φ.hom) (Scheme.Modules.pushforward
    φ.inv)
    ((Scheme.Modules.pushforwardId X).symm ≪≫ Scheme.Modules.pushforwardCongr φ.hom_inv_id.symm ≪≫
      (Scheme.Modules.pushforwardComp φ.hom φ.inv).symm)
    (Scheme.Modules.pushforwardComp φ.inv φ.hom ≪≫ Scheme.Modules.pushforwardCongr φ.inv_hom_id ≪≫
      Scheme.Modules.pushforwardId Y)

/-- Identify pullback along `φ.hom` with pushforward along `φ.inv` using uniqueness of left
adjoints. -/
noncomputable def pullbackIsoPushforwardInv :
    Scheme.Modules.pullback φ.hom ≅ Scheme.Modules.pushforward φ.inv :=
  (Scheme.Modules.pullbackPushforwardAdjunction φ.hom).leftAdjointUniq (pushEquiv
    φ).symm.toAdjunction

end PushIso

theorem _root_.AlgebraicGeometry.Scheme.Modules.nonempty_pushforward_hom_comp_iso
    {X Y Z : Scheme.{u}} (e : X ≅ Y) (f : Y ⟶ Z) (F : X.Modules) :
    Nonempty ((Scheme.Modules.pushforward (e.hom ≫ f)).obj F ≅
      (Scheme.Modules.pushforward f).obj ((Scheme.Modules.pullback e.inv).obj F)) :=
  ⟨(Scheme.Modules.pushforwardComp e.hom f).symm.app F ≪≫
    (Scheme.Modules.pushforward f).mapIso ((PushIso.pullbackIsoPushforwardInv e.symm).app F).symm⟩
end AlgebraicCurves.Geometry.Sheaves.Proofs.Scheme_Modules_nonempty_pushforward_hom_comp_iso
end ProofImplementation
