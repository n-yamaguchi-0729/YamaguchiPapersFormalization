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

import Mathlib.AlgebraicGeometry.Restrict
import Mathlib.CategoryTheory.ConcreteCategory.EpiMono
import Mathlib.CategoryTheory.EqToHom
import Mathlib.CategoryTheory.Opposites

/-!
# bijective app of bijective app Top morphism Restrict
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Schemes.Proofs.bijective_app_of_bijective_appTop_morphismRestrict

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

open TopologicalSpace Opposite

namespace P4Aux

theorem bijective_app_congr {X B : Scheme.{u}} (p : X ⟶ B) {V W : B.Opens} (e : V = W)
    (h : Function.Bijective (p.app V)) : Function.Bijective (p.app W) := by
  subst e; exact h

end P4Aux

open P4Aux


theorem _root_.AlgebraicGeometry.bijective_app_of_bijective_appTop_morphismRestrict {X B :
  Scheme.{u}} (p : X ⟶ B) (U : B.Opens)
    (h : Function.Bijective (p ∣_ U).appTop) : Function.Bijective (p.app U) := by
  have e : U.ι ''ᵁ ⊤ = U := U.ι_image_top
  apply bijective_app_congr p e
  have hcomp : Function.Bijective
      (p.app (U.ι ''ᵁ ⊤) ≫
        X.presheaf.map (eqToHom (image_morphismRestrict_preimage p U ⊤)).op) :=
    (congrArg (fun q : Γ(↑U, ⊤) ⟶ Γ(↑(p ⁻¹ᵁ U), ⊤) => Function.Bijective q)
      (morphismRestrict_appTop p U)).mp h
  exact (Function.Bijective.of_comp_iff'
    (ConcreteCategory.bijective_of_isIso
      (X.presheaf.map (eqToHom (image_morphismRestrict_preimage p U ⊤)).op))
    (p.app (U.ι ''ᵁ ⊤))).mp hcomp
end AlgebraicCurves.Geometry.Schemes.Proofs.bijective_app_of_bijective_appTop_morphismRestrict
end ProofImplementation
