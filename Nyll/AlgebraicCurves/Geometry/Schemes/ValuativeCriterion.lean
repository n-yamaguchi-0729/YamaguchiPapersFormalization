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

import Mathlib.AlgebraicGeometry.ValuativeCriterion
import Nyll.AlgebraicCurves.Geometry.Schemes.SchemeHomOver

/-!
# Valuative Criterion
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace NeronModelInfra

/-- The valuative criterion for a proper morphism, expressed as a unique morphism over the base. -/
theorem existsUnique_schemeHomOver_of_isProper_valuationSubring
    {L : Type u} [Field L] (O : ValuationSubring L)
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f]
    (s : Spec (CommRingCat.of ↥O) ⟶ Y) (x : Spec (CommRingCat.of L) ⟶ X)
    (hx : x ≫ f = Spec.map (CommRingCat.ofHom O.subtype) ≫ s) :
    ∃! xt : SchemeHomOver s f, Spec.map (CommRingCat.ofHom O.subtype) ≫ xt.1 = x := by
  have hProper :
      (ValuativeCriterion ⊓ @QuasiCompact ⊓ @QuasiSeparated ⊓ @LocallyOfFiniteType) f := by
    rw [← IsProper.eq_valuativeCriterion]
    infer_instance
  let square : ValuativeCommSq f :=
    { R := ↥O
      K := L
      i₁ := x
      i₂ := s
      commSq := ⟨hx⟩ }
  obtain ⟨hLift⟩ := hProper.1.1.1 square
  refine ⟨⟨(default : square.commSq.LiftStruct).l,
      (default : square.commSq.LiftStruct).fac_right⟩,
    (default : square.commSq.LiftStruct).fac_left, ?_⟩
  intro lift hLift'
  apply Subtype.ext
  have : (CommSq.LiftStruct.mk lift.1 hLift' lift.2 : square.commSq.LiftStruct) = default :=
    Unique.eq_default _
  exact congrArg CommSq.LiftStruct.l this

end NeronModelInfra
