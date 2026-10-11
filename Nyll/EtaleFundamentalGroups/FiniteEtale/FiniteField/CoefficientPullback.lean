/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# Coefficient base change of charts and overlaps

The literal pullbacks of two charts along a coefficient map form a cartesian overlap.
The comparison with their fiber product preserves both chart projections.
-/

noncomputable section
open CategoryTheory Limits AlgebraicGeometry
universe u
namespace EtaleFundamentalGroups

variable {T T' S A B : Scheme.{u}} (φ : T' ⟶ T) (f : S ⟶ T) (a : A ⟶ S) (b : B ⟶ S)

local notation "v" => (pullback.fst a b ≫ a ≫ f)
local notation "aL" =>
  (pullback.lift (pullback.fst φ (a ≫ f)) (pullback.snd φ (a ≫ f) ≫ a)
    (Eq.trans pullback.condition (Eq.symm (Category.assoc _ _ _))))
local notation "bL" =>
  (pullback.lift (pullback.fst φ (b ≫ f)) (pullback.snd φ (b ≫ f) ≫ b)
    (Eq.trans pullback.condition (Eq.symm (Category.assoc _ _ _))))
local notation "α" =>
  (pullback.lift (pullback.fst φ v) (pullback.snd φ v ≫ pullback.fst a b)
    (Eq.trans pullback.condition (Eq.symm (Category.assoc _ _ _))))
local notation "β" =>
  (pullback.lift (pullback.fst φ v) (pullback.snd φ v ≫ pullback.snd a b)
    (Eq.trans pullback.condition (Eq.trans (congrArg (fun h ↦ pullback.snd φ v ≫ h)
      (pullback.condition_assoc f)) (Eq.symm (Category.assoc _ _ _)))))

/-- The literal base-change map and second projections form a cartesian square. -/
theorem coefficientBaseChange_isPullback :
    IsPullback aL (pullback.snd φ (a ≫ f)) (pullback.snd φ f) a := by
  refine IsPullback.of_right ?_ (pullback.lift_snd _ _ _) (.of_hasPullback φ f)
  rw [pullback.lift_fst]
  exact .of_hasPullback φ (a ≫ f)
/-- Pulling back a fiber product along the coefficient base change remains a
fiber product of the literal base-changed factors. -/
theorem coefficientPullback_isPullback : IsPullback α β aL bL := by
  have hVA : IsPullback α (pullback.snd φ v) (pullback.snd φ (a ≫ f)) (pullback.fst a b) :=
    coefficientBaseChange_isPullback φ (a ≫ f) (pullback.fst a b)
  have hB : IsPullback bL (pullback.snd φ (b ≫ f)) (pullback.snd φ f) b :=
    coefficientBaseChange_isPullback φ f b
  have hw : α ≫ aL = β ≫ bL := by
    apply pullback.hom_ext
    · simp only [Category.assoc, pullback.lift_fst]
    · simp only [Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc]
      exact congrArg (fun h : pullback a b ⟶ S ↦ pullback.snd φ v ≫ h) pullback.condition
  refine IsPullback.of_bot ?_ hw hB
  rw [pullback.lift_snd, pullback.lift_snd]
  exact hVA.paste_vert (.of_hasPullback a b)

/-- The actual comparison of base-changed overlaps with overlaps of base-changed factors. -/
def coefficientPullbackIso : pullback φ v ≅ pullback aL bL :=
  (coefficientPullback_isPullback φ f a b).isoPullback

/-- The comparison has the canonical projection to the first base-changed factor. -/
theorem coefficientPullbackIso_hom_fst :
    (coefficientPullbackIso φ f a b).hom ≫ pullback.fst aL bL = α :=
  (coefficientPullback_isPullback φ f a b).isoPullback_hom_fst

/-- The comparison has the canonical projection to the second base-changed factor. -/
theorem coefficientPullbackIso_hom_snd :
    (coefficientPullbackIso φ f a b).hom ≫ pullback.snd aL bL = β :=
  (coefficientPullback_isPullback φ f a b).isoPullback_hom_snd

end EtaleFundamentalGroups
