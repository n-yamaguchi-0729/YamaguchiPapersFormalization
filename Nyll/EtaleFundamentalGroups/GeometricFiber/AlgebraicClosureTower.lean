/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Nyll.EtaleFundamentalGroups.FiniteEtale.FiniteField.ConstantFieldTower
import Mathlib.FieldTheory.IsSepClosed
import Mathlib.FieldTheory.PurelyInseparable.Basic
import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap

/-!
# Algebraic Closure Tower

The actual projection from the constant extension to its maximal
separable intermediate extension.
-/

noncomputable section
open CategoryTheory Limits
universe u
namespace AlgebraicGeometry.FiniteEtale

variable (k L : Type u) [Field k] [Field L] [Algebra k L]
variable (X : Scheme.{u}) (f : X ⟶ Spec (.of k))

local notation "K" => separableClosure k L
local notation "φK" => Spec.map (CommRingCat.ofHom (algebraMap k K))
local notation "φL" => Spec.map (CommRingCat.ofHom (algebraMap k L))
local notation "ψ" =>
  Spec.map (CommRingCat.ofHom (AlgHom.toRingHom (IntermediateField.val (separableClosure k L))))

/-- The actual projection from the constant extension to its maximal
separable intermediate extension. -/
def separableClosureProjection : Limits.pullback φL f ⟶ Limits.pullback φK f :=
  (EtaleFundamentalGroups.constantFieldTowerIso k L K X f).inv ≫
    pullback.snd ψ (pullback.fst φK f)

/-- The projection to the separable intermediate extension preserves the
original scheme coordinate. -/
@[reassoc]
theorem separableClosureProjection_comp_snd :
    separableClosureProjection k L X f ≫ pullback.snd φK f = pullback.snd φL f := by
  dsimp only [separableClosureProjection]
  rw [Category.assoc, ← EtaleFundamentalGroups.constantFieldTowerIso_hom_snd k L K X f,
    ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

/-- The projection preserves the coefficient coordinate along the canonical
inclusion of the maximal separable subfield. -/
@[reassoc]
theorem separableClosureProjection_comp_fst :
    separableClosureProjection k L X f ≫ pullback.fst φK f =
      pullback.fst φL f ≫ ψ := by
  dsimp only [separableClosureProjection]
  rw [Category.assoc, ← pullback.condition]
  rw [← EtaleFundamentalGroups.constantFieldTowerIso_hom_fst k L K X f,
    ← Category.assoc, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

/-- The projection is the actual base change of the inclusion of the
maximal separable subfield. -/
theorem separableClosureProjection_isPullback :
    IsPullback (separableClosureProjection k L X f) (pullback.fst φL f)
      (pullback.fst φK f) ψ := by
  apply IsPullback.of_right (v₁₃ := f) (h₁₂ := pullback.snd φK f) (h₂₂ := φK)
  · rw [separableClosureProjection_comp_snd]
    have hcoeff : ψ ≫ φK = φL := by
      rw [← Spec.map_comp]
      rfl
    rw [hcoeff]
    exact (IsPullback.of_hasPullback φL f).flip
  · exact separableClosureProjection_comp_fst k L X f
  · exact (IsPullback.of_hasPullback φK f).flip

/-- Connectedness descends from the algebraic constant extension to its
maximal separable intermediate extension. -/
theorem connectedSpace_separableClosure_of_connected_constantField
    [ConnectedSpace ↑(Limits.pullback φL f)] :
    ConnectedSpace ↑(Limits.pullback φK f) := by
  have hψ : Surjective ψ := ⟨fun y ↦
    ⟨Classical.choice (inferInstance : Nonempty (Spec (.of L))), Subsingleton.elim _ _⟩⟩
  let : Surjective (separableClosureProjection k L X f) :=
    MorphismProperty.of_isPullback (P := @Surjective)
      (separableClosureProjection_isPullback k L X f).flip hψ
  exact (separableClosureProjection k L X f).surjective.connectedSpace
    (separableClosureProjection k L X f).continuous

end AlgebraicGeometry.FiniteEtale
