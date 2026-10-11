/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Cohomology.FiniteH1PullbackComposition
import Nyll.EtaleFundamentalGroups.GeometricFiber.PullbackEquivalence

/-! # Identity and isomorphism pullback on actual finite H¹ -/

noncomputable section

open CategoryTheory AlgebraicGeometry

namespace EtaleFundamentalGroups.Cohomology

/-- Surjectivity on actual fundamental groups implies injectivity of the
already constructed derived H¹ pullback. -/
theorem constantFiniteH1Pullback_injective_of_fundamentalGroupHom_surjective
    {X Y : Scheme} [ConnectedSpace X] [ConnectedSpace Y]
    (f : X ⟶ Y) {Ω : Type} [Field Ω] [IsSepClosed Ω]
    (geom : Spec (.of Ω) ⟶ X) (A : AddCommGrpCat.{0}) [Finite A]
    (hf : Function.Surjective (FiniteEtale.fundamentalGroupHom f geom)) :
    Function.Injective (constantCohomologyPullback f A 1) := by
  let : TopologicalSpace (Multiplicative A) := ⊥
  intro a b hab
  apply h1Character_injective A (geom ≫ f)
  apply ContinuousMonoidHom.ext
  intro γ
  obtain ⟨σ, rfl⟩ := hf γ
  have ha := congrArg (fun χ => χ σ) (h1Character_schemePullback f A geom a)
  have hb := congrArg (fun χ => χ σ) (h1Character_schemePullback f A geom b)
  exact ha.trans ((congrArg (fun c => h1Character A geom c σ) hab).trans hb.symm)

/-- Pullback by the identity acts as the identity on actual derived finite H¹. -/
theorem constantFiniteH1Pullback_id
    {X : Scheme} [ConnectedSpace X]
    {Ω : Type} [Field Ω] [IsSepClosed Ω]
    (geom : Spec (.of Ω) ⟶ X) (A : AddCommGrpCat.{0}) [Finite A]
    (c : Sheaf.H.{0} ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{0}).obj A) 1) :
    constantCohomologyPullback (𝟙 X) A 1 c = c := by
  let E : FiniteEtale X ≌ FiniteEtale X :=
    MorphismProperty.Over.pullbackIso
      (@IsFiniteEtale : MorphismProperty Scheme) ⊤ (Iso.refl X)
  have : (FiniteEtale.pullback (𝟙 X)).IsEquivalence := E.isEquivalence_functor
  have hf := FiniteEtale.fundamentalGroupHom_bijective_of_pullback_isEquivalence
    (𝟙 X) geom
  have hi := constantFiniteH1Pullback_injective_of_fundamentalGroupHom_surjective
    (𝟙 X) geom A hf.2
  apply hi
  have h := constantFiniteH1Pullback_comp (𝟙 X) (𝟙 X) geom A c
  rw [Category.id_comp] at h
  exact h.symm

end EtaleFundamentalGroups.Cohomology
