/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Cohomology.PointedH1Pullback
import Nyll.EtaleFundamentalGroups.Cohomology.FiniteH1Comparison
import Nyll.EtaleFundamentalGroups.GeometricFiber.DeckFundamentalGroup
import Nyll.EtaleFundamentalGroups.FiniteEtale.Connected
import Mathlib.CategoryTheory.Galois.Decomposition
import Mathlib.CategoryTheory.Galois.GaloisObjects

/-!
# Centralizers act trivially on actual finite-coefficient H¹

For a geometric deck transformation selected by ambient monodromy, an element
centralizing the covering subgroup acts trivially on the actual derived H¹.
This comparison does not assume H¹ faithfulness. The geometric proof that a
nonidentity deck transformation must act nontrivially remains a separate step.
-/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.PreGaloisCategory

namespace EtaleFundamentalGroups.Cohomology

variable {S : Scheme.{u}} [ConnectedSpace S] (A : FiniteEtale S)
variable [ConnectedSpace A.left]
variable {Ω : Type u} [Field Ω] [IsSepClosed Ω]
variable (xi : Spec (.of Ω) ⟶ A.left)
variable (σ : Aut A) (g : Aut (FiniteEtale.fiber (xi ≫ A.hom)))
variable (h : (FiniteEtale.fiber (xi ≫ A.hom)).map σ.hom
    (FiniteEtale.liftedFiberPoint A xi) = g • FiniteEtale.liftedFiberPoint A xi)

include h in
/-- Actual derived H¹ pullback by the geometric deck transformation is the
identity when its ambient lift centralizes the actual covering subgroup. -/
theorem constantH1Pullback_deck_eq_self_of_centralizes
    (hc : ∀ a : Aut (FiniteEtale.fiber xi),
      Commute g (FiniteEtale.fundamentalGroupHom A.hom xi a))
    (B : AddCommGrpCat.{u}) [Finite B]
    (c : Sheaf.H.{u} ((constantSheaf A.left.smallEtaleTopology AddCommGrpCat.{u}).obj B) 1) :
    constantCohomologyPullback σ.hom.left B 1 c = c := by
  let : TopologicalSpace (Multiplicative B) := ⊥
  apply h1Character_injective B xi
  apply ContinuousMonoidHom.ext
  intro a
  have hp := congrArg
    (fun χ : Aut (FiniteEtale.fiber xi) →ₜ* Multiplicative B => χ a)
    (h1Character_pointedSchemePullback σ.hom.left B xi xi
      (FiniteEtale.deckPointedGeometricFiberIso A xi σ g h) c)
  exact hp.symm.trans
    (congrArg (h1Character B xi c)
      (FiniteEtale.deckPointed_eq_self_of_centralizes A xi σ g h hc a))

end EtaleFundamentalGroups.Cohomology


namespace EtaleFundamentalGroups.Cohomology

/-- Geometric faithfulness of the joint deck action on finite-coefficient
derived H¹ kills every central element of the actual fundamental group.
The geometric faithfulness premise is supplied separately for each curve;
the fiber and conjugation comparisons in this proof are the actual ones. -/
theorem fundamentalGroup_eq_one_of_finiteH1_deck_faithful
    {X : Scheme.{u}} [ConnectedSpace X]
    {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (geom : Spec (.of Ω) ⟶ X)
    (hfaithful : ∀ (A : FiniteEtale X) [CategoryTheory.PreGaloisCategory.IsGalois A]
      (_xi : Spec (.of Ω) ⟶ A.left) (σ : Aut A),
      (∀ (C : AddCommGrpCat.{u}) [Finite C]
        (c : Sheaf.H.{u}
          ((constantSheaf A.left.smallEtaleTopology AddCommGrpCat.{u}).obj C) 1),
        constantCohomologyPullback σ.hom.left C 1 c = c) → σ = 1)
    (g : Aut (FiniteEtale.fiber geom)) (hc : ∀ a, Commute g a) :
    g = 1 := by
  apply Iso.ext
  apply natTrans_ext_of_isGalois (FiniteEtale.fiber geom)
  intro A hA
  have : CategoryTheory.PreGaloisCategory.IsGalois A := hA
  have : ConnectedSpace A.left := FiniteEtale.connectedSpace_left_of_isConnected A
  apply FintypeCat.hom_ext
  intro x
  change g • x = x
  let z : Over.mk geom ⟶ A.toComma := FiniteEtale.fiberObjEquivHom geom A x
  let lift : Spec (.of Ω) ⟶ A.left := z.left
  have hbase : lift ≫ A.hom = geom := z.w
  have hx : (FiniteEtale.fiberObjEquivHom geom A).symm
      (Over.homMk lift hbase) = x := by
    apply (FiniteEtale.fiberObjEquivHom geom A).injective
    rw [Equiv.apply_symm_apply]
    apply Over.OverMorphism.ext
    rfl
  have hfix : ∀ (b : Spec (.of Ω) ⟶ X) (hb : lift ≫ A.hom = b)
      (a : Aut (FiniteEtale.fiber b)), (∀ t, Commute a t) →
      a • (FiniteEtale.fiberObjEquivHom b A).symm (Over.homMk lift hb) =
        (FiniteEtale.fiberObjEquivHom b A).symm (Over.homMk lift hb) := by
    intro b hb
    cases hb
    intro a ha
    let p : (FiniteEtale.fiber (X := X) (lift ≫ A.hom)).obj A :=
      FiniteEtale.liftedFiberPoint A lift
    let σ : Aut A := (evaluationEquivOfIsGalois (C := FiniteEtale X)
      (FiniteEtale.fiber (X := X) (lift ≫ A.hom)) A p).symm (a • p)
    have hs : (FiniteEtale.fiber (X := X) (lift ≫ A.hom)).map σ.hom p = a • p :=
      evaluationEquivOfIsGalois_symm_fiber (C := FiniteEtale X)
        (FiniteEtale.fiber (X := X) (lift ≫ A.hom)) A p (a • p)
    have hσ : σ = 1 := hfaithful A lift σ
      (fun C _ c => constantH1Pullback_deck_eq_self_of_centralizes
        A lift σ a hs
          (fun t => ha (FiniteEtale.fundamentalGroupHom A.hom lift t)) C c)
    rw [hσ] at hs
    change (FiniteEtale.fiber (X := X) (lift ≫ A.hom)).map (𝟙 A) p = a • p at hs
    rw [CategoryTheory.Functor.map_id] at hs
    exact hs.symm
  have h := hfix geom hbase g hc
  rw [hx] at h
  exact h

end EtaleFundamentalGroups.Cohomology
