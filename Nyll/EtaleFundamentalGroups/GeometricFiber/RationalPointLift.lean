/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.GeometricFiber.FundamentalGroup
import Nyll.EtaleFundamentalGroups.GeometricFiber.Functoriality
import Mathlib.AlgebraicGeometry.AlgClosed.Basic

/-! # Actual rational and closed points above points of a finite étale cover -/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry.FiniteEtale

universe u

/-- A nonempty finite étale cover of a connected scheme has a rational
point over each geometric point with algebraically closed residue field. -/
theorem exists_rationalPoint_lift
    {K : Type u} [Field K] [IsAlgClosed K]
    {X : Scheme.{u}} [PreconnectedSpace X]
    (W : FiniteEtale X) [Nonempty W.left]
    (x : Spec (.of K) ⟶ X) :
    ∃ y : Spec (.of K) ⟶ W.left, y ≫ W.hom = x := by
  have : IsFiniteEtale W.hom := W.2
  have : PreconnectedSpace ↑((Functor.fromPUnit X).obj W.right) :=
    inferInstanceAs (PreconnectedSpace X)
  have : Nonempty ((Functor.id Scheme).obj W.left) :=
    inferInstanceAs (Nonempty W.left)
  have : Surjective W.hom := IsFiniteEtale.surjective W.hom
  obtain ⟨y₀, hy₀⟩ := W.hom.surjective (x (IsLocalRing.closedPoint K))
  obtain ⟨z, _, _⟩ := Scheme.Pullback.exists_preimage_pullback
    (f := W.hom) (g := x) y₀ (IsLocalRing.closedPoint K) hy₀
  let y := fiberObjEquivHom x W z
  exact ⟨y.left, y.w⟩

/-- For a curve over an algebraically closed field, a finite étale cover
has an actual closed point over every closed point of the base. -/
theorem exists_closedPoint_above
    {K : Type u} [Field K] [IsAlgClosed K]
    {X : Scheme.{u}} [PreconnectedSpace X]
    (c : X ⟶ Spec (.of K)) [LocallyOfFiniteType c]
    (W : FiniteEtale X) [Nonempty W.left] (x : closedPoints X) :
    ∃ y : closedPoints W.left, W.hom y.val = x.val := by
  let p := pointOfClosedPoint c x.val x.property
  obtain ⟨q, hq⟩ := exists_rationalPoint_lift W p
  have : IsFiniteEtale W.hom := W.2
  let cY := W.hom ≫ c
  have : LocallyOfFiniteType cY := by dsimp only [cY]; infer_instance
  have hqbase : q ≫ cY = 𝟙 _ := by
    dsimp only [cY]
    rw [← Category.assoc, hq]
    exact pointOfClosedPoint_comp c x.val x.property
  refine ⟨pointEquivClosedPoint cY ⟨q, hqbase⟩, ?_⟩
  change W.hom (q (IsLocalRing.closedPoint K)) = x.val
  have h := congrArg (fun t : Spec (.of K) ⟶ X => t (IsLocalRing.closedPoint K)) hq
  exact h.trans (pointOfClosedPoint_apply c x.val x.property _)

end AlgebraicGeometry.FiniteEtale
