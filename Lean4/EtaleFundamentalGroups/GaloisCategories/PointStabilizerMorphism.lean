/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.CategoryTheory.Galois.Full

/-!
# Realizing inclusion of actual point stabilizers

For connected objects, inclusion of the actual stabilizers of two fiber
points gives a morphism taking the first point to the second. The map is
constructed as an equivariant map and lifted by the full fiber-action functor.
No equality between a proposed geometric morphism and subgroup inclusion is
assumed. The fiber and category universes may differ.
-/

noncomputable section

universe u v w

open CategoryTheory

namespace CategoryTheory.PreGaloisCategory

/-- Realize an inclusion of actual point stabilizers by a pointed morphism. -/
theorem exists_hom_of_pointStabilizer_le
    {C : Type u} [Category.{v} C] [GaloisCategory C]
    (F : C ⥤ FintypeCat.{w}) [FiberFunctor F]
    (A B : C) [IsConnected A] (x : F.obj A) (y : F.obj B)
    (hxy : MulAction.stabilizer (Aut F) x ≤ MulAction.stabilizer (Aut F) y) :
    ∃ f : A ⟶ B, F.map f x = y := by
  classical
  have htrans (z : F.obj A) : ∃ g : Aut F, g • x = z :=
    MulAction.exists_smul_eq (Aut F) x z
  let t (z : F.obj A) : Aut F := Classical.choose (htrans z)
  have ht (z : F.obj A) : t z • x = z := Classical.choose_spec (htrans z)
  have hcompat (g h : Aut F) (heq : g • x = h • x) : g • y = h • y := by
    have hx : (h⁻¹ * g) • x = x := by
      rw [mul_smul, heq, inv_smul_smul]
    have hy : (h⁻¹ * g) • y = y := hxy hx
    calc
      g • y = h • ((h⁻¹ * g) • y) := by
        rw [smul_smul, mul_inv_cancel_left]
      _ = h • y := congrArg (h • ·) hy
  let m : F.obj A → F.obj B := fun z => t z • y
  have hm : m x = y := by
    change t x • y = y
    exact hxy (ht x)
  have hcomm (g : Aut F) (z : F.obj A) : m (g • z) = g • m z := by
    change t (g • z) • y = g • (t z • y)
    rw [← mul_smul]
    apply hcompat
    exact (ht (g • z)).trans
      ((congrArg (g • ·) (ht z)).symm.trans (mul_smul g (t z) x).symm)
  let p : (functorToAction F).obj A ⟶ (functorToAction F).obj B :=
    { hom := FintypeCat.homMk m
      comm := fun g => FintypeCat.hom_ext _ _ (fun z => hcomm g z) }
  let f : A ⟶ B := (functorToAction F).preimage p
  have hp : (functorToAction F).map f = p :=
    (functorToAction F).map_preimage p
  refine ⟨f, ?_⟩
  exact (congrArg (fun q : (functorToAction F).obj A ⟶
    (functorToAction F).obj B => q.hom x) hp).trans hm

end CategoryTheory.PreGaloisCategory
