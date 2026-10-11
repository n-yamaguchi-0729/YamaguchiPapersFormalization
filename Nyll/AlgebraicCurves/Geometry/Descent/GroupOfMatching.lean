/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.Geometry.Descent.RepresentableMatching
import Nyll.AlgebraicCurves.Geometry.Picard.RelativeGroupLawGrpObj
import Mathlib.Algebra.Category.Grp.Basic
import Mathlib.Algebra.Group.Subgroup.Basic

/-!
# Commutative group laws on effective descents

Matching local elements form a subgroup. The actual matching equivalence transports
its operations to relative points of the descended scheme.
-/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open NeronModelInfra GoodReductionJacobian

noncomputable section

namespace AlgebraicGeometry.DescentAction

variable {S S' : Scheme.{u}} (s : S' ⟶ S) (G : (Over S)ᵒᵖ ⥤ CommGrpCat.{u + 1})

/-- The subgroup of local elements satisfying the descent matching condition. -/
def matchingSubgroup (T : Over S) :
    Subgroup (G.obj (op ((Over.map s).obj ((Over.pullback s).obj T)))) where
  carrier := {z | Matching s (G ⋙ forget CommGrpCat) T z}
  one_mem' := by
    intro W g₁ g₂ _
    change (G.map g₁.op) 1 = (G.map g₂.op) 1
    rw [map_one, map_one]
  mul_mem' := by
    intro x y hx hy W g₁ g₂ hg
    change (G.map g₁.op) (x * y) = (G.map g₂.op) (x * y)
    rw [map_mul, map_mul]
    exact congrArg₂ (· * ·) (hx g₁ g₂ hg) (hy g₁ g₂ hg)
  inv_mem' := by
    intro x hx W g₁ g₂ hg
    change (G.map g₁.op) x⁻¹ = (G.map g₂.op) x⁻¹
    rw [map_inv, map_inv]
    exact congrArg Inv.inv (hx g₁ g₂ hg)

variable {X' : Scheme.{u}} (x' : X' ⟶ S')
  (hX' : ((Over.map s).op ⋙ G ⋙ forget CommGrpCat).RepresentableBy (Over.mk x'))
  {X : Scheme.{u}} (f : X ⟶ S) (e : pullback f s ≅ X')
  (he : e.hom ≫ x' = pullback.snd f s)
  (hcompat : eRel s x' f e he ≫ repAct s (G ⋙ forget CommGrpCat) x' hX' =
    (canonical s f).act ≫ e.hom)

theorem localPoint_comp {T U : Over S} (φ : U ⟶ T) (m : T ⟶ Over.mk f) :
    localPoint s (G ⋙ forget CommGrpCat) x' hX' f e he (φ ≫ m) =
      G.map ((Over.map s).map ((Over.pullback s).map φ)).op
        (localPoint s (G ⋙ forget CommGrpCat) x' hX' f e he m) := by
  change hX'.homEquiv (bc s x' f e he (φ ≫ m)) =
    G.map ((Over.map s).map ((Over.pullback s).map φ)).op
      (hX'.homEquiv (bc s x' f e he m))
  rw [bc, Functor.map_comp, Category.assoc, hX'.homEquiv_comp]
  rfl

section affineBase

variable {R : Type u} [CommRing R]
  {S' : Scheme.{u}} (s : S' ⟶ Spec (CommRingCat.of R))
  (G : (Over (Spec (CommRingCat.of R)))ᵒᵖ ⥤ CommGrpCat.{u + 1})
  {X' : Scheme.{u}} (x' : X' ⟶ S')
  (hX' : ((Over.map s).op ⋙ G ⋙ forget CommGrpCat).RepresentableBy (Over.mk x'))
  {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) (e : pullback f s ≅ X')
  (he : e.hom ≫ x' = pullback.snd f s)
  (hcompat : eRel s x' f e he ≫ repAct s (G ⋙ forget CommGrpCat) x' hX' =
    (canonical s f).act ≫ e.hom)
  [∀ T : Over (Spec (CommRingCat.of R)), EffectiveEpi (pullback.fst T.hom s)]

/-- Relative scheme points identified with the subgroup of matching local elements. -/
def matchingPointEquiv {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) :
    SchemeHomOver t f ≃ matchingSubgroup s G (Over.mk t) :=
  (overHomEquivSchemeHomOver (Over.mk t) f).symm.trans
    (matchingEquiv s (G ⋙ forget CommGrpCat) x' hX' f e he hcompat)

theorem matchingPointEquiv_apply_val {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver t f) :
    (matchingPointEquiv s G x' hX' f e he hcompat t x).1 =
      localPoint s (G ⋙ forget CommGrpCat) x' hX' f e he (schemeHomOverToOverHom x) := rfl

theorem matchingPointEquiv_comp {T T' : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) (t' : T' ⟶ Spec (CommRingCat.of R))
    (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (x : SchemeHomOver t f) :
    (matchingPointEquiv s G x' hX' f e he hcompat t'
      (schemeHomOverComp ψ hψ x)).1 =
      G.map ((Over.map s).map ((Over.pullback s).map (Over.homMk ψ hψ : Over.mk t' ⟶ Over.mk t))).op
        (matchingPointEquiv s G x' hX' f e he hcompat t x).1 := by
  rw [matchingPointEquiv_apply_val, matchingPointEquiv_apply_val]
  have hm : schemeHomOverToOverHom (schemeHomOverComp ψ hψ x) =
      Over.homMk ψ hψ ≫ schemeHomOverToOverHom x := by
    ext
    rfl
  rw [hm]
  exact localPoint_comp s G x' hX' f e he
    (T := Over.mk t) (U := Over.mk t')
    (Over.homMk ψ hψ : Over.mk t' ⟶ Over.mk t) (schemeHomOverToOverHom x)

/-- The relative group law obtained by effective descent of a group-valued presheaf. -/
def relativeGroupLawOfMatching : RelativeGroupLaw R f where
  mul t x y :=
    (matchingPointEquiv s G x' hX' f e he hcompat t).symm
      (matchingPointEquiv s G x' hX' f e he hcompat t x *
        matchingPointEquiv s G x' hX' f e he hcompat t y)
  one t := (matchingPointEquiv s G x' hX' f e he hcompat t).symm 1
  inv t x :=
    (matchingPointEquiv s G x' hX' f e he hcompat t).symm
      (matchingPointEquiv s G x' hX' f e he hcompat t x)⁻¹
  mul_assoc t x y z := by
    apply (matchingPointEquiv s G x' hX' f e he hcompat t).injective
    simp only [Equiv.apply_symm_apply, mul_assoc]
  one_mul t x := by
    apply (matchingPointEquiv s G x' hX' f e he hcompat t).injective
    simp only [Equiv.apply_symm_apply, one_mul]
  mul_one t x := by
    apply (matchingPointEquiv s G x' hX' f e he hcompat t).injective
    simp only [Equiv.apply_symm_apply, mul_one]
  inv_mul_cancel t x := by
    apply (matchingPointEquiv s G x' hX' f e he hcompat t).injective
    simp only [Equiv.apply_symm_apply, inv_mul_cancel]
  mul_natural t t' ψ hψ x y := by
    apply (matchingPointEquiv s G x' hX' f e he hcompat t').injective
    apply Subtype.ext
    rw [matchingPointEquiv_comp]
    simp only [Equiv.apply_symm_apply, Subgroup.coe_mul, map_mul]
    rw [matchingPointEquiv_comp, matchingPointEquiv_comp]

theorem relativeGroupLawOfMatching_commutative :
    (relativeGroupLawOfMatching s G x' hX' f e he hcompat).IsCommutative := by
  intro T t x y
  change (matchingPointEquiv s G x' hX' f e he hcompat t).symm (_ * _) =
    (matchingPointEquiv s G x' hX' f e he hcompat t).symm (_ * _)
  rw [mul_comm]

end affineBase

end AlgebraicGeometry.DescentAction
