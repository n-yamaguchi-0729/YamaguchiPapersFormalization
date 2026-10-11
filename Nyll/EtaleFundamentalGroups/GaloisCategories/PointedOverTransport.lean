/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.GaloisCategories.PointedOver
import Nyll.EtaleFundamentalGroups.GaloisCategories.FiberIso

/-!
# Monodromy transport on pointed covers

An actual automorphism of a finite fiber functor transports fibers over a
point to fibers over its translate. Under the existing stabilizer comparison,
this transport is conjugation by that same automorphism.
-/

noncomputable section

universe u v w

open CategoryTheory

namespace CategoryTheory.PreGaloisCategory

variable {C : Type u} [Category.{v} C]
variable (F : C ⥤ FintypeCat.{w}) [PreGaloisCategory C] [FiberFunctor F]
variable {X : C} (x : F.obj X) (g : Aut F)

private def fiberOverOrbitEquiv (U : Over X) :
    (fiberOver F x).obj U ≃ (fiberOver F (g • x)).obj U where
  toFun z := ⟨g • z.1, by
    exact ((mulAction_naturality F g U.hom z.1).symm).trans
      (congrArg (g • ·) z.2)⟩
  invFun z := ⟨g⁻¹ • z.1, by
    exact ((mulAction_naturality F g⁻¹ U.hom z.1).symm).trans
      ((congrArg (g⁻¹ • ·) z.2).trans (inv_smul_smul g x))⟩
  left_inv z := by
    apply Subtype.ext
    exact inv_smul_smul g z.1
  right_inv z := by
    apply Subtype.ext
    exact smul_inv_smul g z.1

/-- Transport in the actual fibers of objects over a cover. -/
def fiberOverOrbitIso : fiberOver F x ≅ fiberOver F (g • x) :=
  NatIso.ofComponents
    (fun U => FintypeCat.equivEquivIso (fiberOverOrbitEquiv F x g U))
    (fun f => by
      apply FintypeCat.hom_ext
      intro z
      apply Subtype.ext
      exact mulAction_naturality F g f.left z.1)

/-- Conjugation sends the stabilizer of a point into the stabilizer of its translate. -/
def orbitStabilizerConjugate (a : MulAction.stabilizer (Aut F) x) :
    MulAction.stabilizer (Aut F) (g • x) :=
  ⟨g * a.1 * g⁻¹, by
    change (g * a.1 * g⁻¹) • (g • x) = g • x
    rw [mul_smul, mul_smul, inv_smul_smul, a.2]⟩

omit [PreGaloisCategory C] [FiberFunctor F] in
/-- Fiber transport acts on restricted automorphisms by actual conjugation. -/
theorem fiberOverOrbitIso_conj_restrict
    (a : MulAction.stabilizer (Aut F) x) :
    continuousConjAut (fiberOverOrbitIso F x g)
        (restrictAutToFiberOver F x a) =
      restrictAutToFiberOver F (g • x) (orbitStabilizerConjugate F x g a) := by
  apply Aut.ext
  ext U z
  apply Subtype.ext
  change g • (a.1 • (g⁻¹ • z.1)) = (g * a.1 * g⁻¹) • z.1
  rw [mul_smul, mul_smul]

/-- The established stabilizer identification intertwines fiber transport
and conjugation in the ambient automorphism group. -/
theorem autFiberOverEquivStabilizer_orbit
    (a : Aut (fiberOver F x)) :
    autFiberOverEquivStabilizer F (g • x)
        (continuousConjAut (fiberOverOrbitIso F x g) a) =
      orbitStabilizerConjugate F x g
        (autFiberOverEquivStabilizer F x a) := by
  have ha : restrictAutToFiberOver F x
      (autFiberOverEquivStabilizer F x a) = a :=
    (autFiberOverMulEquivStabilizer F x).symm_apply_apply a
  have hc := fiberOverOrbitIso_conj_restrict F x g
    (autFiberOverEquivStabilizer F x a)
  rw [ha] at hc
  exact (congrArg (autFiberOverEquivStabilizer F (g • x)) hc).trans
    ((autFiberOverMulEquivStabilizer F (g • x)).apply_symm_apply _)

end CategoryTheory.PreGaloisCategory
