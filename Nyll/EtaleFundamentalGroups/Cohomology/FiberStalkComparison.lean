/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Cohomology.ExtensionFibers
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.AlgebraicGeometry.Sites.EtalePoint
import Mathlib.CategoryTheory.Limits.Connected
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks
import Mathlib.CategoryTheory.Limits.Types.Pullbacks
import Mathlib.CategoryTheory.Sites.Point.Basic

/-!
# The geometric stalk of an extension fiber

The sheaf of lifts is the actual pullback over the chosen quotient section.
Since geometric stalks preserve finite limits, its stalk is the fiber of the
stalk homomorphism. The comparison uses the forgetful functor's filtered
colimit comparison, preserving the original abelian group structures.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace EtaleFundamentalGroups.Cohomology

variable {X : Scheme.{u}}
  (S : ShortComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}))
  (t : (Functor.const X.Etaleᵒᵖ).obj PUnit ⟶ S.X₃.obj ⋙ forget AddCommGrpCat.{u})

private abbrev fiberInclusion := (extensionFiberSubfunctor S t).ι

private def fiberToPoint :
    (extensionFiber S t).obj ⟶ (Functor.const X.Etaleᵒᵖ).obj PUnit where
  app _ := ↾fun _ => PUnit.unit

private theorem fiber_square :
    fiberInclusion S t ≫ Functor.whiskerRight S.g.hom (forget AddCommGrpCat.{u}) =
      fiberToPoint S t ≫ t := by
  ext U e
  exact e.property

private abbrev fiberCone :
    PullbackCone (Functor.whiskerRight S.g.hom (forget AddCommGrpCat.{u})) t :=
  PullbackCone.mk (fiberInclusion S t) (fiberToPoint S t) (fiber_square S t)

private def fiberConeIsLimit : IsLimit (fiberCone S t) := by
  refine PullbackCone.IsLimit.mk (fiber_square S t) ?_ ?_ ?_ ?_
  · intro c
    exact
      { app := fun U => ↾fun a => ⟨c.fst.app U a, by
          have h := congrArg
            (fun f : c.pt ⟶ S.X₃.obj ⋙ forget AddCommGrpCat.{u} => f.app U a) c.condition
          exact h.trans (congrArg (t.app U) (Subsingleton.elim _ PUnit.unit))⟩
        naturality := fun U V f => by
          apply ConcreteCategory.hom_ext
          intro a
          apply Subtype.ext
          exact ConcreteCategory.congr_hom (c.fst.naturality f) a }
  · intro c
    rfl
  · intro c
    ext U a
    change PUnit.unit = c.snd.app U a
    exact Subsingleton.elim _ _
  · intro c m hm _
    ext U a
    apply Subtype.ext
    exact congrArg
      (fun f : c.pt ⟶ S.X₂.obj ⋙ forget AddCommGrpCat.{u} => f.app U a) hm

variable {Ω : Type u} [Field Ω] [IsSepClosed Ω] (ξ : Spec (.of Ω) ⟶ X)

private def constantUnitPresheafStalkIso :
    (Scheme.pointSmallEtale ξ).presheafFiber.obj
      ((Functor.const X.Etaleᵒᵖ).obj PUnit.{u + 1}) ≅ PUnit.{u + 1} :=
  (colimit.isColimit _).coconePointUniqueUpToIso
    (isColimitConstCocone (Scheme.pointSmallEtale ξ).fiber.Elementsᵒᵖ PUnit.{u + 1})

private def quotientSectionSetStalk :
    (Scheme.pointSmallEtale ξ).presheafFiber.obj (S.X₃.obj ⋙ forget AddCommGrpCat.{u}) :=
  (Scheme.pointSmallEtale ξ).presheafFiber.map t
    ((constantUnitPresheafStalkIso ξ).inv PUnit.unit)

private def fiberSetStalkEquiv :
    (Scheme.pointSmallEtale ξ).sheafFiber.obj (extensionFiber S t) ≃
      {b : (Scheme.pointSmallEtale ξ).presheafFiber.obj
        (S.X₂.obj ⋙ forget AddCommGrpCat.{u}) //
        (Scheme.pointSmallEtale ξ).presheafFiber.map
          (Functor.whiskerRight S.g.hom (forget AddCommGrpCat.{u})) b =
            quotientSectionSetStalk S t ξ} := by
  let Φ := (Scheme.pointSmallEtale ξ).presheafFiber (A := Type u)
  let e := constantUnitPresheafStalkIso ξ
  let p := Φ.map (Functor.whiskerRight S.g.hom (forget AddCommGrpCat.{u}))
  let q := Φ.map t
  let h := (PullbackCone.isLimitMapConeEquiv (fiberCone S t) Φ).toFun
    (isLimitOfPreserves Φ (fiberConeIsLimit S t))
  refine (PullbackCone.IsLimit.equivPullbackObj h).trans
    { toFun := fun b => ⟨b.val.1, b.property.trans (congrArg q ?_)⟩
      invFun := fun b => ⟨(b.val, e.inv PUnit.unit), b.property⟩
      left_inv := ?_
      right_inv := ?_ }
  · exact e.toEquiv.injective (Subsingleton.elim _ _)
  · intro b
    apply Subtype.ext
    exact Prod.ext rfl (e.toEquiv.injective (Subsingleton.elim _ _))
  · intro b
    rfl

/-- The chosen global quotient section, evaluated in the actual abelian stalk. -/
def quotientSectionStalk :
    (Scheme.pointSmallEtale ξ).sheafFiber (A := AddCommGrpCat.{u}) |>.obj S.X₃ :=
  ((Scheme.pointSmallEtale ξ).sheafFiberCompIso (forget AddCommGrpCat.{u})).hom.app S.X₃
    (quotientSectionSetStalk S t ξ)

/-- Taking the geometric stalk commutes with taking the actual extension fiber. -/
def extensionFiberStalkEquiv :
    (Scheme.pointSmallEtale ξ).sheafFiber.obj (extensionFiber S t) ≃
      {b : (Scheme.pointSmallEtale ξ).sheafFiber (A := AddCommGrpCat.{u}) |>.obj S.X₂ //
        (Scheme.pointSmallEtale ξ).sheafFiber.map S.g b = quotientSectionStalk S t ξ} := by
  let Φ := Scheme.pointSmallEtale ξ
  let e := Φ.sheafFiberCompIso (forget AddCommGrpCat.{u})
  have hn (b : Φ.presheafFiber.obj (S.X₂.obj ⋙ forget AddCommGrpCat.{u})) :
      Φ.sheafFiber.map S.g (e.hom.app S.X₂ b) =
        e.hom.app S.X₃ (Φ.presheafFiber.map
          (Functor.whiskerRight S.g.hom (forget AddCommGrpCat.{u})) b) :=
    (ConcreteCategory.congr_hom (e.hom.naturality S.g) b).symm
  refine (fiberSetStalkEquiv S t ξ).trans
    { toFun := fun b => ⟨e.hom.app S.X₂ b.val,
        (hn b.val).trans (congrArg (e.hom.app S.X₃) b.property)⟩
      invFun := fun b => ⟨e.inv.app S.X₂ b.val, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · apply (e.app S.X₃).toEquiv.injective
    exact (hn (e.inv.app S.X₂ b.val)).symm.trans
      ((congrArg (Φ.sheafFiber.map S.g) ((e.app S.X₂).inv_hom_id_apply b.val)).trans
        b.property)
  · intro b
    exact Subtype.ext ((e.app S.X₂).hom_inv_id_apply b.val)
  · intro b
    exact Subtype.ext ((e.app S.X₂).inv_hom_id_apply b.val)

/-- On a representative germ the comparison is the canonical map into the
original abelian stalk, applied to the original section. -/
theorem extensionFiberStalkEquiv_toFiber (U : X.Etale)
    (x : (Scheme.pointSmallEtale ξ).fiber.obj U)
    (e : (extensionFiber S t).obj.obj (op U)) :
    (extensionFiberStalkEquiv S t ξ
      ((Scheme.pointSmallEtale ξ).toPresheafFiber U x (extensionFiber S t).obj e)).val =
      (Scheme.pointSmallEtale ξ).toPresheafFiber U x S.X₂.obj e.val := by
  let Φ := Scheme.pointSmallEtale ξ
  have hc (q : Φ.presheafFiber.obj (extensionFiber S t).obj) :
      (extensionFiberStalkEquiv S t ξ q).val =
        (Φ.presheafFiberCompIso (forget AddCommGrpCat.{u})).hom.app S.X₂.obj
          (Φ.presheafFiber.map (fiberInclusion S t) q) := by
    let K := Φ.presheafFiber (A := Type u)
    let h := (PullbackCone.isLimitMapConeEquiv (fiberCone S t) K).toFun
      (isLimitOfPreserves K (fiberConeIsLimit S t))
    exact congrArg
      ((Φ.presheafFiberCompIso (forget AddCommGrpCat.{u})).hom.app S.X₂.obj)
      (PullbackCone.IsLimit.equivPullbackObj_apply_fst h q)
  rw [hc]
  have hn := Φ.toPresheafFiber_naturality_apply (fiberInclusion S t) U x e
  change Φ.presheafFiber.map (fiberInclusion S t)
    (Φ.toPresheafFiber U x (extensionFiber S t).obj e) =
      Φ.toPresheafFiber U x (S.X₂.obj ⋙ forget AddCommGrpCat.{u}) e.val at hn
  rw [hn]
  exact ConcreteCategory.congr_hom
    (Φ.toPresheafFiber_presheafFiberCompIso_hom_app
      (forget AddCommGrpCat.{u}) U x S.X₂.obj) e.val

end EtaleFundamentalGroups.Cohomology
