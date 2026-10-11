/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Cohomology.FiniteAbelianSheaf
import Mathlib.CategoryTheory.Sites.Point.Basic
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Group.Hom.Instances
import Mathlib.Topology.Algebra.MulAction

/-!
# Additive stalk comparison for finite abelian monodromy

The actual geometric stalk of the descended abelian sheaf is additively
isomorphic to the original finite representation. Naturality for both
projections and their sum proves compatibility with addition.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace EtaleFundamentalGroups.Cohomology

variable {X : Scheme.{u}} {Ω : Type u} [Field Ω] [IsSepClosed Ω]
  (ξ : Spec (.of Ω) ⟶ X)

private lemma abelianStalk_map_add
    {F H : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}} (f g : F ⟶ H) :
    (Scheme.pointSmallEtale ξ).sheafFiber.map (f + g) =
      (Scheme.pointSmallEtale ξ).sheafFiber.map f +
        (Scheme.pointSmallEtale ξ).sheafFiber.map g := by
  apply (Scheme.pointSmallEtale ξ).presheafFiber_hom_ext
  intro U x
  change (Scheme.pointSmallEtale ξ).toPresheafFiber U x F.obj ≫
      (Scheme.pointSmallEtale ξ).presheafFiber.map (f.hom + g.hom) =
    (Scheme.pointSmallEtale ξ).toPresheafFiber U x F.obj ≫
      ((Scheme.pointSmallEtale ξ).presheafFiber.map f.hom +
        (Scheme.pointSmallEtale ξ).presheafFiber.map g.hom)
  simp only [GrothendieckTopology.Point.toPresheafFiber_naturality,
    Preadditive.comp_add, Preadditive.add_comp, NatTrans.app_add]

variable [ConnectedSpace X]
  (M : Type u) [AddCommGroup M] [Fintype M]
  [DistribMulAction (Aut (FiniteEtale.fiber ξ)) M]
  [TopologicalSpace M] [DiscreteTopology M]
  [ContinuousSMul (Aut (FiniteEtale.fiber ξ)) M]

/-- The actual stalk comparison respects addition in the finite representation. -/
theorem finiteAbelianMonodromyStalkEquiv_add
    (x y : (Scheme.pointSmallEtale ξ).sheafFiber (A := AddCommGrpCat.{u}) |>.obj
      (finiteAbelianMonodromySheaf ξ M)) :
    finiteAbelianMonodromyStalkEquiv ξ M (x + y) =
      finiteAbelianMonodromyStalkEquiv ξ M x +
        finiteAbelianMonodromyStalkEquiv ξ M y := by
  let Φ := (Scheme.pointSmallEtale ξ).sheafFiber (A := AddCommGrpCat.{u})
  let e := finiteAbelianMonodromyStalkEquiv ξ M
  let eP := finiteAbelianMonodromyStalkEquiv ξ (M × M)
  let z := eP.symm (e x, e y)
  let p := AddMonoidHom.fst M M
  let q := AddMonoidHom.snd M M
  have hp : ∀ (g : Aut (FiniteEtale.fiber ξ)) (w : M × M), p (g • w) = g • p w :=
    fun _ _ => rfl
  have hq : ∀ (g : Aut (FiniteEtale.fiber ξ)) (w : M × M), q (g • w) = g • q w :=
    fun _ _ => rfl
  let f := finiteAbelianMonodromySheafMap ξ (M × M) M p hp
  let g := finiteAbelianMonodromySheafMap ξ (M × M) M q hq
  have hx : Φ.map f z = x := e.injective
    ((finiteAbelianMonodromyStalkEquiv_map ξ (M × M) M p hp z).trans
      (congrArg Prod.fst (eP.apply_symm_apply (e x, e y))))
  have hy : Φ.map g z = y := e.injective
    ((finiteAbelianMonodromyStalkEquiv_map ξ (M × M) M q hq z).trans
      (congrArg Prod.snd (eP.apply_symm_apply (e x, e y))))
  have hxy : Φ.map (f + g) z = x + y := by
    rw [abelianStalk_map_add]
    change Φ.map f z + Φ.map g z = x + y
    rw [hx, hy]
  let hsum := fun γ w =>
    (congrArg₂ (· + ·) (hp γ w) (hq γ w)).trans (smul_add γ (p w) (q w)).symm
  have hs := finiteAbelianMonodromyStalkEquiv_map ξ (M × M) M (p + q) hsum z
  rw [finiteAbelianMonodromySheafMap_add] at hs
  change e (Φ.map (f + g) z) = (eP z).1 + (eP z).2 at hs
  rw [hxy] at hs
  exact hs.trans (congrArg (fun w : M × M => w.1 + w.2)
    (eP.apply_symm_apply (e x, e y)))

/-- The actual geometric stalk is the original finite abelian representation,
as an abelian group rather than merely as a finite set. -/
def finiteAbelianMonodromyStalkAddEquiv :
    ((Scheme.pointSmallEtale ξ).sheafFiber (A := AddCommGrpCat.{u}) |>.obj
      (finiteAbelianMonodromySheaf ξ M)) ≃+ M where
  __ := finiteAbelianMonodromyStalkEquiv ξ M
  map_add' := finiteAbelianMonodromyStalkEquiv_add ξ M

end EtaleFundamentalGroups.Cohomology
