/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleCohomology.Constructible.Monodromy
import Nyll.EtaleFundamentalGroups.Cohomology.FiniteAbelianStalk

/-!
# The actual monodromy of a descended finite representation

The unit of finite étale representability identifies the monodromy of a
represented sheaf with the original geometric fiber. Its comparison with
the actual stalk is the existing represented-sheaf stalk comparison.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.PreGaloisCategory EtaleCohomology
open scoped FintypeCatDiscrete

universe u

namespace EtaleFundamentalGroups.Cohomology

variable {X : Scheme.{u}} [ConnectedSpace X]
  {Ω : Type u} [Field Ω] [IsSepClosed Ω] (ξ : Spec (.of Ω) ⟶ X)

/-- Monodromy of the sheaf represented by a finite étale cover is the actual
geometric fiber action of that cover. -/
def representedMonodromyIso (V : FiniteEtale X) :
    (finiteLocallyConstantSetMonodromy ξ).functor.obj
        ((finiteEtaleEquivFiniteLocallyConstantSetSheaf X).functor.obj V) ≅
      (functorToContAction (FiniteEtale.fiber ξ)).obj V :=
  ((functorToContAction (FiniteEtale.fiber ξ)).mapIso
    ((finiteEtaleEquivFiniteLocallyConstantSetSheaf X).unitIso.app V)).symm

/-- The monodromy isomorphism agrees with the actual geometric stalk
comparison, by naturality and the unit-counit identity. -/
theorem representedMonodromyIso_stalk (V : FiniteEtale X)
    (q : ((finiteLocallyConstantSetMonodromy ξ).functor.obj
      ((finiteEtaleEquivFiniteLocallyConstantSetSheaf X).functor.obj V)).obj.V) :
    (finiteEtaleSheafFiberIso ξ).hom.app V
      ((finiteLocallyConstantSetMonodromyStalkIso ξ).hom.app
        ((finiteEtaleEquivFiniteLocallyConstantSetSheaf X).functor.obj V) q) =
      (representedMonodromyIso ξ V).hom.hom.hom q := by
  let e := finiteEtaleEquivFiniteLocallyConstantSetSheaf X
  let L := finiteEtaleSheafFiberIso ξ
  let Φ := (Scheme.pointSmallEtale ξ).sheafFiber (A := Type u)
  let I := ObjectProperty.ι (IsEtaleFiniteLocallyConstantSet (X := X))
  have he : (e.counitIso.hom.app (e.functor.obj V)).hom =
      (finiteEtaleSheaf X).map (e.unitIso.inv.app V) :=
    congrArg (fun f => I.map f) (e.counit_app_functor V)
  change L.hom.app V
    (Φ.map (e.counitIso.hom.app (e.functor.obj V)).hom
      (L.inv.app (e.inverse.obj (e.functor.obj V)) q)) =
    (FiniteEtale.fiber ξ).map (e.unitIso.inv.app V) q
  rw [he]
  have hn := ConcreteCategory.congr_hom (L.hom.naturality (e.unitIso.inv.app V))
    (L.inv.app (e.inverse.obj (e.functor.obj V)) q)
  exact hn.trans (congrArg ((FiniteEtale.fiber ξ).map (e.unitIso.inv.app V))
    ((L.app (e.inverse.obj (e.functor.obj V))).toEquiv.apply_symm_apply q))

variable (M : Type u) [AddCommGroup M] [Fintype M]
  [DistribMulAction (Aut (FiniteEtale.fiber ξ)) M]
  [TopologicalSpace M] [DiscreteTopology M]
  [ContinuousSMul (Aut (FiniteEtale.fiber ξ)) M]

/-- The geometric fiber comparison of the descended cover is equivariant
for the original fundamental-group action. -/
theorem finiteAbelianCoverFiberEquiv_smul (g : Aut (FiniteEtale.fiber ξ))
    (x : (FiniteEtale.fiber ξ).obj (finiteAbelianCover ξ M)) :
    finiteAbelianCoverFiberEquiv ξ M (g • x) =
      g • finiteAbelianCoverFiberEquiv ξ M x :=
  ConcreteCategory.congr_hom
    (((functorToContAction (FiniteEtale.fiber ξ)).asEquivalence.counitIso.app
      (finiteAbelianSetAction ξ M)).hom.hom.comm g) x

end EtaleFundamentalGroups.Cohomology
