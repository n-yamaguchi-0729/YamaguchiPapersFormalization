/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Cohomology.ExtensionMonodromy
import Nyll.EtaleFundamentalGroups.Cohomology.RepresentedMonodromy

/-!
# Evaluating extension monodromy in a represented abelian sheaf

The actual sheaf of lifts maps to the middle term of the extension. A map
from that middle term to a descended finite representation therefore gives
an equivariant map on geometric monodromy. Its value is computed in the
original abelian stalk, retaining the original inclusion and coefficient.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite EtaleCohomology
open scoped FintypeCatDiscrete

universe u

namespace EtaleFundamentalGroups.Cohomology

variable {X : Scheme.{u}} [ConnectedSpace X] (A : AddCommGrpCat.{u}) [Finite A]
  {E Q : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}}
  (i : (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj A ⟶ E)
  (p : E ⟶ Q) (h : i ≫ p = 0) (hs : (ShortComplex.mk i p h).ShortExact)
  (t : (Functor.const X.Etaleᵒᵖ).obj PUnit ⟶ Q.obj ⋙ forget AddCommGrpCat.{u})
  {Ω : Type u} [Field Ω] [IsSepClosed Ω] (ξ : Spec (.of Ω) ⟶ X)

private abbrev lifts : EtaleFiniteLocallyConstantSetSheaf X :=
  ⟨extensionFiber (ShortComplex.mk i p h) t,
    extensionFiber_isFiniteLocallyConstant (ShortComplex.mk i p h) t hs
      (constantAbelian_isFiniteLocallyConstant X A)⟩

/-- A monodromy point of the lift sheaf, evaluated in the original middle stalk. -/
def extensionMonodromyEvaluation
    (q : (extensionMonodromy A i p h hs t ξ).obj.V) :
    (Scheme.pointSmallEtale ξ).sheafFiber (A := AddCommGrpCat.{u}) |>.obj E :=
  (extensionFiberStalkEquiv (ShortComplex.mk i p h) t ξ
    ((finiteLocallyConstantSetMonodromyStalkIso ξ).hom.app (lifts A i p h hs t) q)).val

/-- An evaluated monodromy point is represented by an actual local lift of
the specified quotient section. -/
theorem extensionMonodromyEvaluation_exists_germ
    (q : (extensionMonodromy A i p h hs t ξ).obj.V) :
    ∃ (U : X.Etale) (x : (Scheme.pointSmallEtale ξ).fiber.obj U)
      (a : E.obj.obj (op U)),
      extensionMonodromyEvaluation A i p h hs t ξ q =
        (Scheme.pointSmallEtale ξ).toPresheafFiber U x E.obj a ∧
      p.hom.app (op U) a = t.app (op U) PUnit.unit := by
  let Φ := Scheme.pointSmallEtale ξ
  obtain ⟨U, x, a, ha⟩ := Φ.toPresheafFiber_jointly_surjective
    (P := (extensionFiber (ShortComplex.mk i p h) t).obj)
    ((finiteLocallyConstantSetMonodromyStalkIso ξ).hom.app (lifts A i p h hs t) q)
  refine ⟨U, x, a.val, ?_, a.property⟩
  exact (congrArg (fun z => (extensionFiberStalkEquiv
    (ShortComplex.mk i p h) t ξ z).val) ha.symm).trans
      (extensionFiberStalkEquiv_toFiber (ShortComplex.mk i p h) t ξ U x a)

/-- Evaluation preserves translation by the actual constant coefficient. -/
theorem extensionMonodromyEvaluation_translation (a : Multiplicative A)
    (q : (extensionMonodromy A i p h hs t ξ).obj.V) :
    let := extensionMonodromyTorsor A i p h hs t ξ
    extensionMonodromyEvaluation A i p h hs t ξ (a • q) =
      (Scheme.pointSmallEtale ξ).sheafFiber.map i
        ((constantAbelianStalkIso ξ A).inv a.toAdd) +
      extensionMonodromyEvaluation A i p h hs t ξ q := by
  let S := (ShortComplex.mk i p h).map (Scheme.pointSmallEtale ξ).sheafFiber
  let z := quotientSectionStalk (ShortComplex.mk i p h) t ξ
  let e : (extensionMonodromy A i p h hs t ξ).obj.V ≃ abelianExtensionFiber S z :=
    ((finiteLocallyConstantSetMonodromyStalkIso ξ).app
    (lifts A i p h hs t)).toEquiv.trans
      (extensionFiberStalkEquiv (ShortComplex.mk i p h) t ξ)
  let T := extensionMonodromyTorsor A i p h hs t ξ
  change (e (a • q)).val = S.f ((constantAbelianStalkIso ξ A).inv a.toAdd) + (e q).val
  exact extensionFiberTransportTorsor_smul S (shortExact_geometricStalk ξ _ hs)
    z A (constantAbelianStalkIso ξ A).symm e a q

variable (M : Type u) [AddCommGroup M] [Fintype M]
  [DistribMulAction (Aut (FiniteEtale.fiber ξ)) M]
  [TopologicalSpace M] [DiscreteTopology M]
  [ContinuousSMul (Aut (FiniteEtale.fiber ξ)) M]
  (f : E ⟶ finiteAbelianMonodromySheaf ξ M)

private def representedLiftMap :
    lifts A i p h hs t ⟶
      (finiteEtaleEquivFiniteLocallyConstantSetSheaf X).functor.obj
        (finiteAbelianCover ξ M) :=
  ObjectProperty.homMk
    { hom := (extensionFiberSubfunctor (ShortComplex.mk i p h) t).ι ≫
        Functor.whiskerRight f.hom (forget AddCommGrpCat.{u}) }

private theorem representedLiftMap_stalk
    (q : (Scheme.pointSmallEtale ξ).sheafFiber.obj
      (extensionFiber (ShortComplex.mk i p h) t)) :
    ((Scheme.pointSmallEtale ξ).sheafFiberCompIso (forget AddCommGrpCat.{u})).hom.app
      (finiteAbelianMonodromySheaf ξ M)
      ((Scheme.pointSmallEtale ξ).sheafFiber.map
        (representedLiftMap A i p h hs t ξ M f).hom q) =
      (Scheme.pointSmallEtale ξ).sheafFiber.map f
        (extensionFiberStalkEquiv (ShortComplex.mk i p h) t ξ q).val := by
  let Φ := Scheme.pointSmallEtale ξ
  obtain ⟨U, x, e, rfl⟩ := Φ.toPresheafFiber_jointly_surjective
    (P := (extensionFiber (ShortComplex.mk i p h) t).obj) q
  rw [extensionFiberStalkEquiv_toFiber]
  have hn := Φ.toPresheafFiber_naturality_apply
    (representedLiftMap A i p h hs t ξ M f).hom.hom U x e
  have hc := ConcreteCategory.congr_hom
    (Φ.toPresheafFiber_presheafFiberCompIso_hom_app
      (forget AddCommGrpCat.{u}) U x (finiteAbelianMonodromySheaf ξ M).obj)
    (f.hom.app (op U) e.val)
  exact (congrArg
    ((Φ.sheafFiberCompIso (forget AddCommGrpCat.{u})).hom.app
      (finiteAbelianMonodromySheaf ξ M)) hn).trans
    (hc.trans (Φ.toPresheafFiber_naturality_apply f.hom U x e.val).symm)

private theorem representedLiftMap_evaluation
    (q : (extensionMonodromy A i p h hs t ξ).obj.V) :
    finiteAbelianMonodromyStalkAddEquiv ξ M
      ((Scheme.pointSmallEtale ξ).sheafFiber.map f
        (extensionMonodromyEvaluation A i p h hs t ξ q)) =
      finiteAbelianCoverFiberEquiv ξ M
        ((representedMonodromyIso ξ (finiteAbelianCover ξ M)).hom.hom.hom
          (((finiteLocallyConstantSetMonodromy ξ).functor.map
            (representedLiftMap A i p h hs t ξ M f)).hom.hom q)) := by
  let I := finiteLocallyConstantSetMonodromyStalkIso ξ
  let F := lifts A i p h hs t
  let V := finiteAbelianCover ξ M
  let mf := representedLiftMap A i p h hs t ξ M f
  let N := (finiteLocallyConstantSetMonodromy ξ).functor
  let Φ := Scheme.pointSmallEtale ξ
  let c := (Φ.sheafFiberCompIso (forget AddCommGrpCat.{u})).app
    (finiteAbelianMonodromySheaf ξ M)
  have hc := representedLiftMap_stalk A i p h hs t ξ M f (I.hom.app F q)
  have hc' := (congrArg c.inv hc).symm.trans
    (c.toEquiv.symm_apply_apply (Φ.sheafFiber.map mf.hom (I.hom.app F q)))
  have hn := ConcreteCategory.congr_hom (I.hom.naturality mf) q
  change finiteAbelianCoverFiberEquiv ξ M
    ((finiteEtaleSheafFiberIso ξ).hom.app V
      (c.inv (Φ.sheafFiber.map f
        (extensionMonodromyEvaluation A i p h hs t ξ q)))) = _
  exact (congrArg (fun x => finiteAbelianCoverFiberEquiv ξ M
    ((finiteEtaleSheafFiberIso ξ).hom.app V x)) hc').trans
      ((congrArg (fun x => finiteAbelianCoverFiberEquiv ξ M
        ((finiteEtaleSheafFiberIso ξ).hom.app V x)) hn.symm).trans
          (congrArg (finiteAbelianCoverFiberEquiv ξ M)
            (representedMonodromyIso_stalk ξ V ((N.map mf).hom.hom q))))

/-- Evaluation of the actual lift monodromy in a finite descended abelian
representation is equivariant for the original representation action. -/
theorem extensionMonodromyEvaluation_smul (g : Aut (FiniteEtale.fiber ξ))
    (q : (extensionMonodromy A i p h hs t ξ).obj.V) :
    finiteAbelianMonodromyStalkAddEquiv ξ M
      ((Scheme.pointSmallEtale ξ).sheafFiber.map f
        (extensionMonodromyEvaluation A i p h hs t ξ (g • q))) =
      g • finiteAbelianMonodromyStalkAddEquiv ξ M
        ((Scheme.pointSmallEtale ξ).sheafFiber.map f
          (extensionMonodromyEvaluation A i p h hs t ξ q)) := by
  let N := (finiteLocallyConstantSetMonodromy ξ).functor
  let mf := N.map (representedLiftMap A i p h hs t ξ M f)
  let e := representedMonodromyIso ξ (finiteAbelianCover ξ M)
  rw [representedLiftMap_evaluation, representedLiftMap_evaluation]
  have hf := ConcreteCategory.congr_hom (mf.hom.comm g) q
  have he := ConcreteCategory.congr_hom (e.hom.hom.comm g) (mf.hom.hom q)
  exact (congrArg (fun x => finiteAbelianCoverFiberEquiv ξ M (e.hom.hom.hom x)) hf).trans
    ((congrArg (finiteAbelianCoverFiberEquiv ξ M) he).trans
      (finiteAbelianCoverFiberEquiv_smul ξ M g (e.hom.hom.hom (mf.hom.hom q))))

end EtaleFundamentalGroups.Cohomology
