/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Cohomology.FiniteAbelianStalk
import Nyll.EtaleFundamentalGroups.Cohomology.ConstantStalk
import Nyll.EtaleFundamentalGroups.Cohomology.FiniteLocallyConstantDetection
import Nyll.EtaleFundamentalGroups.Cohomology.LocalTrivialization
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.CategoryTheory.Monoidal.Cartesian.CommGrp_

/-!
# Constant coefficients in finite abelian monodromy descent

For a trivial finite abelian representation, constant equivariant functions
give sections of the descended finite étale group. These sections respect
addition and define a map from the actual constant abelian sheaf.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite EtaleCohomology
open scoped CategoryTheory.MonObj CategoryTheory.Obj FintypeCatDiscrete

universe u

namespace EtaleFundamentalGroups.Cohomology

variable {X : Scheme.{u}} [ConnectedSpace X]
  {Ω : Type u} [Field Ω] [IsSepClosed Ω] (ξ : Spec (.of Ω) ⟶ X)
  (M : Type u) [AddCommGroup M] [Fintype M]
  [DistribMulAction (Aut (FiniteEtale.fiber ξ)) M]
  [TopologicalSpace M] [DiscreteTopology M]
  [ContinuousSMul (Aut (FiniteEtale.fiber ξ)) M]
  (hM : ∀ (g : Aut (FiniteEtale.fiber ξ)) (m : M), g • m = m)

private abbrev baseCover : FiniteEtale X :=
  MorphismProperty.Over.mk ⊤ (𝟙 X) (show IsFiniteEtale (𝟙 X) from ⟨⟩)

private def constantEquivariant (m : M) :
    MulActionHom (id : Aut (FiniteEtale.fiber ξ) → _)
      ((FiniteEtale.fiber ξ).obj (baseCover (X := X))) M where
  toFun := fun _ => m
  map_smul' := fun g _ => (hM g m).symm

/-- A coefficient in a trivial representation determines a section of its
actual descended finite étale cover. -/
def finiteAbelianConstantSection (m : M) :
    baseCover (X := X) ⟶ finiteAbelianCover ξ M :=
  (finiteAbelianRepresentableBy ξ M).homEquiv.symm (constantEquivariant ξ M hM m)

/-- The section has the prescribed value in the actual geometric fiber. -/
theorem finiteAbelianConstantSection_fiber (m : M)
    (x : (FiniteEtale.fiber ξ).obj (baseCover (X := X))) :
    finiteAbelianCoverFiberEquiv ξ M
      ((FiniteEtale.fiber ξ).map (finiteAbelianConstantSection ξ M hM m) x) = m :=
  congrArg (fun f : MulActionHom (id : Aut (FiniteEtale.fiber ξ) → _)
      ((FiniteEtale.fiber ξ).obj (baseCover (X := X))) M => f x)
    ((finiteAbelianRepresentableBy ξ M).homEquiv.apply_symm_apply
      (constantEquivariant ξ M hM m))

private theorem constantSection_add (m n : M) :
    let : CartesianMonoidalCategory (FiniteEtale X) := .ofHasFiniteProducts
    let : BraidedCategory (FiniteEtale X) := .ofCartesianMonoidalCategory
    let : CommGrpObj (finiteAbelianCover ξ M) := finiteAbelianCoverGroup ξ M
    finiteAbelianConstantSection ξ M hM (m + n) =
      finiteAbelianConstantSection ξ M hM m * finiteAbelianConstantSection ξ M hM n := by
  let : CartesianMonoidalCategory (FiniteEtale X) := .ofHasFiniteProducts
  let : BraidedCategory (FiniteEtale X) := .ofCartesianMonoidalCategory
  let : CommGrpObj (finiteAbelianCover ξ M) := finiteAbelianCoverGroup ξ M
  let r := finiteAbelianRepresentableBy ξ M
  let e := yonedaGrpObjIsoOfRepresentableBy _
    (finiteAbelianEquivariantPresheaf ξ M ⋙ forget₂ CommGrpCat GrpCat) r
  apply r.homEquiv.injective
  have hm := (e.hom.app (op (baseCover (X := X)))).hom.map_mul
    (finiteAbelianConstantSection ξ M hM m) (finiteAbelianConstantSection ξ M hM n)
  change r.homEquiv (_ * _) = r.homEquiv _ * r.homEquiv _ at hm
  have hs := r.homEquiv.apply_symm_apply (constantEquivariant ξ M hM (m + n))
  have hmn := congrArg₂ (· * ·)
    (r.homEquiv.apply_symm_apply (constantEquivariant ξ M hM m))
    (r.homEquiv.apply_symm_apply (constantEquivariant ξ M hM n))
  exact hs.trans (hmn.symm.trans hm.symm)

private def toBaseCover (U : X.Etale) :
    U ⟶ (finiteEtaleToEtale X).obj (baseCover (X := X)) :=
  MorphismProperty.Over.homMk U.hom (Category.comp_id U.hom)

private def constantSectionsPresheaf :
    (Functor.const X.Etaleᵒᵖ).obj (AddCommGrpCat.of M) ⟶
      (finiteAbelianMonodromySheaf ξ M).obj where
  app U := AddCommGrpCat.ofHom
    (AddMonoidHom.mk'
      (fun m => Additive.ofMul
        (toBaseCover U.unop ≫ (finiteEtaleToEtale X).map
          (finiteAbelianConstantSection ξ M hM m)))
      (fun m n => by
        let : CartesianMonoidalCategory (FiniteEtale X) := .ofHasFiniteProducts
        let : BraidedCategory (FiniteEtale X) := .ofCartesianMonoidalCategory
        let : CommGrpObj (finiteAbelianCover ξ M) := finiteAbelianCoverGroup ξ M
        let F := finiteEtaleToEtale X
        have h := congrArg F.map (constantSection_add ξ M hM m n)
        have hm := F.map_mul (finiteAbelianConstantSection ξ M hM m)
          (finiteAbelianConstantSection ξ M hM n)
        exact (congrArg (toBaseCover U.unop ≫ ·) (h.trans hm)).trans
          (MonObj.comp_mul (toBaseCover U.unop)
            (F.map (finiteAbelianConstantSection ξ M hM m))
            (F.map (finiteAbelianConstantSection ξ M hM n)))))
  naturality U V f := by
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro m
    have hw : toBaseCover V.unop = f.unop ≫ toBaseCover U.unop := by
      apply MorphismProperty.Over.Hom.ext
      exact f.unop.w.symm
    exact (congrArg (· ≫ (finiteEtaleToEtale X).map
      (finiteAbelianConstantSection ξ M hM m)) hw).trans
        (Category.assoc f.unop (toBaseCover U.unop)
          ((finiteEtaleToEtale X).map (finiteAbelianConstantSection ξ M hM m)))

/-- Constant equivariant sections extend uniquely through sheafification to
a homomorphism from the actual constant abelian sheaf. -/
def finiteAbelianConstantSheafMap :
    (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj (AddCommGrpCat.of M) ⟶
      finiteAbelianMonodromySheaf ξ M :=
  ⟨sheafifyLift X.smallEtaleTopology (constantSectionsPresheaf ξ M hM)
    (finiteAbelianMonodromySheaf ξ M).property⟩

private theorem constantSection_stalk (U : X.Etale)
    (x : (Scheme.pointSmallEtale ξ).fiber.obj U) (m : M) :
    finiteAbelianMonodromyStalkEquiv ξ M
      ((Scheme.pointSmallEtale ξ).toPresheafFiber U x
        (finiteAbelianMonodromySheaf ξ M).obj
          ((constantSectionsPresheaf ξ M hM).app (op U) m)) = m := by
  let Φ := Scheme.pointSmallEtale ξ
  let H := finiteAbelianMonodromySheaf ξ M
  let T := baseCover (X := X)
  let V := finiteAbelianCover ξ M
  let F := finiteEtaleSheaf X
  let f := finiteAbelianConstantSection ξ M hM m
  let a := toBaseCover U
  let s := (constantSectionsPresheaf ξ M hM).app (op U) m
  let t := Φ.toPresheafFiber U x (F.obj T).obj a
  let r := Φ.toPresheafFiber U x (H.obj ⋙ forget AddCommGrpCat.{u}) s
  let q := Φ.toPresheafFiber U x H.obj s
  let e := (Φ.sheafFiberCompIso (forget AddCommGrpCat.{u})).app H
  let L := finiteEtaleSheafFiberIso ξ
  have he : e.hom r = q := congrArg (fun k => k s)
    (Φ.toPresheafFiber_presheafFiberCompIso_hom_app
      (forget AddCommGrpCat.{u}) U x H.obj)
  have he' : e.inv q = r := (congrArg e.inv he).symm.trans
    (e.toEquiv.symm_apply_apply r)
  have hf : Φ.sheafFiber.map (F.map f) t = r := congrArg (fun k => k a)
    (Φ.toPresheafFiber_naturality (F.map f).hom U x)
  have hL : (L.app V).hom (Φ.sheafFiber.map (F.map f) t) =
      (FiniteEtale.fiber ξ).map f ((L.app T).hom t) :=
    congrArg (fun k => k t) (L.hom.naturality f)
  change finiteAbelianCoverFiberEquiv ξ M ((L.app V).hom (e.inv q)) = m
  exact (congrArg (fun z => finiteAbelianCoverFiberEquiv ξ M ((L.app V).hom z)) he').trans
    ((congrArg (finiteAbelianCoverFiberEquiv ξ M)
      ((congrArg (L.app V).hom hf.symm).trans hL)).trans
        (finiteAbelianConstantSection_fiber ξ M hM m ((L.app T).hom t)))

/-- The map from the constant sheaf has the prescribed coefficient map on
the actual geometric stalk. -/
theorem finiteAbelianConstantSheafMap_stalk
    (z : (Scheme.pointSmallEtale ξ).sheafFiber (A := AddCommGrpCat.{u}) |>.obj
      ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj (AddCommGrpCat.of M))) :
    finiteAbelianMonodromyStalkAddEquiv ξ M
      ((Scheme.pointSmallEtale ξ).sheafFiber.map (finiteAbelianConstantSheafMap ξ M hM) z) =
        (constantAbelianStalkIso ξ (AddCommGrpCat.of M)).hom z := by
  let Φ := Scheme.pointSmallEtale ξ
  let H := finiteAbelianMonodromySheaf ξ M
  let C := (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj (AddCommGrpCat.of M)
  let P := (Functor.const X.Etaleᵒᵖ).obj (AddCommGrpCat.of M)
  let f := finiteAbelianConstantSheafMap ξ M hM
  let E := AddCommGrpCat.ofHom (finiteAbelianMonodromyStalkAddEquiv ξ M).toAddMonoidHom
  have hh : Φ.sheafFiber.map f ≫ E = (constantAbelianStalkIso ξ (AddCommGrpCat.of M)).hom := by
    apply (cancel_epi (Φ.presheafFiber.map (toSheafify X.smallEtaleTopology P))).mp
    apply Φ.presheafFiber_hom_ext
    intro U x
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro m
    have hunit := congrArg (fun k => k m)
      (constantAbelianStalkIso_unit ξ (AddCommGrpCat.of M) U x)
    have hlift := congrArg (fun trans => trans.app (op U))
      (toSheafify_sheafifyLift X.smallEtaleTopology
        (constantSectionsPresheaf ξ M hM) H.property)
    have hn₁ := congrArg (fun k => k m)
      (Φ.toPresheafFiber_naturality (toSheafify X.smallEtaleTopology P) U x)
    have hn₂ := congrArg (fun k => k ((toSheafify X.smallEtaleTopology P).app (op U) m))
      (Φ.toPresheafFiber_naturality f.hom U x)
    have hv := congrArg (fun k => k m) hlift
    exact (congrArg (fun y => E (Φ.sheafFiber.map f y)) hn₁).trans
      ((congrArg E hn₂).trans
        ((congrArg (fun y => E (Φ.toPresheafFiber U x H.obj y)) hv).trans
          ((constantSection_stalk ξ M hM U x m).trans
            ((congrArg (fun y => (constantAbelianStalkIso ξ
              (AddCommGrpCat.of M)).hom y) hn₁).trans hunit).symm)))
  exact congrArg (fun k => k z) hh

/-- A trivial finite abelian representation descends to the actual constant
abelian sheaf with those coefficients. -/
def finiteAbelianConstantSheafIso :
    (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj (AddCommGrpCat.of M) ≅
      finiteAbelianMonodromySheaf ξ M := by
  let f := finiteAbelianConstantSheafMap ξ M hM
  let e := finiteAbelianMonodromyStalkAddEquiv ξ M
  let c := (constantAbelianStalkIso ξ (AddCommGrpCat.of M)).addCommGroupIsoToAddEquiv
  have hf : (Scheme.pointSmallEtale ξ).sheafFiber.map f =
      AddCommGrpCat.ofHom (c.trans e.symm).toAddMonoidHom := by
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro z
    apply e.injective
    exact (finiteAbelianConstantSheafMap_stalk ξ M hM z).trans (e.apply_symm_apply (c z)).symm
  have hb : Function.Bijective ((Scheme.pointSmallEtale ξ).sheafFiber.map f) := by
    rw [hf]
    exact (c.trans e.symm).bijective
  have : IsIso f := isIso_of_bijective_finiteLocallyConstant_abelianStalk ξ f
    (constantAbelian_isFiniteLocallyConstant X (AddCommGrpCat.of M))
    (finiteAbelianMonodromySheaf_isFiniteLocallyConstant ξ M) hb
  exact asIso f

end EtaleFundamentalGroups.Cohomology
