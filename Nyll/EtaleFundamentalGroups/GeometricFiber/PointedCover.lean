/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.GaloisCategories.PointedOver
import Nyll.EtaleFundamentalGroups.GeometricFiber.PullbackFiberPoint

/-!
# Geometric fibers over a pointed finite étale cover

A finite étale scheme over the source of a finite étale cover is the same as
a finite étale scheme over the base equipped with a map to that cover.  Under
this equivalence, the geometric fiber at a lifted point is the corresponding
fiber-over-a-point functor.  Consequently, its automorphism group is the
stabilizer of the lifted point in the automorphism group over the base.
-/

noncomputable section

universe u

open CategoryTheory
open CategoryTheory.PreGaloisCategory
open scoped FintypeCatDiscrete

namespace AlgebraicGeometry.FiniteEtale

variable {S : Scheme.{u}}

private abbrev overBaseObj (A : FiniteEtale S) (B : FiniteEtale A.left) :
    FiniteEtale S :=
  MorphismProperty.Over.mk ⊤ (B.hom ≫ A.hom) (by
    exact @IsFiniteEtale.instCompScheme B.left A.left S B.hom A.hom B.2 A.2)

private abbrev overBaseHom (A : FiniteEtale S) (B : FiniteEtale A.left) :
    overBaseObj A B ⟶ A :=
  MorphismProperty.Over.homMk B.hom

private abbrev toOverObj (A : FiniteEtale S) (B : FiniteEtale A.left) : Over A :=
  Over.mk (overBaseHom A B)

private abbrev toOverMap (A : FiniteEtale S) {B C : FiniteEtale A.left}
    (f : B ⟶ C) : toOverObj A B ⟶ toOverObj A C :=
  Over.homMk
    (MorphismProperty.Over.homMk f.left (by
      change f.left ≫ (C.hom ≫ A.hom) = B.hom ≫ A.hom
      rw [← Category.assoc, MorphismProperty.Over.w f]))
    (by
      apply MorphismProperty.Over.Hom.ext
      exact MorphismProperty.Over.w f)

private def toOver (A : FiniteEtale S) : FiniteEtale A.left ⥤ Over A where
  obj B := toOverObj A B
  map f := toOverMap A f
  map_id B := by
    apply Over.OverMorphism.ext
    apply MorphismProperty.Over.Hom.ext
    rfl
  map_comp f g := by
    apply Over.OverMorphism.ext
    apply MorphismProperty.Over.Hom.ext
    rfl

private abbrev toOverFaithful (A : FiniteEtale S) : (toOver A).Faithful where
  map_injective {B C} f g h := by
    change toOverMap A f = toOverMap A g at h
    apply MorphismProperty.Over.Hom.ext
    exact congrArg (fun q ↦ q.left.left) h

private abbrev toOverFull (A : FiniteEtale S) : (toOver A).Full where
  map_surjective {B C} f := by
    let g : B ⟶ C := MorphismProperty.Over.homMk f.left.left (by
      exact congrArg (fun q ↦ q.left) (Over.w f))
    refine ⟨g, ?_⟩
    change toOverMap A g = f
    apply Over.OverMorphism.ext
    apply MorphismProperty.Over.Hom.ext
    rfl

private abbrev toOverEssSurj (A : FiniteEtale S) : (toOver A).EssSurj where
  mem_essImage U := by
    let B : FiniteEtale A.left := FiniteEtale.mk U.hom.left
    let eBase : overBaseObj A B ≅ U.left :=
      MorphismProperty.Over.isoMk (Iso.refl U.left.left) (by
        change (𝟙 U.left.left) ≫ U.left.hom = U.hom.left ≫ A.hom
        rw [Category.id_comp]
        exact (MorphismProperty.Over.w U.hom).symm)
    let e : toOverObj A B ≅ U := Over.isoMk eBase (by
      apply MorphismProperty.Over.Hom.ext
      rfl)
    change (toOver A).essImage U
    exact ⟨B, ⟨e⟩⟩

/-- Finite étale schemes over the source of `A` are equivalent to finite
étale schemes over the base equipped with a map to `A`. -/
noncomputable def overEquiv (A : FiniteEtale S) :
    FiniteEtale A.left ≌ Over A := by
  letI : (toOver A).IsEquivalence :=
    { faithful := toOverFaithful A
      full := toOverFull A
      essSurj := toOverEssSurj A }
  exact (toOver A).asEquivalence

variable {Omega : Type u} [Field Omega] [IsSepClosed Omega]

private abbrev basePoint (A : FiniteEtale S)
    (xi' : Spec (.of Omega) ⟶ A.left) : Spec (.of Omega) ⟶ S :=
  xi' ≫ A.hom

private abbrev liftedPointHom (A : FiniteEtale S)
    (xi' : Spec (.of Omega) ⟶ A.left) :
    Over.mk (basePoint A xi') ⟶ A.toComma :=
  Over.homMk xi'

/-- The point of the geometric fiber of `A` determined by a lift of the base
geometric point to the source of `A`. -/
noncomputable def liftedFiberPoint (A : FiniteEtale S)
    (xi' : Spec (.of Omega) ⟶ A.left) :
    (fiber (basePoint A xi')).obj A :=
  (fiberObjEquivHom (basePoint A xi') A).symm (liftedPointHom A xi')

/-- The point of the geometric fiber determined by a lift, with the base
point displayed explicitly as the composite with the covering map. -/
noncomputable def liftedFiberPointOverComposite (A : FiniteEtale S)
    (xi' : Spec (.of Omega) ⟶ A.left) :
    (fiber (xi' ≫ A.hom)).obj A :=
  liftedFiberPoint A xi'

private noncomputable def sourcePointOfFiberOver
    (A : FiniteEtale S) (xi' : Spec (.of Omega) ⟶ A.left)
    (B : FiniteEtale A.left)
    (y : (fiberOver (fiber (basePoint A xi')) (liftedFiberPoint A xi')).obj
      (toOverObj A B)) :
    Over.mk xi' ⟶ B.toComma := by
  let q : Over.mk (basePoint A xi') ⟶ (overBaseObj A B).toComma :=
    fiberObjEquivHom (basePoint A xi') (overBaseObj A B) y.1
  have hq : q ≫ (overBaseHom A B).hom = liftedPointHom A xi' := by
    calc
      q ≫ (overBaseHom A B).hom =
          fiberObjEquivHom (basePoint A xi') A
            ((fiber (basePoint A xi')).map (overBaseHom A B) y.1) :=
        fiberObjEquivHom_naturality (basePoint A xi') (overBaseHom A B) y.1
      _ = fiberObjEquivHom (basePoint A xi') A (liftedFiberPoint A xi') :=
        congrArg (fiberObjEquivHom (basePoint A xi') A) y.2
      _ = liftedPointHom A xi' := Equiv.apply_symm_apply _ _
  refine Over.homMk q.left ?_
  exact congrArg (fun f ↦ f.left) hq

private noncomputable def fiberOverOfSourcePoint
    (A : FiniteEtale S) (xi' : Spec (.of Omega) ⟶ A.left)
    (B : FiniteEtale A.left) (z : Over.mk xi' ⟶ B.toComma) :
    (fiberOver (fiber (basePoint A xi')) (liftedFiberPoint A xi')).obj
      (toOverObj A B) := by
  let q : Over.mk (basePoint A xi') ⟶ (overBaseObj A B).toComma :=
    Over.homMk z.left (by
      change z.left ≫ (B.hom ≫ A.hom) = xi' ≫ A.hom
      calc
        z.left ≫ (B.hom ≫ A.hom) = (z.left ≫ B.hom) ≫ A.hom :=
          (Category.assoc _ _ _).symm
        _ = xi' ≫ A.hom := congrArg (fun f ↦ f ≫ A.hom) z.w)
  let y := (fiberObjEquivHom (basePoint A xi') (overBaseObj A B)).symm q
  refine ⟨y, ?_⟩
  apply (fiberObjEquivHom (basePoint A xi') A).injective
  calc
    fiberObjEquivHom (basePoint A xi') A
        ((fiber (basePoint A xi')).map (overBaseHom A B) y) =
        fiberObjEquivHom (basePoint A xi') (overBaseObj A B) y ≫
          (overBaseHom A B).hom :=
      (fiberObjEquivHom_naturality (basePoint A xi') (overBaseHom A B) y).symm
    _ = q ≫ (overBaseHom A B).hom :=
      congrArg (fun r ↦ r ≫ (overBaseHom A B).hom) (Equiv.apply_symm_apply _ q)
    _ = liftedPointHom A xi' := by
      apply Over.OverMorphism.ext
      exact z.w
    _ = fiberObjEquivHom (basePoint A xi') A (liftedFiberPoint A xi') :=
      (Equiv.apply_symm_apply _ _).symm

private theorem sourcePointOfFiberOver_fiberOverOfSourcePoint
    (A : FiniteEtale S) (xi' : Spec (.of Omega) ⟶ A.left)
    (B : FiniteEtale A.left) (z : Over.mk xi' ⟶ B.toComma) :
    sourcePointOfFiberOver A xi' B (fiberOverOfSourcePoint A xi' B z) = z := by
  apply Over.OverMorphism.ext
  simp [sourcePointOfFiberOver, fiberOverOfSourcePoint]
  rfl

private theorem fiberOverOfSourcePoint_sourcePointOfFiberOver
    (A : FiniteEtale S) (xi' : Spec (.of Omega) ⟶ A.left)
    (B : FiniteEtale A.left)
    (y : (fiberOver (fiber (basePoint A xi')) (liftedFiberPoint A xi')).obj
      (toOverObj A B)) :
    fiberOverOfSourcePoint A xi' B (sourcePointOfFiberOver A xi' B y) = y := by
  apply Subtype.ext
  change (fiberObjEquivHom (basePoint A xi') (overBaseObj A B)).symm
    (fiberObjEquivHom (basePoint A xi') (overBaseObj A B) y.1) = y.1
  exact Equiv.symm_apply_apply (fiberObjEquivHom (basePoint A xi') (overBaseObj A B)) y.1

private noncomputable def fiberOverEquiv
    (A : FiniteEtale S) (xi' : Spec (.of Omega) ⟶ A.left)
    (B : FiniteEtale A.left) :
    (fiberOver (fiber (basePoint A xi')) (liftedFiberPoint A xi')).obj
        (toOverObj A B) ≃
      (fiber xi').obj B where
  toFun y := (fiberObjEquivHom xi' B).symm (sourcePointOfFiberOver A xi' B y)
  invFun z := fiberOverOfSourcePoint A xi' B (fiberObjEquivHom xi' B z)
  left_inv y := by
    exact (congrArg (fiberOverOfSourcePoint A xi' B)
      (Equiv.apply_symm_apply (fiberObjEquivHom xi' B)
        (sourcePointOfFiberOver A xi' B y))).trans
      (fiberOverOfSourcePoint_sourcePointOfFiberOver A xi' B y)
  right_inv z := by
    apply (fiberObjEquivHom xi' B).injective
    rw [Equiv.apply_symm_apply]
    exact sourcePointOfFiberOver_fiberOverOfSourcePoint A xi' B _

private theorem fiberOverEquiv_apply
    (A : FiniteEtale S) (xi' : Spec (.of Omega) ⟶ A.left)
    (B : FiniteEtale A.left)
    (y : (fiberOver (fiber (basePoint A xi')) (liftedFiberPoint A xi')).obj
      (toOverObj A B)) :
    fiberOverEquiv A xi' B y =
      (fiberObjEquivHom xi' B).symm (sourcePointOfFiberOver A xi' B y) :=
  rfl

private theorem sourcePointOfFiberOver_naturality
    (A : FiniteEtale S) (xi' : Spec (.of Omega) ⟶ A.left)
    {B C : FiniteEtale A.left} (f : B ⟶ C)
    (y : (fiberOver (fiber (basePoint A xi')) (liftedFiberPoint A xi')).obj
      (toOverObj A B)) :
    sourcePointOfFiberOver A xi' C
        ((fiberOver (fiber (basePoint A xi')) (liftedFiberPoint A xi')).map
          (toOverMap A f) y) =
      sourcePointOfFiberOver A xi' B y ≫ f.hom := by
  apply Over.OverMorphism.ext
  change
    (fiberObjEquivHom (basePoint A xi') (overBaseObj A C)
      ((fiber (basePoint A xi')).map (toOverMap A f).left y.1)).left =
    (fiberObjEquivHom (basePoint A xi') (overBaseObj A B) y.1).left ≫ f.left
  exact congrArg (fun q ↦ q.left)
    (fiberObjEquivHom_naturality (basePoint A xi') (toOverMap A f).left y.1).symm

private theorem fiberObjEquivHom_map_symm
    (xi' : Spec (.of Omega) ⟶ S) {B C : FiniteEtale S} (f : B ⟶ C)
    (z : Over.mk xi' ⟶ B.toComma) :
    z ≫ f.hom =
      fiberObjEquivHom xi' C
        ((fiber xi').map f ((fiberObjEquivHom xi' B).symm z)) := by
  calc
    z ≫ f.hom =
        fiberObjEquivHom xi' B ((fiberObjEquivHom xi' B).symm z) ≫ f.hom :=
      congrArg (fun q ↦ q ≫ f.hom) (Equiv.apply_symm_apply _ z).symm
    _ = fiberObjEquivHom xi' C
        ((fiber xi').map f ((fiberObjEquivHom xi' B).symm z)) :=
      fiberObjEquivHom_naturality xi' f _

private theorem fiberOverFormula_naturality
    (A : FiniteEtale S) (xi' : Spec (.of Omega) ⟶ A.left)
    {B C : FiniteEtale A.left} (f : B ⟶ C)
    (y : (fiberOver (fiber (basePoint A xi')) (liftedFiberPoint A xi')).obj
      (toOverObj A B)) :
    (fiberObjEquivHom xi' C).symm
        (sourcePointOfFiberOver A xi' C
          ((fiberOver (fiber (basePoint A xi')) (liftedFiberPoint A xi')).map
            (toOverMap A f) y)) =
      (fiber xi').map f
        ((fiberObjEquivHom xi' B).symm (sourcePointOfFiberOver A xi' B y)) := by
  apply (fiberObjEquivHom xi' C).symm_apply_eq.mpr
  exact (sourcePointOfFiberOver_naturality A xi' f y).trans
    (fiberObjEquivHom_map_symm xi' f (sourcePointOfFiberOver A xi' B y))

private theorem fiberOverEquiv_naturality
    (A : FiniteEtale S) (xi' : Spec (.of Omega) ⟶ A.left)
    {B C : FiniteEtale A.left} (f : B ⟶ C)
    (y : (fiberOver (fiber (basePoint A xi')) (liftedFiberPoint A xi')).obj
      (toOverObj A B)) :
    fiberOverEquiv A xi' C
        ((fiberOver (fiber (basePoint A xi')) (liftedFiberPoint A xi')).map
          (toOverMap A f) y) =
      (fiber xi').map f (fiberOverEquiv A xi' B y) := by
  simpa only [fiberOverEquiv_apply] using fiberOverFormula_naturality A xi' f y

/-- Under the equivalence with the over-category, the geometric fiber at the
lifted point is the fiber over the corresponding point of the base fiber. -/
noncomputable def overEquivFiberIso (A : FiniteEtale S)
    (xi' : Spec (.of Omega) ⟶ A.left) :
    (overEquiv A).functor ⋙
        fiberOver (fiber (basePoint A xi')) (liftedFiberPoint A xi') ≅
      fiber xi' := by
  change toOver A ⋙
      fiberOver (fiber (basePoint A xi')) (liftedFiberPoint A xi') ≅ fiber xi'
  exact NatIso.ofComponents
    (fun B ↦ FintypeCat.equivEquivIso (fiberOverEquiv A xi' B))
    (fun f ↦ by
      apply FintypeCat.hom_ext
      intro y
      exact fiberOverEquiv_naturality A xi' f y)

/-- The over-category fiber comparison induces the actual topological
isomorphism of its automorphism group with the lifted geometric fundamental group. -/
noncomputable def autFiberOverEquivFiber
    (A : FiniteEtale S) (xi' : Spec (.of Omega) ⟶ A.left) :
    Aut (fiberOver (fiber (basePoint A xi')) (liftedFiberPoint A xi')) ≃ₜ*
      Aut (fiber xi') := by
  let E : (FiniteEtale A.left ⥤ FintypeCat) ≌ (Over A ⥤ FintypeCat) :=
    (overEquiv A).congrLeft
  let e :
      Aut (fiberOver (fiber (basePoint A xi')) (liftedFiberPoint A xi')) ≃*
        Aut (fiber xi') :=
    (E.fullyFaithfulInverse.autMulEquivOfFullyFaithful
      (fiberOver (fiber (basePoint A xi')) (liftedFiberPoint A xi'))).trans
        (overEquivFiberIso A xi').conjAut
  exact
    { toMulEquiv := e
      continuous_toFun := by
        change Continuous
          (autHomOfCompIso (overEquiv A).functor (overEquivFiberIso A xi'))
        exact (autHomOfCompIso
          (overEquiv A).functor (overEquivFiberIso A xi')).continuous
      continuous_invFun :=
        Continuous.continuous_symm_of_equiv_compact_to_t2
          (f := e.toEquiv) (by
            change Continuous
              (autHomOfCompIso (overEquiv A).functor (overEquivFiberIso A xi'))
            exact (autHomOfCompIso
              (overEquiv A).functor (overEquivFiberIso A xi')).continuous) }

/-- The étale fundamental group at a lifted geometric point is canonically
isomorphic to the stabilizer of the corresponding point in the geometric
fiber of the finite étale cover over the base. -/
noncomputable def fundamentalGroupEquivStabilizerOfLift
    [ConnectedSpace S] (A : FiniteEtale S)
    (xi' : Spec (.of Omega) ⟶ A.left) :
    π₁ᵉᵗ(xi') ≃ₜ*
      MulAction.stabilizer (π₁ᵉᵗ(basePoint A xi')) (liftedFiberPoint A xi') :=
  (autFiberOverEquivFiber A xi').symm.trans
    (autFiberOverEquivStabilizer (fiber (basePoint A xi')) (liftedFiberPoint A xi'))

private def pullbackToProductOver
    (A : FiniteEtale S) (B : FiniteEtale S) :
    toOverObj A ((pullback A.hom).obj B) ⟶
      (productOver (X := A)).obj B := by
  let pB : overBaseObj A ((pullback A.hom).obj B) ⟶ B :=
    MorphismProperty.Over.homMk (Limits.pullback.fst B.hom A.hom) (by
      exact Limits.pullback.condition)
  let pA : overBaseObj A ((pullback A.hom).obj B) ⟶ A :=
    overBaseHom A ((pullback A.hom).obj B)
  exact Over.homMk (Limits.prod.lift pB pA) (by
    exact Limits.prod.lift_snd pB pA)

private theorem sourcePointOf_overEquivFiberIso_inv
    (A : FiniteEtale S) (xi' : Spec (.of Omega) ⟶ A.left)
    (B : FiniteEtale A.left) (p : (fiber xi').obj B) :
    sourcePointOfFiberOver A xi' B
        ((overEquivFiberIso A xi').inv.app B p) =
      fiberObjEquivHom xi' B p := by
  let y := (overEquivFiberIso A xi').inv.app B p
  have h := FintypeCat.inv_hom_id_apply ((overEquivFiberIso A xi').app B) p
  change fiberOverEquiv A xi' B y = p at h
  change (fiberObjEquivHom xi' B).symm
      (sourcePointOfFiberOver A xi' B y) = p at h
  exact (fiberObjEquivHom xi' B).symm.injective
    (h.trans (Equiv.symm_apply_apply (fiberObjEquivHom xi' B) p).symm)

private theorem fiberOver_map_pullbackToProductOver
    [ConnectedSpace S] (A : FiniteEtale S) (xi' : Spec (.of Omega) ⟶ A.left)
    (B : FiniteEtale S) (b : (fiber (basePoint A xi')).obj B) :
    (fiberOver (fiber (basePoint A xi')) (liftedFiberPoint A xi')).map
        (pullbackToProductOver A B)
        ((overEquivFiberIso A xi').inv.app ((pullback A.hom).obj B)
          (transportedPointOfCompIso (pullback A.hom)
            (pullbackFiberIso A.hom xi') B b)) =
      productFiberEquivComparison
        (fiber (basePoint A xi')) (liftedFiberPoint A xi') B b := by
  let PB : FiniteEtale A.left := (pullback A.hom).obj B
  let p : (fiber xi').obj PB :=
    transportedPointOfCompIso (pullback A.hom)
      (pullbackFiberIso A.hom xi') B b
  let y := (overEquivFiberIso A xi').inv.app PB p
  let pB : overBaseObj A PB ⟶ B :=
    MorphismProperty.Over.homMk (Limits.pullback.fst B.hom A.hom) (by
      exact Limits.pullback.condition)
  have hySource : sourcePointOfFiberOver A xi' PB y =
      fiberObjEquivHom xi' PB p := by
    exact sourcePointOf_overEquivFiberIso_inv A xi' PB p
  have hp : (fiber (basePoint A xi')).map pB y.1 = b := by
    apply (fiberObjEquivHom (basePoint A xi') B).injective
    rw [← fiberObjEquivHom_naturality (basePoint A xi') pB y.1]
    apply Over.OverMorphism.ext
    change ((fiberObjEquivHom (basePoint A xi') (overBaseObj A PB) y.1).left ≫
        pB.left : Spec (.of Omega) ⟶ B.left) =
      (fiberObjEquivHom (basePoint A xi') B b).left
    have htransport : (pullbackFiberIso A.hom xi').hom.app B p = b := by
      exact FintypeCat.inv_hom_id_apply ((pullbackFiberIso A.hom xi').app B) b
    have hprojection :
        (fiberObjEquivHom xi' PB p).left ≫ Limits.pullback.fst B.hom A.hom =
          (fiberObjEquivHom (basePoint A xi') B
            ((pullbackFiberIso A.hom xi').hom.app B p)).left := by
      have h :=
        (pullbackFiberIso_hom_fiberObjEquivHom_left A.hom xi' B p).symm
      change ((fiberObjEquivHom xi' PB p).left ≫
          Limits.pullback.fst B.hom A.hom :
            Spec (.of Omega) ⟶ B.left) =
        (fiberObjEquivHom (basePoint A xi') B
          ((pullbackFiberIso A.hom xi').hom.app B p)).left at h
      exact h
    let q0 : Spec (.of Omega) ⟶ B.left :=
      (fiberObjEquivHom (basePoint A xi') (overBaseObj A PB) y.1).left ≫ pB.left
    let q1 : Spec (.of Omega) ⟶ B.left :=
      (sourcePointOfFiberOver A xi' PB y).left ≫
        Limits.pullback.fst B.hom A.hom
    let q2 : Spec (.of Omega) ⟶ B.left :=
      (fiberObjEquivHom xi' PB p).left ≫ Limits.pullback.fst B.hom A.hom
    let q3 : Spec (.of Omega) ⟶ B.left :=
      (fiberObjEquivHom (basePoint A xi') B
        ((pullbackFiberIso A.hom xi').hom.app B p)).left
    let q4 : Spec (.of Omega) ⟶ B.left :=
      (fiberObjEquivHom (basePoint A xi') B b).left
    have h01 : q0 = q1 := by rfl
    have h12 : q1 = q2 := by
      exact congrArg
        (fun q ↦ (q.left ≫ Limits.pullback.fst B.hom A.hom :
          Spec (.of Omega) ⟶ B.left)) hySource
    have h23 : q2 = q3 := hprojection
    have h34 : q3 = q4 := by
      exact congrArg
        (fun q ↦ ((fiberObjEquivHom (basePoint A xi') B q).left :
          Spec (.of Omega) ⟶ B.left)) htransport
    exact h01.trans (h12.trans (h23.trans h34))
  apply (productFiberEquivComparison
    (fiber (basePoint A xi')) (liftedFiberPoint A xi') B).symm.injective
  rw [Equiv.symm_apply_apply, productFiberEquivComparison_symm_apply]
  change (fiber (basePoint A xi')).map Limits.prod.fst
      (((fiberOver (fiber (basePoint A xi')) (liftedFiberPoint A xi')).map
        (pullbackToProductOver A B)) y).1 = b
  change (fiber (basePoint A xi')).map Limits.prod.fst
    ((fiber (basePoint A xi')).map (pullbackToProductOver A B).left y.1) = b
  have hq : (pullbackToProductOver A B).left ≫ Limits.prod.fst = pB := by
    change Limits.prod.lift _ _ ≫ Limits.prod.fst = pB
    exact Limits.prod.lift_fst _ _
  calc
    (fiber (basePoint A xi')).map Limits.prod.fst
        ((fiber (basePoint A xi')).map (pullbackToProductOver A B).left y.1) =
      (fiber (basePoint A xi')).map
        ((pullbackToProductOver A B).left ≫ Limits.prod.fst) y.1 := by
          change
            ((fiber (basePoint A xi')).map (pullbackToProductOver A B).left ≫
              (fiber (basePoint A xi')).map Limits.prod.fst) y.1 =
              (fiber (basePoint A xi')).map
                ((pullbackToProductOver A B).left ≫ Limits.prod.fst) y.1
          exact congrArg (fun q ↦ q y.1)
            ((fiber (basePoint A xi')).map_comp
              (pullbackToProductOver A B).left Limits.prod.fst).symm
    _ = (fiber (basePoint A xi')).map pB y.1 :=
      congrArg (fun q ↦ (fiber (basePoint A xi')).map q y.1) hq
    _ = b := hp

theorem fundamentalGroupEquivStabilizerOfLift_coe
    [ConnectedSpace S] (A : FiniteEtale S)
    (xi' : Spec (.of Omega) ⟶ A.left) (a : π₁ᵉᵗ(xi')) :
    (fundamentalGroupEquivStabilizerOfLift A xi' a :
        π₁ᵉᵗ(basePoint A xi')) =
      fundamentalGroupHom A.hom xi' a := by
  change extendFiberOverAut (fiber (basePoint A xi')) (liftedFiberPoint A xi')
      ((autFiberOverEquivFiber A xi').symm a) =
    fundamentalGroupHom A.hom xi' a
  apply Aut.ext
  ext B b
  rw [extendFiberOverAut_hom_app_apply_eq]
  apply (productFiberEquivComparison
    (fiber (basePoint A xi')) (liftedFiberPoint A xi') B).injective
  rw [Equiv.apply_symm_apply]
  let F := fiber (basePoint A xi')
  let x := liftedFiberPoint A xi'
  let d : Aut (fiberOver F x) := (autFiberOverEquivFiber A xi').symm a
  let PB : FiniteEtale A.left := (pullback A.hom).obj B
  let tPull := pullbackFiberIso A.hom xi'
  let p : (fiber xi').obj PB := transportedPointOfCompIso
    (pullback A.hom) tPull B b
  let y := (overEquivFiberIso A xi').inv.app PB p
  let b' : F.obj B := (fundamentalGroupHom A.hom xi' a).hom.app B b
  let p' : (fiber xi').obj PB := transportedPointOfCompIso
    (pullback A.hom) tPull B b'
  let y' := (overEquivFiberIso A xi').inv.app PB p'
  have hdp : d.hom.app (toOverObj A ((pullback A.hom).obj B)) y = y' := by
    change d.hom.app ((overEquiv A).functor.obj PB) y = y'
    have hd : autFiberOverEquivFiber A xi' d = a := by
      exact (autFiberOverEquivFiber A xi').apply_symm_apply a
    have heq : (overEquivFiberIso A xi').hom.app PB (d.hom.app _ y) =
        (autHomOfCompIso (overEquiv A).functor
          (overEquivFiberIso A xi') d).hom.app PB
            ((overEquivFiberIso A xi').hom.app PB y) := by
      simp only [autHomOfCompIso_apply, Iso.conjAut_hom, Iso.conj_apply,
        NatTrans.comp_app, FintypeCat.comp_apply]
      congr 2
      exact (FintypeCat.hom_inv_id_apply ((overEquivFiberIso A xi').app PB) y).symm
    change autHomOfCompIso (overEquiv A).functor
      (overEquivFiberIso A xi') d = a at hd
    rw [hd] at heq
    have hyp : (overEquivFiberIso A xi').hom.app PB y = p := by
      exact FintypeCat.inv_hom_id_apply ((overEquivFiberIso A xi').app PB) p
    rw [hyp] at heq
    have hy' : (overEquivFiberIso A xi').hom.app PB y' = p' := by
      dsimp only [y']
      exact FintypeCat.inv_hom_id_apply ((overEquivFiberIso A xi').app PB) p'
    apply (ConcreteCategory.bijective_of_isIso
      ((overEquivFiberIso A xi').hom.app PB)).injective
    rw [hy', heq]
    have hpull : tPull.hom.app B (a.hom.app PB p) =
        (fundamentalGroupHom A.hom xi' a).hom.app B (tPull.hom.app B p) := by
      exact pullbackFiberIso_hom_fundamentalGroupHom_apply A.hom xi' a B p
    have hp : tPull.hom.app B p = b := by
      exact FintypeCat.inv_hom_id_apply (tPull.app B) b
    have hp' : tPull.hom.app B (tPull.inv.app B b') = b' := by
      exact FintypeCat.inv_hom_id_apply (tPull.app B) b'
    have hb' : (fundamentalGroupHom A.hom xi' a).hom.app B b = b' := by
      rfl
    change a.hom.app PB p = tPull.inv.app B b'
    apply (ConcreteCategory.bijective_of_isIso (tPull.hom.app B)).injective
    exact hpull.trans ((congrArg
      ((fundamentalGroupHom A.hom xi' a).hom.app B) hp).trans
        (hb'.trans hp'.symm))
  have hy := fiberOver_map_pullbackToProductOver A xi' B b
  have hy' := fiberOver_map_pullbackToProductOver A xi' B b'
  change d.hom.app ((productOver (X := A)).obj B)
      (productFiberEquivComparison F x B b) =
    productFiberEquivComparison F x B b'
  calc
    d.hom.app ((productOver (X := A)).obj B)
        (productFiberEquivComparison F x B b) =
      d.hom.app ((productOver (X := A)).obj B)
        ((fiberOver F x).map (pullbackToProductOver A B) y) :=
      congrArg (d.hom.app ((productOver (X := A)).obj B)) hy.symm
    _ = (fiberOver F x).map (pullbackToProductOver A B)
        (d.hom.app (toOverObj A ((pullback A.hom).obj B)) y) := by
      change
        ((fiberOver F x).map (pullbackToProductOver A B) ≫
          d.hom.app ((productOver (X := A)).obj B)) y =
        (d.hom.app (toOverObj A ((pullback A.hom).obj B)) ≫
          (fiberOver F x).map (pullbackToProductOver A B)) y
      exact ConcreteCategory.congr_hom
        (d.hom.naturality (pullbackToProductOver A B)) y
    _ = (fiberOver F x).map (pullbackToProductOver A B) y' :=
      congrArg ((fiberOver F x).map (pullbackToProductOver A B)) hdp
    _ = productFiberEquivComparison F x B b' := hy'

/-- The lifted-point stabilizer equivalence with the base point written as
the literal composite with the finite-etale covering map. -/
noncomputable def fundamentalGroupEquivStabilizerOfLiftOverComposite
    [ConnectedSpace S] (A : FiniteEtale S)
    (xi' : Spec (.of Omega) ⟶ A.left) :
    π₁ᵉᵗ(xi') ≃ₜ*
      MulAction.stabilizer (π₁ᵉᵗ(xi' ≫ A.hom))
        (liftedFiberPointOverComposite A xi') :=
  fundamentalGroupEquivStabilizerOfLift A xi'

/-- Transporting the stabilizer of a lifted fiber point along an equality of
base points gives the stabilizer of the corresponding point in the chosen
fiber. -/
theorem transported_stabilizer_liftedFiberPointOverComposite
    [ConnectedSpace S] (A : FiniteEtale S)
    (xi' : Spec (.of Omega) ⟶ A.left)
    {xi : Spec (.of Omega) ⟶ S} (hxi : xi' ≫ A.hom = xi) :
    (hxi ▸ MulAction.stabilizer (π₁ᵉᵗ(xi' ≫ A.hom))
      (liftedFiberPointOverComposite A xi')) =
        MulAction.stabilizer (π₁ᵉᵗ(xi))
          ((fiberObjEquivHom xi A).symm (Over.homMk xi' hxi)) := by
  subst xi
  rfl

/-- The stabilizer equivalence transported along an equality identifying the
composite of a lifted point with a chosen base point. -/
noncomputable def fundamentalGroupEquivStabilizerOfLiftOfEq
    [ConnectedSpace S] (A : FiniteEtale S)
    (xi' : Spec (.of Omega) ⟶ A.left)
    {xi : Spec (.of Omega) ⟶ S} (hxi : xi' ≫ A.hom = xi) :
    π₁ᵉᵗ(xi') ≃ₜ*
      ↥(show Subgroup π₁ᵉᵗ(xi) from
        hxi ▸ MulAction.stabilizer (π₁ᵉᵗ(xi' ≫ A.hom))
          (liftedFiberPointOverComposite A xi')) := by
  subst xi
  exact fundamentalGroupEquivStabilizerOfLiftOverComposite A xi'

/-- After transporting the base point equality, the stabilizer equivalence is
the homomorphism on fundamental groups induced by the covering map. -/
theorem fundamentalGroupEquivStabilizerOfLiftOfEq_coe
    [ConnectedSpace S] (A : FiniteEtale S)
    (xi' : Spec (.of Omega) ⟶ A.left)
    {xi : Spec (.of Omega) ⟶ S} (hxi : xi' ≫ A.hom = xi)
    (a : π₁ᵉᵗ(xi')) :
    ((fundamentalGroupEquivStabilizerOfLiftOfEq A xi' hxi a :
        ↥(show Subgroup π₁ᵉᵗ(xi) from
          hxi ▸ MulAction.stabilizer (π₁ᵉᵗ(xi' ≫ A.hom))
            (liftedFiberPointOverComposite A xi'))) : π₁ᵉᵗ(xi)) =
      hxi ▸ fundamentalGroupHom A.hom xi' a := by
  subst xi
  exact fundamentalGroupEquivStabilizerOfLift_coe A xi' a

end AlgebraicGeometry.FiniteEtale
