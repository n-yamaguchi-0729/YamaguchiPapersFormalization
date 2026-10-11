/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.GaloisCategories.Functoriality
import Mathlib.CategoryTheory.Comma.Over.Basic

/-!
# Fiber functors on pointed over-categories

For a finite fiber functor `F`, an object `X`, and a point `x` of its fiber,
we compare the automorphisms of `F` fixing `x` with the automorphisms of the
fiber-over-`x` functor on `Over X`.
-/

noncomputable section

universe u₁ u₂ w

open CategoryTheory Limits

namespace CategoryTheory.PreGaloisCategory

variable {C : Type u₁} [Category.{u₂} C]
variable (F : C ⥤ FintypeCat.{w})
variable {X : C} (x : F.obj X)

/-- The fiber over `x` of an object over `X`. -/
def fiberOver : Over X ⥤ FintypeCat.{w} where
  obj U := FintypeCat.of { y : F.obj U.left // F.map U.hom y = x }
  map {U V} f := FintypeCat.homMk fun y ↦
    ⟨F.map f.left y.1, by
      rw [← FintypeCat.comp_apply, ← F.map_comp, Over.w f]
      exact y.2⟩
  map_id U := by
    apply FintypeCat.hom_ext
    intro y
    change (⟨F.map (𝟙 U.left) y.1, _⟩ :
      { z : F.obj U.left // F.map U.hom z = x }) = y
    simp
  map_comp f g := by
    apply FintypeCat.hom_ext
    intro y
    apply Subtype.ext
    change F.map (f.left ≫ g.left) y.1 = F.map g.left (F.map f.left y.1)
    rw [F.map_comp]
    exact FintypeCat.comp_apply (F.map f.left) (F.map g.left) y.1

/-- The underlying point of a mapped element is obtained by applying `F` to
the underlying morphism in the over-category. -/
@[simp]
theorem fiberOver_map_val {U V : Over X} (f : U ⟶ V) (y : (fiberOver F x).obj U) :
    ((fiberOver F x).map f y).1 = F.map f.left y.1 :=
  rfl

variable [PreGaloisCategory C] [FiberFunctor F]

/-- Sending `Y` to the projection `Y ⨯ X ⟶ X` defines a functor into `Over X`. -/
def productOver : C ⥤ Over X where
  obj Y := Over.mk (prod.snd : Y ⨯ X ⟶ X)
  map {Y Z} f := Over.homMk (prod.map f (𝟙 X)) (by
    change prod.map f (𝟙 X) ≫ prod.snd = prod.snd
    simp)
  map_id Y := by
    ext
    change prod.map (𝟙 Y) (𝟙 X) = 𝟙 (Y ⨯ X)
    exact prod.map_id_id
  map_comp f g := by
    ext
    change prod.map (f ≫ g) (𝟙 X) = prod.map f (𝟙 X) ≫ prod.map g (𝟙 X)
    exact prod.map_comp_id f g

private def productFiberEquiv (Y : C) :
    F.obj Y ≃ (fiberOver F x).obj ((productOver (X := X)).obj Y) where
  toFun y :=
    ⟨(fiberBinaryProductEquiv F Y X).symm (y, x),
      fiberBinaryProductEquiv_symm_snd_apply F y x⟩
  invFun z := ((fiberBinaryProductEquiv F Y X) z.1).1
  left_inv y := by
    rw [← fiberBinaryProductEquiv_symm_fst_apply F y x]
    simp
  right_inv z := by
    apply Subtype.ext
    let e := fiberBinaryProductEquiv F Y X
    have hz : F.map (prod.snd : Y ⨯ X ⟶ X) z.1 = x := by
      exact z.2
    have hsnd : (e z.1).2 = x := by
      calc
        (e z.1).2 = F.map prod.snd (e.symm (e z.1)) :=
          (fiberBinaryProductEquiv_symm_snd_apply F (e z.1).1 (e z.1).2).symm
        _ = F.map prod.snd z.1 :=
          congrArg (F.map prod.snd) (e.symm_apply_apply z.1)
        _ = x := hz
    change e.symm ((e z.1).1, x) = z.1
    have hpair : ((e z.1).1, x) = e z.1 := by
      apply Prod.ext
      · rfl
      · exact hsnd.symm
    exact (congrArg e.symm hpair).trans (e.symm_apply_apply z.1)

private theorem fiberBinaryProductEquiv_apply (Y : C) (z : F.obj (Y ⨯ X)) :
    fiberBinaryProductEquiv F Y X z = (F.map prod.fst z, F.map prod.snd z) := by
  let e := fiberBinaryProductEquiv F Y X
  apply Prod.ext
  · calc
      (e z).1 = F.map prod.fst (e.symm (e z)) :=
        (fiberBinaryProductEquiv_symm_fst_apply F (e z).1 (e z).2).symm
      _ = F.map prod.fst z := congrArg (F.map prod.fst) (e.symm_apply_apply z)
  · calc
      (e z).2 = F.map prod.snd (e.symm (e z)) :=
        (fiberBinaryProductEquiv_symm_snd_apply F (e z).1 (e z).2).symm
      _ = F.map prod.snd z := congrArg (F.map prod.snd) (e.symm_apply_apply z)

private theorem productPoint_naturality {Y Z : C} (f : Y ⟶ Z) (y : F.obj Y) :
    F.map (prod.map f (𝟙 X)) ((fiberBinaryProductEquiv F Y X).symm (y, x)) =
      (fiberBinaryProductEquiv F Z X).symm (F.map f y, x) := by
  apply (fiberBinaryProductEquiv F Z X).injective
  rw [fiberBinaryProductEquiv_apply F]
  rw [Equiv.apply_symm_apply]
  apply Prod.ext
  · calc
      F.map prod.fst
          (F.map (prod.map f (𝟙 X)) ((fiberBinaryProductEquiv F Y X).symm (y, x))) =
          F.map (prod.map f (𝟙 X) ≫ prod.fst)
            ((fiberBinaryProductEquiv F Y X).symm (y, x)) := by
              rw [F.map_comp, FintypeCat.comp_apply]
      _ = F.map (prod.fst ≫ f) ((fiberBinaryProductEquiv F Y X).symm (y, x)) := by
        rw [prod.map_fst]
      _ = F.map f
          (F.map prod.fst ((fiberBinaryProductEquiv F Y X).symm (y, x))) := by
            rw [F.map_comp, FintypeCat.comp_apply]
      _ = F.map f y := by rw [fiberBinaryProductEquiv_symm_fst_apply]
  · calc
      F.map prod.snd
          (F.map (prod.map f (𝟙 X)) ((fiberBinaryProductEquiv F Y X).symm (y, x))) =
          F.map (prod.map f (𝟙 X) ≫ prod.snd)
            ((fiberBinaryProductEquiv F Y X).symm (y, x)) := by
              rw [F.map_comp, FintypeCat.comp_apply]
      _ = F.map prod.snd ((fiberBinaryProductEquiv F Y X).symm (y, x)) := by
        rw [prod.map_snd, Category.comp_id]
      _ = x := fiberBinaryProductEquiv_symm_snd_apply F y x

private theorem productFiberEquiv_naturality {Y Z : C} (f : Y ⟶ Z) (y : F.obj Y) :
    (fiberOver F x).map ((productOver (X := X)).map f) (productFiberEquiv F x Y y) =
      productFiberEquiv F x Z (F.map f y) := by
  apply Subtype.ext
  change
    F.map (prod.map f (𝟙 X)) ((fiberBinaryProductEquiv F Y X).symm (y, x)) =
      (fiberBinaryProductEquiv F Z X).symm (F.map f y, x)
  exact productPoint_naturality F x f y

/-- The original fiber functor is the restriction of `fiberOver F x` along
`Y ↦ (Y ⨯ X ⟶ X)`. -/
def productFiberIso :
    productOver (X := X) ⋙ fiberOver F x ≅ F :=
  (NatIso.ofComponents
    (fun Y ↦ FintypeCat.equivEquivIso (productFiberEquiv F x Y))
    (fun f ↦ by
      apply FintypeCat.hom_ext
      intro y
      exact (productFiberEquiv_naturality F x f y).symm)).symm

/-- Extend a natural automorphism of the fiber-over-`x` functor to the
original fiber functor by evaluating it on the projections `Y ⨯ X ⟶ X`. -/
def extendFiberOverAut : Aut (fiberOver F x) →ₜ* Aut F :=
  autHomOfCompIso (productOver (X := X)) (productFiberIso F x)

/-- The point comparison used to extend fiber-over automorphisms. -/
def productFiberEquivComparison (Y : C) :
    F.obj Y ≃ (fiberOver F x).obj ((productOver (X := X)).obj Y) :=
  productFiberEquiv F x Y

@[simp]
theorem productFiberEquivComparison_symm_apply
    (Y : C) (z : (fiberOver F x).obj ((productOver (X := X)).obj Y)) :
    (productFiberEquivComparison F x Y).symm z = F.map Limits.prod.fst z.1 :=
  by
    change (productFiberEquiv F x Y).symm z = _
    change ((fiberBinaryProductEquiv F Y X) z.1).1 = _
    exact congrArg (fun q ↦ q.1) (fiberBinaryProductEquiv_apply F Y z.1)

private theorem extendFiberOverAut_hom_app_apply
    (a : Aut (fiberOver F x)) (Y : C) (y : F.obj Y) :
    (extendFiberOverAut F x a).hom.app Y y =
      (productFiberEquiv F x Y).symm
        (a.hom.app ((productOver (X := X)).obj Y) (productFiberEquiv F x Y y)) := by
  rfl

/-- Evaluation formula for the extension of a fiber-over automorphism. -/
theorem extendFiberOverAut_hom_app_apply_eq
    (a : Aut (fiberOver F x)) (Y : C) (y : F.obj Y) :
    (extendFiberOverAut F x a).hom.app Y y =
      (productFiberEquivComparison F x Y).symm
        (a.hom.app ((productOver (X := X)).obj Y)
          (productFiberEquivComparison F x Y y)) :=
  extendFiberOverAut_hom_app_apply F x a Y y

/-- The graph of an object `U ⟶ X` as a morphism to the projection
`U ⨯ X ⟶ X`. -/
def graphToProduct (U : Over X) : U ⟶ (productOver (X := X)).obj U.left :=
  Over.homMk (prod.lift (𝟙 U.left) U.hom) (by
    change prod.lift (𝟙 U.left) U.hom ≫ prod.snd = U.hom
    exact prod.lift_snd (𝟙 U.left) U.hom)

private theorem graphPoint_eq_productPoint (U : Over X) (y : F.obj U.left)
    (hy : F.map U.hom y = x) :
    F.map (prod.lift (𝟙 U.left) U.hom) y =
      (fiberBinaryProductEquiv F U.left X).symm (y, x) := by
  apply (fiberBinaryProductEquiv F U.left X).injective
  rw [fiberBinaryProductEquiv_apply F, Equiv.apply_symm_apply]
  apply Prod.ext
  · change F.map prod.fst (F.map (prod.lift (𝟙 U.left) U.hom) y) = y
    rw [← FintypeCat.comp_apply, ← F.map_comp, prod.lift_fst, F.map_id]
    rfl
  · change F.map prod.snd (F.map (prod.lift (𝟙 U.left) U.hom) y) = x
    rw [← FintypeCat.comp_apply, ← F.map_comp, prod.lift_snd]
    exact hy

private theorem fiberOver_map_graphToProduct
    (U : Over X) (y : (fiberOver F x).obj U) :
    (fiberOver F x).map (graphToProduct (X := X) U) y =
      productFiberEquiv F x U.left y.1 := by
  apply Subtype.ext
  change F.map (prod.lift (𝟙 U.left) U.hom) y.1 =
    (fiberBinaryProductEquiv F U.left X).symm (y.1, x)
  exact graphPoint_eq_productPoint F x U y.1 y.2

private theorem extendFiberOverAut_fixes_point (a : Aut (fiberOver F x)) :
    extendFiberOverAut F x a • x = x := by
  let U : Over X := Over.mk (𝟙 X)
  let y : (fiberOver F x).obj U := ⟨x, by
    change F.map (𝟙 X) x = x
    rw [F.map_id]
    rfl⟩
  have hay : a.hom.app U y = y := by
    apply Subtype.ext
    have ha := (a.hom.app U y).2
    change F.map (𝟙 X) (a.hom.app U y).1 = x at ha
    rw [F.map_id] at ha
    exact ha
  have hnat :
      a.hom.app ((productOver (X := X)).obj U.left)
          ((fiberOver F x).map (graphToProduct (X := X) U) y) =
        (fiberOver F x).map (graphToProduct (X := X) U) (a.hom.app U y) := by
    simpa only [FintypeCat.comp_apply] using
      ConcreteCategory.congr_hom
        (a.hom.naturality (graphToProduct (X := X) U)) y
  have hfixProductU :
      a.hom.app ((productOver (X := X)).obj U.left)
          (productFiberEquiv F x U.left y.1) =
        productFiberEquiv F x U.left y.1 := by
    calc
      a.hom.app ((productOver (X := X)).obj U.left)
          (productFiberEquiv F x U.left y.1) =
          a.hom.app ((productOver (X := X)).obj U.left)
            ((fiberOver F x).map (graphToProduct (X := X) U) y) := by
              rw [fiberOver_map_graphToProduct]
      _ = (fiberOver F x).map (graphToProduct (X := X) U) (a.hom.app U y) := hnat
      _ = (fiberOver F x).map (graphToProduct (X := X) U) y :=
        congrArg ((fiberOver F x).map (graphToProduct (X := X) U)) hay
      _ = productFiberEquiv F x U.left y.1 := fiberOver_map_graphToProduct F x U y
  have hfixProduct :
      a.hom.app ((productOver (X := X)).obj X) (productFiberEquiv F x X x) =
        productFiberEquiv F x X x := by
    dsimp [U, y, Over.mk] at hfixProductU
    exact hfixProductU
  change (extendFiberOverAut F x a).hom.app X x = x
  rw [extendFiberOverAut_hom_app_apply, hfixProduct]
  exact (productFiberEquiv F x X).symm_apply_apply x

private def restrictAutToFiberOverObj
    (a : MulAction.stabilizer (Aut F) x) (U : Over X) :
    (fiberOver F x).obj U ≅ (fiberOver F x).obj U :=
  FintypeCat.equivEquivIso
    { toFun := fun y ↦
        ⟨a.1 • y.1, by
          calc
            F.map U.hom (a.1 • y.1) = a.1 • F.map U.hom y.1 :=
              (mulAction_naturality F a.1 U.hom y.1).symm
            _ = a.1 • x := congrArg (a.1 • ·) y.2
            _ = x := a.2⟩
      invFun := fun y ↦
        ⟨a.1⁻¹ • y.1, by
          calc
            F.map U.hom (a.1⁻¹ • y.1) = a.1⁻¹ • F.map U.hom y.1 :=
              (mulAction_naturality F a.1⁻¹ U.hom y.1).symm
            _ = a.1⁻¹ • x := congrArg (a.1⁻¹ • ·) y.2
            _ = x := by
              calc
                a.1⁻¹ • x = a.1⁻¹ • (a.1 • x) := congrArg (a.1⁻¹ • ·) a.2.symm
                _ = x := inv_smul_smul a.1 x⟩
      left_inv := fun y ↦ by apply Subtype.ext; simp
      right_inv := fun y ↦ by apply Subtype.ext; simp }

/-- Restrict an automorphism of `F` fixing `x` to the fibers over `x`. -/
def restrictAutToFiberOver :
    MulAction.stabilizer (Aut F) x →* Aut (fiberOver F x) where
  toFun a := NatIso.ofComponents (restrictAutToFiberOverObj F x a) (fun f ↦ by
    apply FintypeCat.hom_ext
    intro y
    apply Subtype.ext
    change a.1 • F.map f.left y.1 = F.map f.left (a.1 • y.1)
    exact mulAction_naturality F a.1 f.left y.1)
  map_one' := by
    ext U y
    rfl
  map_mul' a b := by
    ext U y
    rfl

private theorem extendFiberOverAut_restrictAutToFiberOver
    (a : MulAction.stabilizer (Aut F) x) :
    extendFiberOverAut F x (restrictAutToFiberOver F x a) = a.1 := by
  apply Aut.ext
  ext Y y
  rw [extendFiberOverAut_hom_app_apply]
  change
    ((fiberBinaryProductEquiv F Y X)
      (a.1 • (fiberBinaryProductEquiv F Y X).symm (y, x))).1 = a.1 • y
  rw [fiberBinaryProductEquiv_apply]
  change F.map prod.fst
      (a.1 • (fiberBinaryProductEquiv F Y X).symm (y, x)) = a.1 • y
  calc
    F.map prod.fst (a.1 • (fiberBinaryProductEquiv F Y X).symm (y, x)) =
        a.1 • F.map prod.fst ((fiberBinaryProductEquiv F Y X).symm (y, x)) :=
      (mulAction_naturality F a.1 prod.fst _).symm
    _ = a.1 • y := congrArg (a.1 • ·)
      (fiberBinaryProductEquiv_symm_fst_apply F y x)

private theorem restrictAutToFiberOver_extendFiberOverAut
    (a : Aut (fiberOver F x)) :
    restrictAutToFiberOver F x
        ⟨extendFiberOverAut F x a, extendFiberOverAut_fixes_point F x a⟩ = a := by
  apply Aut.ext
  ext U y
  apply Subtype.ext
  change (extendFiberOverAut F x a).hom.app U.left y.1 = (a.hom.app U y).1
  rw [extendFiberOverAut_hom_app_apply]
  have hnat :
      a.hom.app ((productOver (X := X)).obj U.left)
          ((fiberOver F x).map (graphToProduct (X := X) U) y) =
        (fiberOver F x).map (graphToProduct (X := X) U) (a.hom.app U y) := by
    simpa only [FintypeCat.comp_apply] using
      ConcreteCategory.congr_hom
        (a.hom.naturality (graphToProduct (X := X) U)) y
  have hproduct :
      a.hom.app ((productOver (X := X)).obj U.left)
          (productFiberEquiv F x U.left y.1) =
        productFiberEquiv F x U.left (a.hom.app U y).1 := by
    calc
      a.hom.app ((productOver (X := X)).obj U.left)
          (productFiberEquiv F x U.left y.1) =
          a.hom.app ((productOver (X := X)).obj U.left)
            ((fiberOver F x).map (graphToProduct (X := X) U) y) := by
              rw [fiberOver_map_graphToProduct]
      _ = (fiberOver F x).map (graphToProduct (X := X) U) (a.hom.app U y) := hnat
      _ = productFiberEquiv F x U.left (a.hom.app U y).1 :=
        fiberOver_map_graphToProduct F x U (a.hom.app U y)
  rw [hproduct]
  exact (productFiberEquiv F x U.left).symm_apply_apply (a.hom.app U y).1

/-- Extension identifies the automorphism group of the fiber-over-`x`
functor with the stabilizer of `x` in `Aut F`. -/
noncomputable def autFiberOverMulEquivStabilizer :
    Aut (fiberOver F x) ≃* MulAction.stabilizer (Aut F) x where
  toFun a := ⟨extendFiberOverAut F x a, extendFiberOverAut_fixes_point F x a⟩
  invFun := restrictAutToFiberOver F x
  left_inv := restrictAutToFiberOver_extendFiberOverAut F x
  right_inv a := by
    apply Subtype.ext
    exact extendFiberOverAut_restrictAutToFiberOver F x a
  map_mul' a b := by
    apply Subtype.ext
    exact (extendFiberOverAut F x).map_mul a b

/-- The stabilizer comparison is an isomorphism of topological groups. -/
noncomputable def autFiberOverEquivStabilizer :
    Aut (fiberOver F x) ≃ₜ* MulAction.stabilizer (Aut F) x where
  toMulEquiv := autFiberOverMulEquivStabilizer F x
  continuous_toFun := (extendFiberOverAut F x).continuous.subtype_mk _
  continuous_invFun :=
    Continuous.continuous_symm_of_equiv_compact_to_t2
      (f := (autFiberOverMulEquivStabilizer F x).toEquiv)
      ((extendFiberOverAut F x).continuous.subtype_mk _)

end CategoryTheory.PreGaloisCategory
