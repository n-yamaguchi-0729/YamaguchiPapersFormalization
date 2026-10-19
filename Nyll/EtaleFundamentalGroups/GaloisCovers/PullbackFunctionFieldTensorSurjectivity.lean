/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.GaloisCovers.FunctionFieldResidueAtSourceGeneric
import Nyll.EtaleFundamentalGroups.GaloisCovers.TensorProductSurjectivityTransport
import Nyll.SchemeTheory.FiniteEtale.BaseChange.PullbackResidueTensorProduct
import Nyll.EtaleFundamentalGroups.LocalGeometry.HeightOne.ComponentFunctionField

/-!
# Function-field tensors selected by a pullback component

The residue tensor of a pullback point has its two factor maps given by the
two pullback projections.  At the image of the generic point of an integral
closed component, these factor maps identify with the corresponding
function-field maps.
-/

noncomputable section

open CategoryTheory Limits TopologicalSpace
open scoped TensorProduct

namespace AlgebraicGeometry.Scheme.Pullback

universe u

variable {X Y S Z : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S}

/-- A surjective residue tensor at the generic point of an integral closed
component makes the corresponding canonical function-field product map
surjective.  The residue tensor is written in pullback order (`Y`, then
`X`), while the conclusion is written in function-field order (`X`, then
`Y`). -/
theorem functionFieldProductMap_surjective_of_pullback_generic_residue
    [IsIntegral X] [IsIntegral Y] [IsIntegral S] [IsIntegral Z]
    (f : X ⟶ S) (g : Y ⟶ S)
    (i : Z ⟶ pullback g f) [IsClosedImmersion i]
    (hX : DenseRange (i ≫ pullback.snd g f))
    (hY : DenseRange (i ≫ pullback.fst g f))
    [Algebra S.functionField X.functionField]
    [Algebra S.functionField Y.functionField]
    [Algebra S.functionField Z.functionField]
    (fX : X.functionField →ₐ[S.functionField] Z.functionField)
    (fY : Y.functionField →ₐ[S.functionField] Z.functionField)
    (hfX : fX.toRingHom =
      (i ≫ pullback.snd g f).functionFieldMap hX)
    (hfY : fY.toRingHom =
      (i ≫ pullback.fst g f).functionFieldMap hY)
    (hTensorSurjective :
      let t : ↑(pullback g f) := i (genericPoint Z)
      let T := Triplet.ofPoint t
      letI : Algebra (S.residueField T.s) (Y.residueField T.x) :=
        (((S.residueFieldCongr T.hx).inv ≫
          g.residueFieldMap T.x).hom).toAlgebra
      letI : Algebra (S.residueField T.s) (X.residueField T.y) :=
        (((S.residueFieldCongr T.hy).inv ≫
          f.residueFieldMap T.y).hom).toAlgebra
      Function.Surjective (tensorProductToResidueField t)) :
    Function.Surjective (Algebra.TensorProduct.productMap fX fY) := by
  let xMap : Z ⟶ X := i ≫ pullback.snd g f
  let yMap : Z ⟶ Y := i ≫ pullback.fst g f
  let t : ↑(pullback g f) := i (genericPoint Z)
  let T := Triplet.ofPoint t
  let : Algebra (S.residueField T.s) (Y.residueField T.x) :=
    (((S.residueFieldCongr T.hx).inv ≫
      g.residueFieldMap T.x).hom).toAlgebra
  let : Algebra (S.residueField T.s) (X.residueField T.y) :=
    (((S.residueFieldCongr T.hy).inv ≫
      f.residueFieldMap T.y).hom).toAlgebra
  let eXAt : X.functionField ≃+* X.residueField T.y := by
    change X.functionField ≃+*
      X.residueField (xMap (genericPoint Z))
    exact xMap.functionFieldResidueFieldRingEquivAtSourceGeneric hX
  let eYAt : Y.functionField ≃+* Y.residueField T.x := by
    change Y.functionField ≃+*
      Y.residueField (yMap (genericPoint Z))
    exact yMap.functionFieldResidueFieldRingEquivAtSourceGeneric hY
  let eZ := Scheme.functionFieldResidueFieldRingEquiv Z
  let eI : (pullback g f).residueField t ≃+*
      Z.residueField (genericPoint Z) := by
    change (pullback g f).residueField (i (genericPoint Z)) ≃+*
      Z.residueField (genericPoint Z)
    exact i.residueFieldRingEquivOfIsClosedImmersion (genericPoint Z)
  let eTarget : (pullback g f).residueField t ≃+* Z.functionField :=
    eI.trans eZ.symm
  let iResidue := i.residueFieldMap (genericPoint Z)
  let fstResidue := (pullback.fst g f).residueFieldMap t
  let sndResidue := (pullback.snd g f).residueFieldMap t
  have hyResidue :
      (yMap.residueFieldMap (genericPoint Z)).hom =
        iResidue.hom.comp fstResidue.hom := by
    have h := Scheme.residueFieldMap_comp
      (f := i) (g := pullback.fst g f) (genericPoint Z)
    change yMap.residueFieldMap (genericPoint Z) =
      fstResidue ≫ iResidue at h
    exact congrArg CommRingCat.Hom.hom h
  have hxResidue :
      (xMap.residueFieldMap (genericPoint Z)).hom =
        iResidue.hom.comp sndResidue.hom := by
    have h := Scheme.residueFieldMap_comp
      (f := i) (g := pullback.snd g f) (genericPoint Z)
    change xMap.residueFieldMap (genericPoint Z) =
      sndResidue ≫ iResidue at h
    exact congrArg CommRingCat.Hom.hom h
  have hYFactor (y : Y.functionField) :
      eTarget (fstResidue (eYAt y)) = fY y := by
    have hn := yMap.functionFieldResidueFieldRingEquivAtSourceGeneric_naturality hY
    have hn' := DFunLike.congr_fun (congrArg CommRingCat.Hom.hom hn) y
    change (yMap.residueFieldMap (genericPoint Z)).hom (eYAt y) =
      eZ (yMap.functionFieldMap hY y) at hn'
    rw [hyResidue] at hn'
    change eZ.symm (iResidue (fstResidue (eYAt y))) = fY y
    apply eZ.injective
    rw [eZ.apply_symm_apply]
    exact hn'.trans
      (congrArg eZ (DFunLike.congr_fun hfY.symm y))
  have hXFactor (x : X.functionField) :
      eTarget (sndResidue (eXAt x)) = fX x := by
    have hn := xMap.functionFieldResidueFieldRingEquivAtSourceGeneric_naturality hX
    have hn' := DFunLike.congr_fun (congrArg CommRingCat.Hom.hom hn) x
    change (xMap.residueFieldMap (genericPoint Z)).hom (eXAt x) =
      eZ (xMap.functionFieldMap hX x) at hn'
    rw [hxResidue] at hn'
    change eZ.symm (iResidue (sndResidue (eXAt x))) = fX x
    apply eZ.injective
    rw [eZ.apply_symm_apply]
    exact hn'.trans
      (congrArg eZ (DFunLike.congr_fun hfX.symm x))
  have hTensorLeftApply (y : Y.residueField T.x) :
      tensorProductToResidueField t
          (y ⊗ₜ[S.residueField T.s] (1 : X.residueField T.y)) =
        fstResidue y := by
    have hinc := DFunLike.congr_fun
      (congrArg CommRingCat.Hom.hom
        (includeLeft_tensorIsoTensorProduct_inv T)) y
    change (T.tensorIsoTensorProduct).inv
      ((Algebra.TensorProduct.includeLeftRingHom
        (R := S.residueField T.s) (A := Y.residueField T.x)
        (B := X.residueField T.y)) y) = T.tensorInl y at hinc
    change ofPointTensor t
      ((T.tensorIsoTensorProduct).inv
        ((Algebra.TensorProduct.includeLeftRingHom
          (R := S.residueField T.s) (A := Y.residueField T.x)
          (B := X.residueField T.y)) y)) = fstResidue y
    rw [hinc]
    have hdesc := DFunLike.congr_fun
      (congrArg CommRingCat.Hom.hom
        (pushout.inl_desc
          ((pullback.fst g f).residueFieldMap t)
          ((pullback.snd g f).residueFieldMap t)
          (residueFieldCongr_inv_residueFieldMap_ofPoint t))) y
    change ofPointTensor t (T.tensorInl y) = fstResidue y at hdesc
    exact hdesc
  have hTensorRightApply (x : X.residueField T.y) :
      tensorProductToResidueField t
          ((1 : Y.residueField T.x) ⊗ₜ[S.residueField T.s] x) =
        sndResidue x := by
    have hinc := DFunLike.congr_fun
      (congrArg CommRingCat.Hom.hom
        (includeRight_tensorIsoTensorProduct_inv T)) x
    change (T.tensorIsoTensorProduct).inv
      ((Algebra.TensorProduct.includeRight
        (R := S.residueField T.s) (A := Y.residueField T.x)
        (B := X.residueField T.y)) x) = T.tensorInr x at hinc
    change ofPointTensor t
      ((T.tensorIsoTensorProduct).inv
        ((Algebra.TensorProduct.includeRight
          (R := S.residueField T.s) (A := Y.residueField T.x)
          (B := X.residueField T.y)) x)) = sndResidue x
    rw [hinc]
    have hdesc := DFunLike.congr_fun
      (congrArg CommRingCat.Hom.hom
        (pushout.inr_desc
          ((pullback.fst g f).residueFieldMap t)
          ((pullback.snd g f).residueFieldMap t)
          (residueFieldCongr_inv_residueFieldMap_ofPoint t))) x
    change ofPointTensor t (T.tensorInr x) = sndResidue x at hdesc
    exact hdesc
  have hTensorPure (y : Y.residueField T.x)
      (x : X.residueField T.y) :
      tensorProductToResidueField t (y ⊗ₜ x) =
        fstResidue y * sndResidue x := by
    rw [show y ⊗ₜ[S.residueField T.s] x =
      (y ⊗ₜ (1 : X.residueField T.y)) *
        ((1 : Y.residueField T.x) ⊗ₜ x) by
        rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]]
    rw [map_mul, hTensorLeftApply, hTensorRightApply]
  apply
    Algebra.TensorProduct.productMap_surjective_of_surjective_reversed_tensor
      fX fY (tensorProductToResidueField t).hom eXAt eYAt eTarget
      hTensorSurjective
  intro x y
  rw [hTensorPure, map_mul, hYFactor, hXFactor, mul_comm]

end AlgebraicGeometry.Scheme.Pullback

end
