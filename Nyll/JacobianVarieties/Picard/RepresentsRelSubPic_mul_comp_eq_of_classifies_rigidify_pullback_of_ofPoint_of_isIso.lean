/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_mul_comp_eq_of_classifies_rigidify_pullback_of_ofPoint_of_isIso.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.Util.WithWeakNamespace
import Mathlib.CategoryTheory.Iso
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.CategoryTheory.MorphismProperty.Limits
import Mathlib.CategoryTheory.Comma.Over.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Nyll.AlgebraicCurves.Geometry.Picard.RelativeGroupLaw
import Nyll.AlgebraicCurves.Geometry.Schemes.SchemeHomOver
import Nyll.AlgebraicCurves.Geometry.Picard.Functor
import Nyll.JacobianVarieties.Picard.Representation
import Nyll.AlgebraicCurves.Geometry.Picard.AlgEquivZeroCut
import Nyll.AlgebraicCurves.Geometry.Picard.AlgEquivZeroGroupCut
import Nyll.AlgebraicCurves.Geometry.Picard.RelSubPic.Group
import Nyll.SchemeTheory.Modules.Monoidal
import Nyll.AlgebraicCurves.Geometry.Sheaves.IdealSheafModule
import Nyll.AlgebraicCurves.RelativeDivisors.RelEffCartierDiv
import Nyll.AlgebraicCurves.RelativeDivisors.RelEffCartierDivOfPoint
import Nyll.AlgebraicCurves.Geometry.Picard.Pullback
import Nyll.AlgebraicCurves.Geometry.Sheaves.ModulesRigidify
import Nyll.AlgebraicCurves.Geometry.Sheaves.ModulesNormModule
import Nyll.AlgebraicCurves.Geometry.Schemes.RigidifiedLineBundleOfInvertible
import Nyll.SchemeTheory.Modules.PullbackMonoidal
import Nyll.JacobianVarieties.Picard.RepresentsRelSubPic_nonempty_poincare_pullbackAlong_mul_iso
import Nyll.AlgebraicCurves.Geometry.Schemes.Scheme_Hom_isInvertible_ker_of_comp_eq_id_of_mem_opens
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_IdealSheafData_IsInvertible_isInvertible_module
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_IdealSheafData_IsInvertible_isInvertible_invModule
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_IsInvertible_dual
import Nyll.AlgebraicCurves.Geometry.Schemes.Scheme_Hom_nonempty_pullback_ker_pow_invModule_iso_of_isIso
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_IdealSheafData_IsInvertible_nonempty_module_tensor_invModule_iso

import Nyll.JacobianVarieties.Picard.RepresentsRelSubPicPullback
import Nyll.JacobianVarieties.Picard.RepresentsRelSubPicGroup
/-!
# Point divisors and Picard multiplication under a curve isomorphism

Pullback identifies the line bundles and ideal modules of corresponding points.
Combining these identifications with rigidification and the Poincare tensor product
shows that the induced Picard map carries the specified point classes to their product.
-/

section ProofImplementation

namespace JacobianVarieties.Picard.Proofs.PointPullback
attribute [-simp]
  AlgebraicGeometry.Scheme.Modules.toUnitSection_ofUnitSection
  AlgebraicGeometry.Scheme.Modules.pullbackSection_def
  AlgebraicGeometry.Scheme.Modules.ofUnitSection_toUnitSection


open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory
open _root_.AlgebraicGeometry
open _root_.AlgebraicGeometry.RelPicard
open _root_.NeronModelInfra
open _root_.GoodReductionJacobian


universe u

noncomputable section

namespace GenPullIsoAJ

theorem poincare_mul {R : Type u} [CommRing R] {C : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of R)}
    {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c}
    {P : SubPicGroupCondition c ε} {D : RelativePic0Designation R c}
    (h : RepresentsRelSubPic c ε P.toSubPicCondition D)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t D.toBase) :
    Nonempty ((h.poincare.pullbackAlong (h.relativeGroupLaw.mul t x y)).L ≅
      (h.poincare.pullbackAlong x).L ⊗ (h.poincare.pullbackAlong y).L) :=
  h.nonempty_poincare_pullbackAlong_mul_iso (T := Over.mk t)
    (schemeHomOverToOverHom x) (schemeHomOverToOverHom y)

theorem isInvertible_I_ofPoint_field {R : Type u} [CommRing R] {K : Type u} [Field K]
    {C : Scheme.{u}}
    (c : C ⟶ Spec (CommRingCat.of R)) [IsSeparated c]
    (t : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of R))
    [SmoothOfRelativeDimension 1 (pullback.snd c t)]
    (x : Spec (CommRingCat.of K) ⟶ C) (hx : x ≫ c = t) :
    (RelEffCartierDiv.ofPoint c x hx).I.IsInvertible := by
  have : IsSeparated (pullback.snd c t) := inferInstance
  have : SmoothOfRelativeDimension 1 ((⊤ : (pullback c t).Opens).ι ≫ pullback.snd c t) := by
    have : SmoothOfRelativeDimension (0 + 1) ((⊤ : (pullback c t).Opens).ι ≫ pullback.snd c t) :=
      inferInstance
    simpa only [Nat.zero_add] using this
  exact Scheme.Hom.isInvertible_ker_of_comp_eq_id_of_mem_opens
    (pullback.snd c t) ⊤ (graphOver c x hx)
    (graphOver_snd c x hx) trivial

theorem pull_ofPoint {R : Type u} [CommRing R] {K : Type u} [Field K] {C C' : Scheme.{u}}
    (c : C ⟶ Spec (CommRingCat.of R))
    (c' : C' ⟶ Spec (CommRingCat.of R)) [IsSeparated c] [IsSeparated c']
    (t : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of R))
    [SmoothOfRelativeDimension 1 (pullback.snd c t)]
    [SmoothOfRelativeDimension 1 (pullback.snd c' t)]
    (π : C' ⟶ C) (hπ : π ≫ c = c') [IsIso π]
    (y : Spec (CommRingCat.of K) ⟶ C) (hy : y ≫ c = t)
    (y' : Spec (CommRingCat.of K) ⟶ C')
    (hy' : y' ≫ c' = t)
    (hyy : y' ≫ π = y) :
    Nonempty ((Scheme.Modules.pullback (curveChange π hπ t)).obj
      (RelEffCartierDiv.ofPoint c y hy).lineBundle ≅
        (RelEffCartierDiv.ofPoint c' y' hy').lineBundle) ∧
      Nonempty ((Scheme.Modules.pullback (curveChange π hπ t)).obj
        (RelEffCartierDiv.ofPoint c y hy).idealModule ≅
        (RelEffCartierDiv.ofPoint c' y' hy').idealModule) := by
  have : IsIso (curveChange π hπ t) := by unfold curveChange; infer_instance
  have hg : graphOver c' y' hy' ≫ curveChange π hπ t = graphOver c y hy := by
    apply pullback.hom_ext
    · simp only [curveChange, Category.assoc, pullback.lift_fst,
        graphOver_fst_assoc, hyy, graphOver_fst]
    · simp only [curveChange, Category.assoc, pullback.lift_snd, Category.comp_id, graphOver_snd]
  have hI := isInvertible_I_ofPoint_field c t y hy
  have hI' := isInvertible_I_ofPoint_field c' t y' hy'
  obtain ⟨⟨e₁⟩, ⟨e₂⟩⟩ :=
    Scheme.Hom.nonempty_pullback_ker_pow_invModule_iso_of_isIso (curveChange π hπ t)
    (graphOver c y hy) (graphOver c' y' hy') hg hI hI' 1
  simp only [pow_one] at e₁ e₂
  exact ⟨⟨e₁⟩, ⟨e₂⟩⟩

end GenPullIsoAJ

end

open GenPullIsoAJ in
with_weak_namespace _root_.AlgebraicGeometry.RelPicard.RepresentsRelSubPic
theorem mul_comp_eq_of_classifies_rigidify_pullback_of_ofPoint_of_isIso
    {R : Type u} [CommRing R] {C C' : Scheme.{u}}
    {c : C ⟶ Spec (CommRingCat.of R)}
    {c' : C' ⟶ Spec (CommRingCat.of R)} [IsSeparated c] [IsSeparated c']
    {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c}
    {ε' : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c'}
    {D : RelativePic0Designation R c} {D' : RelativePic0Designation R c'}
    (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)
    (h' : RepresentsRelSubPic c' ε' (algEquivZeroCut c' ε') D')
    (π : C' ⟶ C) (hπ : π ≫ c = c') [IsIso π]
    (N : SchemeHomOver D.toBase D'.toBase)
    (hN : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (a : SchemeHomOver t D.toBase),
      Nonempty ((h'.poincare.pullbackAlong (NeronModelInfra.schemeHomOverComp a N)).L ≅
        Scheme.Modules.rigidify (rigSection c' t ε') (pullback.snd c' t)
          ((Scheme.Modules.pullback (curveChange π hπ t)).obj (h.poincare.pullbackAlong a).L)))
    {K : Type u} [Field K] (t : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of R))
    [SmoothOfRelativeDimension 1 (pullback.snd c t)]
    [SmoothOfRelativeDimension 1 (pullback.snd c' t)]
    (y : SchemeHomOver t c) (y' xe : SchemeHomOver t c')
    (hy' : y'.1 ≫ π = y.1) (hxe : xe.1 ≫ π = t ≫ ε.1)
    (a : SchemeHomOver t D.toBase)
    (ha : Nonempty ((h.poincare.pullbackAlong a).L ≅
      (RelEffCartierDiv.ofPoint c y.1 y.2).lineBundle ⊗
        (RelEffCartierDiv.ofPoint c (t ≫ ε.1)
          ((Category.assoc _ _ _).trans
            ((congrArg (t ≫ ·) ε.2).trans (Category.comp_id t)))).idealModule))
    (b g : SchemeHomOver t D'.toBase)
    (hb : Nonempty ((h'.poincare.pullbackAlong b).L ≅
      (RelEffCartierDiv.ofPoint c' xe.1 xe.2).lineBundle ⊗
        (RelEffCartierDiv.ofPoint c' (t ≫ ε'.1)
          ((Category.assoc _ _ _).trans
            ((congrArg (t ≫ ·) ε'.2).trans (Category.comp_id t)))).idealModule))
    (hg : Nonempty ((h'.poincare.pullbackAlong g).L ≅
      (RelEffCartierDiv.ofPoint c' y'.1 y'.2).lineBundle ⊗
        (RelEffCartierDiv.ofPoint c' (t ≫ ε'.1)
          ((Category.assoc _ _ _).trans
            ((congrArg (t ≫ ·) ε'.2).trans (Category.comp_id t)))).idealModule)) :
    (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c' ε') h').mul t
      (NeronModelInfra.schemeHomOverComp a N) b = g := by
  have pε : (t ≫ ε.1) ≫ c = t :=
    (Category.assoc _ _ _).trans ((congrArg (t ≫ ·) ε.2).trans (Category.comp_id t))
  have pε' : (t ≫ ε'.1) ≫ c' = t :=
    (Category.assoc _ _ _).trans ((congrArg (t ≫ ·) ε'.2).trans (Category.comp_id t))
  let M : RigidifiedLineBundle c ε t := h.poincare.pullbackAlong a
  have hinvM :
      Scheme.Modules.IsInvertible ((Scheme.Modules.pullback (curveChange π hπ t)).obj M.L) :=
    M.isInvertible.pullback _
  obtain ⟨e1⟩ : Nonempty ((h'.poincare.pullbackAlong (NeronModelInfra.schemeHomOverComp a N)).L ≅
      (RigidifiedLineBundle.ofInvertible (ε := ε')
        ((Scheme.Modules.pullback (curveChange π hπ t)).obj M.L) hinvM).L) := hN t a
  have hIxe := isInvertible_I_ofPoint_field c' t xe.1 xe.2
  have hOxe : Scheme.Modules.IsInvertible (RelEffCartierDiv.ofPoint c' xe.1 xe.2).lineBundle :=
    hIxe.isInvertible_invModule
  have hIxe' : Scheme.Modules.IsInvertible (RelEffCartierDiv.ofPoint c' xe.1 xe.2).idealModule :=
    hIxe.isInvertible_module
  have hIε' :
      Scheme.Modules.IsInvertible (RelEffCartierDiv.ofPoint c' (t ≫ ε'.1) pε').idealModule :=
    (isInvertible_I_ofPoint_field c' t (t ≫ ε'.1) pε').isInvertible_module
  have hOy' : Scheme.Modules.IsInvertible (RelEffCartierDiv.ofPoint c' y'.1 y'.2).lineBundle :=
    (isInvertible_I_ofPoint_field c' t y'.1 y'.2).isInvertible_invModule
  obtain ⟨iM⟩ := ha
  obtain ⟨ib⟩ := hb
  obtain ⟨ig⟩ := hg
  obtain ⟨⟨n1⟩, -⟩ := pull_ofPoint c c' t π hπ y.1 y.2 y'.1 y'.2 hy'
  obtain ⟨-, ⟨n2⟩⟩ := pull_ofPoint c c' t π hπ (t ≫ ε.1) pε xe.1 xe.2 hxe
  let t1 := Scheme.Modules.pullbackTensorObjIso (curveChange π hπ t)
    (RelEffCartierDiv.ofPoint c y.1 y.2).lineBundle
    (RelEffCartierDiv.ofPoint c (t ≫ ε.1) pε).idealModule
  obtain ⟨mi, -⟩ := hIxe.nonempty_module_tensor_invModule_iso
  obtain ⟨mi⟩ := mi
  have raw : (Scheme.Modules.pullback (curveChange π hπ t)).obj M.L ⊗
      (h'.poincare.pullbackAlong b).L ≅
      (h'.poincare.pullbackAlong g).L :=
    (((Scheme.Modules.pullback (curveChange π hπ t)).mapIso iM ≪≫ t1 ≪≫ (n1 ⊗ᵢ n2)) ⊗ᵢ ib) ≪≫
    α_ _ _ _ ≪≫
    (Iso.refl _ ⊗ᵢ ((α_ _ _ _).symm ≪≫ (mi ⊗ᵢ Iso.refl _) ≪≫ λ_ _)) ≪≫
    ig.symm
  obtain ⟨r1⟩ := RigidifiedLineBundle.nonempty_ofInvertible_iso_of_rigidified
    (h'.poincare.pullbackAlong b)
  obtain ⟨r2⟩ := RigidifiedLineBundle.nonempty_ofInvertible_tensor_iso (ε := ε') hinvM
    (h'.poincare.pullbackAlong b).isInvertible
  obtain ⟨r3⟩ := RigidifiedLineBundle.nonempty_ofInvertible_iso_of_iso (ε := ε')
    (hinvM.tensor (h'.poincare.pullbackAlong b).isInvertible)
    (h'.poincare.pullbackAlong g).isInvertible raw
  obtain ⟨r4⟩ := RigidifiedLineBundle.nonempty_ofInvertible_iso_of_rigidified
    (h'.poincare.pullbackAlong g)
  have key : (RigidifiedLineBundle.ofInvertible (ε := ε')
        ((Scheme.Modules.pullback (curveChange π hπ t)).obj M.L) hinvM).L ⊗
      (h'.poincare.pullbackAlong b).L ≅ (h'.poincare.pullbackAlong g).L :=
    (Iso.refl _ ⊗ᵢ r1.symm) ≪≫ r2.symm ≪≫ r3 ≪≫ r4
  obtain ⟨emul⟩ := poincare_mul (P := algEquivZeroGroupCut c' ε') h' t
    (NeronModelInfra.schemeHomOverComp a N) b
  exact h'.ext_of_iso t _ _ ⟨emul ≪≫ (e1 ⊗ᵢ Iso.refl _) ≪≫ key⟩
end JacobianVarieties.Picard.Proofs.PointPullback
end ProofImplementation

attribute [-instance]
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instNeg
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulInt
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAddCommGroup
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAdd
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSub
open _root_.AlgebraicGeometry.Scheme.IdealSheafData.IdealHom in
attribute [-instance]
  instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop
open _root_.AlgebraicGeometry.Scheme.IdealSheafData.IdealHom in
attribute [-instance]
  instSMulCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop
attribute [-instance]
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulNat
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instZero
attribute [-simp]
  AlgebraicGeometry.RelPicard.rigSection_snd
  AlgebraicGeometry.RelPicard.RigidifiedLineBundle.ofInvertible_L
  AlgebraicGeometry.RelPicard.rigSection_snd_assoc
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.sub_app
  AlgebraicGeometry.Scheme.IdealSheafData.sres_sresTop
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.add_app
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.sizeOf_spec
  AlgebraicGeometry.Scheme.IdealSheafData.coe_resLE
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.smul_app
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_ofLE_app
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.ideal_range
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zero_app
  AlgebraicGeometry.Scheme.IdealSheafData.sres_sres
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.comp_app
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.neg_app
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.id_app
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_mulRight_app
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.nsmul_app
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.injEq
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zsmul_app
  AlgebraicGeometry.Scheme.Modules.toUnitSection_ofUnitSection
  AlgebraicGeometry.Scheme.Modules.pullbackSection_def
  AlgebraicGeometry.Scheme.Modules.ofUnitSection_toUnitSection
