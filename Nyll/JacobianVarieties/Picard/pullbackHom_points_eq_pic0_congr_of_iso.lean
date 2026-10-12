/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_RelPicard_pullbackHom_points_eq_pic0_congr_of_iso.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Geometry.Picard.Functor
import Nyll.JacobianVarieties.Picard.Representation
import Nyll.AlgebraicCurves.Geometry.Picard.AlgEquivZeroCut
import Nyll.AlgebraicCurves.Geometry.Picard.AlgEquivZeroGroupCut
import Nyll.AlgebraicCurves.Geometry.Picard.RelSubPic.Group
import Nyll.AlgebraicCurves.Geometry.Picard.Pullback
import Nyll.AlgebraicCurves.Geometry.Picard.RelativeGroupLaw
import Nyll.AlgebraicCurves.Models.Basic
import Nyll.AlgebraicCurves.FunctionFields.CurveOver
import Nyll.AlgebraicCurves.Divisors.Maps
import Nyll.SchemeTheory.Modules.Monoidal
import Nyll.AlgebraicCurves.Geometry.Sheaves.IdealSheafModule
import Nyll.AlgebraicCurves.RelativeDivisors.RelEffCartierDiv
import Nyll.AlgebraicCurves.RelativeDivisors.RelEffCartierDivOfPoint
import Nyll.AlgebraicCurves.Divisors.Pic0Congr
import Nyll.AlgebraicCurves.Geometry.Curves.SmoothProperCurveBase
import Nyll.JacobianVarieties.Picard.RepresentsRelSubPic_mul_comp_eq_of_classifies_rigidify_pullback_of_ofPoint_of_isIso
import Nyll.JacobianVarieties.Picard.RepresentsRelSubPic_nonempty_poincare_pullbackAlong_schemeHomOverComp_pullbackHom_iso_rigidify

import Nyll.JacobianVarieties.Picard.RepresentsRelSubPicPullback
import Nyll.JacobianVarieties.Picard.RepresentsRelSubPicGroup
/-!
# Pullback on Picard points and congruence of function fields
-/

section ProofImplementation

namespace JacobianVarieties.Picard.Proofs.PicardPointsTransport
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

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory
open _root_.AlgebraicGeometry
open _root_.AlgebraicGeometry.RelPicard
open _root_.NeronModelInfra
open _root_.GoodReductionJacobian
open _root_.AlgebraicCurve


universe u v

namespace PtsIntertwineIso

section Generic

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

/-- The degree-zero divisor of a point relative to a chosen base point. -/
noncomputable def gen (hdeg : ∀ v : Place K F, v.deg = 1) (Q₀ P : Place K F) :
    Divisor.degZero (K := K) (F := F) :=
  ⟨Finsupp.single P 1 - Finsupp.single Q₀ 1, by
    rw [Divisor.mem_degZero, map_sub, Divisor.degree_single, Divisor.degree_single, hdeg, hdeg]
    norm_num⟩

/-- The underlying divisor of a point-difference generator. -/
@[scoped simp] theorem coe_gen (hdeg : ∀ v : Place K F, v.deg = 1) (Q₀ P : Place K F) :
    (gen hdeg Q₀ P : Divisor K F) = Finsupp.single P 1 - Finsupp.single Q₀ 1 := rfl

/-- Point-difference classes generate Pic0 when every place has degree one. -/
theorem closure_range_mk_gen_eq_top (hdeg : ∀ v : Place K F, v.deg = 1) (Q₀ : Place K F) :
    AddSubgroup.closure (Set.range fun P : Place K F => Pic0.mk (gen hdeg Q₀ P)) = ⊤ := by
  classical
  set S := AddSubgroup.closure (Set.range fun P : Place K F => Pic0.mk (gen hdeg Q₀ P)) with hS
  let θ : Divisor K F →+ Divisor K F :=
    AddMonoidHom.id _ - (zmultiplesHom (Divisor K F) (Finsupp.single Q₀ 1)).comp Divisor.degree
  have hθ : ∀ E : Divisor K F, θ E = E - Divisor.degree E • Finsupp.single Q₀ 1 := fun E => by
    simp only [θ, AddMonoidHom.sub_apply, AddMonoidHom.id_apply,
      AddMonoidHom.comp_apply, zmultiplesHom_apply]
  have hθmem : ∀ E : Divisor K F, θ E ∈ Divisor.degZero (K := K) (F := F) := by
    intro E
    rw [Divisor.mem_degZero, hθ, map_sub, map_zsmul, Divisor.degree_single, hdeg]
    simp only [Nat.cast_one, mul_one, smul_eq_mul, sub_self]
  let ψ : Divisor K F →+ Pic0 K F := (QuotientAddGroup.mk' _).comp (θ.codRestrict _ hθmem)
  have hψ : ∀ E : Divisor K F, ψ E = Pic0.mk ⟨θ E, hθmem E⟩ := fun E => rfl
  have hψS : ∀ E : Divisor K F, ψ E ∈ S := by
    intro E
    induction E using Finsupp.induction with
    | zero => rw [map_zero]; exact S.zero_mem
    | single_add a b f _ _ ih =>
      rw [map_add]
      refine S.add_mem ?_ ih
      have h1 : ψ (Finsupp.single a 1) = Pic0.mk (gen hdeg Q₀ a) := by
        rw [hψ]; congr 1; apply Subtype.ext
        simp only [coe_gen, hθ, Divisor.degree_single, hdeg, Nat.cast_one, mul_one, one_smul]
      have hb : Finsupp.single a b = b • Finsupp.single a (1 : ℤ) := by
        rw [Finsupp.smul_single, smul_eq_mul, mul_one]
      rw [hb, map_zsmul, h1]
      exact S.zsmul_mem (AddSubgroup.subset_closure ⟨a, rfl⟩) b
  rw [eq_top_iff]
  rintro c -
  obtain ⟨D, rfl⟩ := Pic0.mk_surjective c
  have hD : Pic0.mk D = ψ (D : Divisor K F) := by
    rw [hψ]; congr 1; apply Subtype.ext
    simp only [hθ, (Divisor.mem_degZero.mp D.2), zero_smul, sub_zero]
  rw [hD]; exact hψS _

/-- Additive maps from Pic0 agree if they agree on all point-difference generators. -/
theorem addMonoidHom_ext_of_gen {G : Type*} [AddGroup G] (hdeg : ∀ v : Place K F, v.deg = 1)
    (Q₀ : Place K F)
    {f g : Pic0 K F →+ G} (h : ∀ P : Place K F, f (Pic0.mk (gen hdeg Q₀ P)) = g (Pic0.mk (gen hdeg
      Q₀ P))) :
    f = g :=
  AddMonoidHom.eq_of_eqOn_dense (closure_range_mk_gen_eq_top hdeg Q₀)
    (by rintro _ ⟨P, rfl⟩; exact h P)

end Generic

end PtsIntertwineIso

attribute [local simp] PtsIntertwineIso.coe_gen


open PtsIntertwineIso

namespace RepIsoPII

section PullbackHomMul

open scoped CategoryTheory.MonObj

variable {R : Type u} [CommRing R] {C C' : Scheme.{u}}
  {c : C ⟶ Spec (CommRingCat.of R)} {c' : C' ⟶ Spec (CommRingCat.of R)}
  {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c} {ε' : SchemeHomOver (𝟙 (Spec (CommRingCat.of
    R))) c'}
  {D : RelativePic0Designation R c} {D' : RelativePic0Designation R c'}

/-- Pullback along the curve preserves the tensor product of rigidified line bundles. -/
theorem nonempty_tensor_pullbackCurve_iso (f : C' ⟶ C) (hf : f ≫ c = c') (hε : ε'.1 ≫ f = ε.1)
    {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} (L M : RigidifiedLineBundle c ε t) :
    Nonempty (((L.tensor M).pullbackCurve f hf hε).L ≅ ((L.pullbackCurve f hf hε).tensor
      (M.pullbackCurve f hf hε)).L) :=
  ⟨Scheme.Modules.pullbackTensorObjIso _ _ _⟩

/-- The Poincare bundle at a product is the tensor product of its two pullbacks. -/
theorem nonempty_pullbackAlong_mul_iso (P : SubPicGroupCondition c ε)
    (h : RepresentsRelSubPic c ε P.toSubPicCondition D)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (a b : SchemeHomOver t D.toBase) :
    Nonempty ((h.poincare.pullbackAlong (h.relativeGroupLaw.mul t a b)).L ≅
      ((h.poincare.pullbackAlong a).tensor (h.poincare.pullbackAlong b)).L) := by
  let : GrpObj (Over.mk D.toBase) := h.grpObj
  let : CommGroup ((relSubPicPresheaf c ε P.toSubPicCondition).obj
      (Opposite.op (Over.mk t))) := P.commGroupObj (Opposite.op (Over.mk t))
  have key := congrArg Subtype.val (h.homEquiv_mul (Over.mk t) (schemeHomOverToOverHom a)
    (schemeHomOverToOverHom b))
  have hl : (h.representableBy.homEquiv (schemeHomOverToOverHom a * schemeHomOverToOverHom b)).1 =
      Quotient.mk _ (h.poincare.pullbackAlong (h.relativeGroupLaw.mul t a b)) := rfl
  have hr : ((h.representableBy.homEquiv (schemeHomOverToOverHom a)) *
      (h.representableBy.homEquiv (schemeHomOverToOverHom b))).1 =
      Quotient.mk _ ((h.poincare.pullbackAlong a).tensor (h.poincare.pullbackAlong b)) := rfl
  rw [hl, hr] at key
  exact Quotient.exact key

/-- The representing pullback map classifies pullback along the curve. -/
theorem nonempty_pullbackAlong_postComp_pullbackHom_iso (f : C' ⟶ C) (hf : f ≫ c = c')
    (hε : ε'.1 ≫ f = ε.1)
    (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D) (h' : RepresentsRelSubPic c' ε'
      (algEquivZeroCut c' ε') D')
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver t D.toBase) :
    Nonempty ((h'.poincare.pullbackAlong (postComp (RepresentsRelSubPic.pullbackHom f hf hε h h')
      x)).L ≅
      ((h.poincare.pullbackAlong x).pullbackCurve f hf hε).L) := by
  have hPx : (algEquivZeroCut c ε).P t (h.poincare.pullbackAlong x) :=
    (algEquivZeroCut c ε).pullback_mem _ _ x _ h.poincare_mem
  have hx : x = h.classify t (h.poincare.pullbackAlong x) hPx := h.classify_unique t _ hPx x
    ⟨Iso.refl _⟩
  have hx' : postComp (RepresentsRelSubPic.pullbackHom f hf hε h h') x =
      h'.classify t ((h.poincare.pullbackAlong x).pullbackCurve f hf hε)
        (FibrewiseAlgEquivZero.pullbackCurve f hf hε hPx) := by
    conv_lhs => rw [hx]
    exact RepresentsRelSubPic.postComp_pullbackHom_classify f hf hε h h' t _ hPx
  rw [hx']
  exact h'.classify_spec t _ _

/-- Postcomposition with the representing pullback map preserves multiplication. -/
theorem postComp_pullbackHom_mul (f : C' ⟶ C) (hf : f ≫ c = c') (hε : ε'.1 ≫ f = ε.1)
    (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D) (h' : RepresentsRelSubPic c' ε'
      (algEquivZeroCut c' ε') D')
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (a b : SchemeHomOver t D.toBase) :
    postComp (RepresentsRelSubPic.pullbackHom f hf hε h h')
        ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) h).mul t a b) =
      (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c' ε') h').mul t
        (postComp (RepresentsRelSubPic.pullbackHom f hf hε h h') a)
        (postComp (RepresentsRelSubPic.pullbackHom f hf hε h h') b) := by
  refine h'.ext_of_iso t _ _ ?_
  obtain ⟨i1⟩ := nonempty_pullbackAlong_postComp_pullbackHom_iso f hf hε h h' t
    ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) h).mul t a b)
  obtain ⟨i2⟩ := nonempty_pullbackAlong_mul_iso (algEquivZeroGroupCut c ε) h t a b
  obtain ⟨i3⟩ := nonempty_tensor_pullbackCurve_iso f hf hε (h.poincare.pullbackAlong a)
    (h.poincare.pullbackAlong b)
  obtain ⟨ia⟩ := nonempty_pullbackAlong_postComp_pullbackHom_iso f hf hε h h' t a
  obtain ⟨ib⟩ := nonempty_pullbackAlong_postComp_pullbackHom_iso f hf hε h h' t b
  obtain ⟨i4⟩ := nonempty_pullbackAlong_mul_iso (algEquivZeroGroupCut c' ε') h' t
    (postComp (RepresentsRelSubPic.pullbackHom f hf hε h h') a) (postComp
      (RepresentsRelSubPic.pullbackHom f hf hε h h') b)
  exact ⟨i1 ≪≫ (Scheme.Modules.pullback _).mapIso i2 ≪≫ i3 ≪≫ (ia.symm ⊗ᵢ ib.symm) ≪≫ i4.symm⟩

end PullbackHomMul

attribute [local simp] PtsIntertwineIso.coe_gen


end RepIsoPII

attribute [local simp] PtsIntertwineIso.coe_gen


open _root_.AlgebraicGeometry.RelPicard.RepresentsRelSubPic in
/-- The map on Picard points induced by a curve isomorphism agrees with Pic0 congruence. -/
theorem _root_.AlgebraicGeometry.RelPicard.pullbackHom_points_eq_pic0_congr_of_iso
    (R : Type u) [CommRing R]
    {C C' : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) (c' : C' ⟶ Spec (CommRingCat.of R))
    [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    [IsProper c'] [SmoothOfRelativeDimension 1 c'] [GeometricallyIntegral c']
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) (ε' : SchemeHomOver (𝟙 (Spec
      (CommRingCat.of R))) c')
    (f : C' ≅ C) (hf : f.hom ≫ c = c') (hε : ε'.1 ≫ f.hom = ε.1)
    (D : RelativePic0Designation R c) (D' : RelativePic0Designation R c')
    (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)
    (h' : RepresentsRelSubPic c' ε' (algEquivZeroCut c' ε') D')
    (aj : SchemeHomOver c D.toBase) (aj' : SchemeHomOver c' D'.toBase)
    (haj : ∀ (K : Type u) [Field K] (t : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of R)) (x :
      SchemeHomOver t c),
        Nonempty ((h.poincare.pullbackAlong
            ⟨x.1 ≫ aj.1, (Category.assoc _ _ _).trans ((congrArg (x.1 ≫ ·) aj.2).trans x.2)⟩).L ≅
          (RelEffCartierDiv.ofPoint c x.1 x.2).lineBundle ⊗
            (RelEffCartierDiv.ofPoint c (t ≫ ε.1)
              ((Category.assoc _ _ _).trans ((congrArg (t ≫ ·) ε.2).trans (Category.comp_id
                t)))).idealModule))
    (haj' : ∀ (K : Type u) [Field K] (t : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of R)) (x :
      SchemeHomOver t c'),
        Nonempty ((h'.poincare.pullbackAlong
            ⟨x.1 ≫ aj'.1, (Category.assoc _ _ _).trans ((congrArg (x.1 ≫ ·) aj'.2).trans x.2)⟩).L ≅
          (RelEffCartierDiv.ofPoint c' x.1 x.2).lineBundle ⊗
            (RelEffCartierDiv.ofPoint c' (t ≫ ε'.1)
              ((Category.assoc _ _ _).trans ((congrArg (t ≫ ·) ε'.2).trans (Category.comp_id
                t)))).idealModule))
    (K : Type u) [Field K] [IsAlgClosed K] (i : R →+* K)
    (F F' : Type v) [Field F] [Field F'] [Algebra K F] [Algebra K F'] [IsCurveOver K F]
      [IsCurveOver K F']
    (eF : F ≃+* F') (heF : ∀ a : K, eF (algebraMap K F a) = algebraMap K F' a)
    (M : CurveModel K F) (M' : CurveModel K F')
    (e : M.C ⟶ pullback c (Spec.map (CommRingCat.ofHom i))) [IsIso e]
    (he : e ≫ pullback.snd c (Spec.map (CommRingCat.ofHom i)) = M.toBase)
    (e' : M'.C ⟶ pullback c' (Spec.map (CommRingCat.ofHom i))) [IsIso e']
    (he' : e' ≫ pullback.snd c' (Spec.map (CommRingCat.ofHom i)) = M'.toBase)
    (hfK : ∀ (y : {q : Spec (CommRingCat.of K) ⟶ M'.C // q ≫ M'.toBase = 𝟙 _})
        (x : {q : Spec (CommRingCat.of K) ⟶ M.C // q ≫ M.toBase = 𝟙 _}),
      x.1 ≫ e ≫ pullback.fst c (Spec.map (CommRingCat.ofHom i)) =
        y.1 ≫ e' ≫ pullback.fst c' (Spec.map (CommRingCat.ofHom i)) ≫ f.hom →
      M'.pointEquivPlace y = AlgebraicCurve.Place.congrRingEquiv eF heF (M.pointEquivPlace x))
    (pts : Pic0 K F ≃ SchemeHomOver (Spec.map (CommRingCat.ofHom i)) D.toBase)
    (hadd : ∀ x y : Pic0 K F,
      pts (x + y) = (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) h).mul
        (Spec.map (CommRingCat.ofHom i)) (pts x) (pts y))
    (hnorm : ∀ (x s : {q : Spec (CommRingCat.of K) ⟶ M.C // q ≫ M.toBase = 𝟙 _}),
      s.1 ≫ e ≫ pullback.fst c (Spec.map (CommRingCat.ofHom i)) =
        Spec.map (CommRingCat.ofHom i) ≫ ε.1 →
      ∃ Dv : Divisor.degZero (K := K) (F := F),
        (Dv : Divisor K F) =
          Finsupp.single (M.pointEquivPlace x) 1 - Finsupp.single (M.pointEquivPlace s) 1 ∧
        (pts (Pic0.mk Dv)).1 =
          x.1 ≫ e ≫ pullback.fst c (Spec.map (CommRingCat.ofHom i)) ≫ aj.1)
    (pts' : Pic0 K F' ≃ SchemeHomOver (Spec.map (CommRingCat.ofHom i)) D'.toBase)
    (hadd' : ∀ x y : Pic0 K F',
      pts' (x + y) = (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c' ε')
        h').mul (Spec.map (CommRingCat.ofHom i)) (pts' x) (pts' y))
    (hnorm' : ∀ (x s : {q : Spec (CommRingCat.of K) ⟶ M'.C // q ≫ M'.toBase = 𝟙 _}),
      s.1 ≫ e' ≫ pullback.fst c' (Spec.map (CommRingCat.ofHom i)) =
        Spec.map (CommRingCat.ofHom i) ≫ ε'.1 →
      ∃ Dv : Divisor.degZero (K := K) (F := F'),
        (Dv : Divisor K F') =
          Finsupp.single (M'.pointEquivPlace x) 1 - Finsupp.single (M'.pointEquivPlace s) 1 ∧
        (pts' (Pic0.mk Dv)).1 =
          x.1 ≫ e' ≫ pullback.fst c' (Spec.map (CommRingCat.ofHom i)) ≫ aj'.1) :
    ∀ z : Pic0 K F,
      (pts' (Pic0.congr eF heF z)).1 = (pts z).1 ≫ (RepresentsRelSubPic.pullbackHom f.hom hf hε h
        h').1 := by
  classical
  let L' := RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c' ε') h'
  let N : SchemeHomOver D.toBase D'.toBase := RepresentsRelSubPic.pullbackHom f.hom hf hε h h'
  have hfinv : f.inv ≫ c' = c := by rw [← hf, Iso.inv_hom_id_assoc]
  have hεinv : ε.1 ≫ f.inv = ε'.1 := by rw [← hε, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have hinve : inv e ≫ M.toBase = pullback.snd c (Spec.map (CommRingCat.ofHom i))
    := by rw [IsIso.inv_comp_eq, he]
  have hinve' : inv e' ≫ M'.toBase = pullback.snd c' (Spec.map (CommRingCat.ofHom i))
    := by rw [IsIso.inv_comp_eq, he']
  let X : {q : Spec (CommRingCat.of K) ⟶ M.C // q ≫ M.toBase = 𝟙 _} → SchemeHomOver (Spec.map
    (CommRingCat.ofHom i)) c := fun x ↦
    ⟨x.1 ≫ e ≫ pullback.fst c (Spec.map (CommRingCat.ofHom i)), by
      rw [Category.assoc, Category.assoc, pullback.condition, reassoc_of% he, reassoc_of% x.2]⟩
  let X' : {q : Spec (CommRingCat.of K) ⟶ M'.C // q ≫ M'.toBase = 𝟙 _} → SchemeHomOver (Spec.map
    (CommRingCat.ofHom i)) c' := fun y ↦
    ⟨y.1 ≫ e' ≫ pullback.fst c' (Spec.map (CommRingCat.ofHom i)), by
      rw [Category.assoc, Category.assoc, pullback.condition, reassoc_of% he', reassoc_of% y.2]⟩
  let under : {q : Spec (CommRingCat.of K) ⟶ M.C // q ≫ M.toBase = 𝟙 _} →
      {q : Spec (CommRingCat.of K) ⟶ M'.C // q ≫ M'.toBase = 𝟙 _} := fun x ↦
    ⟨pullback.lift (x.1 ≫ e ≫ pullback.fst c (Spec.map (CommRingCat.ofHom i)) ≫ f.inv) (x.1 ≫ e ≫
      pullback.snd c (Spec.map (CommRingCat.ofHom i)))
        (by simp only [Category.assoc, hfinv]; rw [pullback.condition]) ≫ inv e', by
      rw [Category.assoc, hinve', pullback.lift_snd, he]; exact x.2⟩
  have hunder : ∀ x, (under x).1 ≫ e' ≫ pullback.fst c' (Spec.map (CommRingCat.ofHom i)) = x.1 ≫ e
    ≫ pullback.fst c (Spec.map (CommRingCat.ofHom i)) ≫ f.inv := by
    intro x; simp only [under, Category.assoc, IsIso.inv_hom_id_assoc, pullback.lift_fst]
  have hunder' : ∀ x, x.1 ≫ e ≫ pullback.fst c (Spec.map (CommRingCat.ofHom i)) = (under x).1 ≫ e'
    ≫ pullback.fst c' (Spec.map (CommRingCat.ofHom i)) ≫ f.hom := by
    intro x; rw [reassoc_of% (hunder x)]; simp only [Iso.inv_hom_id, Category.comp_id]
  let s : {q : Spec (CommRingCat.of K) ⟶ M.C // q ≫ M.toBase = 𝟙 _} :=
    ⟨pullback.lift ((Spec.map (CommRingCat.ofHom i)) ≫ ε.1) (𝟙 _)
      (by rw [Category.assoc, ε.2, Category.comp_id, Category.id_comp]) ≫ inv e, by
      rw [Category.assoc, hinve, pullback.lift_snd]⟩
  have hs : s.1 ≫ e ≫ pullback.fst c (Spec.map (CommRingCat.ofHom i)) = (Spec.map
    (CommRingCat.ofHom i)) ≫ ε.1 := by
    simp only [s, Category.assoc, IsIso.inv_hom_id_assoc, pullback.lift_fst]
  have hs' : (under s).1 ≫ e' ≫ pullback.fst c' (Spec.map (CommRingCat.ofHom i)) = (Spec.map
    (CommRingCat.ofHom i)) ≫ ε'.1 := by
    rw [hunder, reassoc_of% hs, hεinv]
  let Φ : Pic0 K F → Pic0 K F' := fun z ↦ pts'.symm (NeronModelInfra.schemeHomOverComp (pts z) N)
  have hΦ : ∀ z, pts' (Φ z) = NeronModelInfra.schemeHomOverComp (pts z) N := fun z ↦
    pts'.apply_symm_apply _
  have hNhom : ∀ x y : SchemeHomOver (Spec.map (CommRingCat.ofHom i)) D.toBase,
      NeronModelInfra.schemeHomOverComp ((RepresentsRelSubPic.relativeGroupLaw (P :=
        algEquivZeroGroupCut c ε) h).mul _ x y) N =
        L'.mul _ (NeronModelInfra.schemeHomOverComp x N) (NeronModelInfra.schemeHomOverComp y N) :=
    fun x y ↦ RepIsoPII.postComp_pullbackHom_mul f.hom hf hε h h' (Spec.map (CommRingCat.ofHom i))
      x y
  have hΦadd : ∀ z w, Φ (z + w) = Φ z + Φ w := by
    intro z w; apply pts'.injective
    rw [hadd', hΦ, hΦ, hΦ, hadd, hNhom]
  let Φh : Pic0 K F →+ Pic0 K F' := AddMonoidHom.mk' Φ hΦadd
  suffices hfun : (Pic0.congr eF heF).toAddMonoidHom = Φh by
    intro z
    have h1 : Pic0.congr eF heF z = Φ z := DFunLike.congr_fun hfun z
    rw [h1]; change (pts' (Φ z)).1 = _; rw [hΦ]; rfl
  have hdeg : ∀ v : Place K F, v.deg = 1 := fun v ↦
    AlgebraicCurve.IsCurveOver.deg_eq_one_of_isAlgClosed v
  refine addMonoidHom_ext_of_gen hdeg (M.pointEquivPlace s) fun P ↦ ?_
  obtain ⟨x, hPx⟩ := M.pointEquivPlace.surjective P
  subst hPx
  obtain ⟨Dv, hDv, hptsDv⟩ := hnorm x s hs
  obtain ⟨Dv', hDv', hptsDv'⟩ := hnorm' (under x) (under s) hs'
  obtain ⟨Dv₀, hDv₀, hptsDv₀⟩ := hnorm' (under s) (under s) hs'
  have hgen : gen hdeg (M.pointEquivPlace s) (M.pointEquivPlace x) = Dv := Subtype.ext
    (by rw [coe_gen, hDv])
  have hcongr : Pic0.congr eF heF (Pic0.mk (gen hdeg (M.pointEquivPlace s) (M.pointEquivPlace x)))
    = Pic0.mk Dv' := by
    change Pic0.mk (Pic0.degZeroCongr eF heF _) = _
    congr 1
    apply Subtype.ext
    rw [Pic0.coe_degZeroCongr, coe_gen, map_sub, Divisor.congr_single, Divisor.congr_single,
      ← hfK (under x) x (hunder' x), ← hfK (under s) s (hunder' s), hDv']
  have : IsSeparated c := inferInstance
  have : IsSeparated c' := inferInstance
  let a : SchemeHomOver (Spec.map (CommRingCat.ofHom i)) D.toBase :=
    ⟨(X x).1 ≫ aj.1, (Category.assoc _ _ _).trans ((congrArg ((X x).1 ≫ ·) aj.2).trans (X x).2)⟩
  let b : SchemeHomOver (Spec.map (CommRingCat.ofHom i)) D'.toBase :=
    ⟨(X' (under s)).1 ≫ aj'.1, (Category.assoc _ _ _).trans ((congrArg ((X' (under s)).1 ≫ ·)
      aj'.2).trans (X' (under s)).2)⟩
  let g : SchemeHomOver (Spec.map (CommRingCat.ofHom i)) D'.toBase :=
    ⟨(X' (under x)).1 ≫ aj'.1, (Category.assoc _ _ _).trans ((congrArg ((X' (under x)).1 ≫ ·)
      aj'.2).trans (X' (under x)).2)⟩
  have hmul : L'.mul (Spec.map (CommRingCat.ofHom i)) (NeronModelInfra.schemeHomOverComp a N) b = g
    :=
    mul_comp_eq_of_classifies_rigidify_pullback_of_ofPoint_of_isIso
      h h' f.hom hf N
      (fun t' a' ↦ nonempty_poincare_pullbackAlong_schemeHomOverComp_pullbackHom_iso_rigidify
        f.hom hf hε h h' t' a')
      (Spec.map (CommRingCat.ofHom i)) (X x) (X' (under x)) (X' (under s))
      (by
        change ((under x).1 ≫ e' ≫ pullback.fst c' (Spec.map (CommRingCat.ofHom i))) ≫ f.hom = x.1
          ≫ e ≫ pullback.fst c (Spec.map (CommRingCat.ofHom i))
        simp only [Category.assoc]; exact (hunder' x).symm)
      (by
        change ((under s).1 ≫ e' ≫ pullback.fst c' (Spec.map (CommRingCat.ofHom i))) ≫ f.hom =
          (Spec.map (CommRingCat.ofHom i)) ≫ ε.1
        simp only [Category.assoc]; rw [← hunder' s, hs])
      a (haj K (Spec.map (CommRingCat.ofHom i)) (X x)) b g (haj' K (Spec.map (CommRingCat.ofHom i))
        (X' (under s))) (haj' K (Spec.map (CommRingCat.ofHom i)) (X' (under x)))
  have hb0 : b = pts' 0 := by
    have h0 : Pic0.mk Dv₀ = 0 := by
      rw [show Dv₀ = 0 from Subtype.ext (by rw [hDv₀, sub_self]; rfl), Pic0.mk_zero]
    apply Subtype.ext
    rw [← h0, hptsDv₀]
    change ((under s).1 ≫ e' ≫ pullback.fst c' (Spec.map (CommRingCat.ofHom i))) ≫ aj'.1 = _
    simp only [Category.assoc]
  have hkey : NeronModelInfra.schemeHomOverComp a N = g := by
    rw [← hmul, hb0, ← pts'.apply_symm_apply (NeronModelInfra.schemeHomOverComp a N), ← hadd',
      add_zero]
  change Pic0.congr eF heF (Pic0.mk _) = Φ _
  apply pts'.injective
  rw [hΦ, hcongr]
  apply Subtype.ext
  rw [hptsDv', NeronModelInfra.schemeHomOverComp_coe, hgen, hptsDv]
  have hkey1 := congrArg Subtype.val hkey
  simp only [NeronModelInfra.schemeHomOverComp_coe, a, g, X, X', Category.assoc] at hkey1
  simp only [Category.assoc]
  exact hkey1.symm
end JacobianVarieties.Picard.Proofs.PicardPointsTransport
end ProofImplementation

attribute [-instance]
  AlgebraicGeometry.SmoothOfRelativeDimension.fiberToSpecResidueField
  AlgebraicGeometry.SmoothOfRelativeDimension.pullback_snd
  AlgebraicGeometry.SmoothOfRelativeDimension.pullback_fst
  AlgebraicGeometry.SmoothOfRelativeDimension.smooth_one
  AlgebraicGeometry.SmoothProperCurve.isIntegral_pullback_Spec_field
  AlgebraicGeometry.IsProper.fiberToSpecResidueField
  PresheafOfModules.ExteriorPower.instModulePresheafAb
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
  AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_snd
  AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_fst
  NeronModelInfra.schemeHomOverComp_id_left
  NeronModelInfra.schemeHomOverComp_id_right
  NeronModelInfra.schemeHomOverId_coe
  NeronModelInfra.schemeHomOverComp_coe
  AlgebraicGeometry.Scheme.Modules.normModuleFunctor_obj
  AlgebraicGeometry.Scheme.Modules.exteriorPower_obj
  PresheafOfModules.exteriorPower_map_ιMulti
  PresheafOfModules.ExteriorPower.appₗ_apply
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
