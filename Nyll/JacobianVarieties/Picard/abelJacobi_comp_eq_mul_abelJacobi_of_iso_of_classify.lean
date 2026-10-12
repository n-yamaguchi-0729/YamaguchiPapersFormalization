/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_RelPicard_abelJacobi_comp_eq_mul_abelJacobi_of_iso_of_classify.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.Tactic.Choose
import Nyll.AlgebraicCurves.Geometry.Picard.Functor
import Nyll.JacobianVarieties.Picard.Representation
import Nyll.AlgebraicCurves.Geometry.Picard.AlgEquivZeroCut
import Nyll.AlgebraicCurves.Geometry.Picard.AlgEquivZeroGroupCut
import Nyll.AlgebraicCurves.Geometry.Picard.RelSubPic.Group
import Nyll.AlgebraicCurves.Geometry.Picard.RelativeGroupLaw
import Nyll.SchemeTheory.Modules.Monoidal
import Nyll.SchemeTheory.Modules.PullbackMonoidal
import Nyll.AlgebraicCurves.Geometry.Picard.Pullback
import Nyll.AlgebraicCurves.Geometry.Sheaves.IdealSheafModule
import Nyll.AlgebraicCurves.RelativeDivisors.RelEffCartierDiv
import Nyll.AlgebraicCurves.RelativeDivisors.RelEffCartierDivOfPoint
import Nyll.AlgebraicCurves.RelativeDivisors.Cartier
import Nyll.AlgebraicCurves.Geometry.Curves.SmoothProperCurveBase
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_IsInvertible_tensor
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_IsInvertible_exists_tensor_inverse
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_IsInvertible_dual
import Nyll.JacobianVarieties.Picard.RepresentsRelSubPic_nonempty_poincare_pullbackAlong_mul_iso
import Nyll.AlgebraicCurves.Geometry.Schemes.Scheme_Hom_nonempty_pullback_ker_pow_invModule_iso_of_isIso
import Nyll.AlgebraicCurves.RelativeDivisors.RelEffCartierDiv_isInvertible_I
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_IdealSheafData_IsInvertible_isInvertible_module

import Nyll.JacobianVarieties.Picard.RepresentsRelSubPicPullback
import Nyll.JacobianVarieties.Picard.RepresentsRelSubPicGroup

/-!
# Abel–Jacobi morphisms under a curve isomorphism

Classified transport along a curve isomorphism compares the two Abel–Jacobi morphisms.
-/

section ProofImplementation

namespace JacobianVarieties.Picard.Proofs.AbelJacobiIsoComparison

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory
open _root_.AlgebraicGeometry
open _root_.NeronModelInfra
open _root_.GoodReductionJacobian
open _root_.AlgebraicGeometry.RelPicard

universe u

noncomputable section

namespace Sub2c

section Monoidal

variable {𝒞 : Type*} [Category 𝒞] [MonoidalCategory 𝒞] [SymmetricCategory 𝒞]

/-- Tensor inverses of isomorphic objects are isomorphic via the given inverse evaluations. -/
def inverseIso {X X' Q Q' : 𝒞} (eX : X ≅ X') (hQ : X ⊗ Q ≅ 𝟙_ 𝒞) (hQ' : X' ⊗ Q' ≅ 𝟙_ 𝒞) : Q ≅ Q' :=
  (ρ_ Q).symm ≪≫ whiskerLeftIso Q hQ'.symm ≪≫ (α_ Q X' Q').symm ≪≫
    whiskerRightIso ((β_ Q X') ≪≫ whiskerRightIso eX.symm Q ≪≫ hQ) Q' ≪≫ λ_ Q'

/-- Transport the given tensor-inverse evaluation along an isomorphism of its first factor. -/
def inverseOfIso {X Y Q : 𝒞} (eX : X ≅ Y) (hQ : X ⊗ Q ≅ 𝟙_ 𝒞) : Y ⊗ Q ≅ 𝟙_ 𝒞 :=
  whiskerRightIso eX.symm Q ≪≫ hQ

end Monoidal

section Modules

variable {R : Type u} [CommRing R] {C : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of R)}

theorem rigSection_snd {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) :
    rigSection c t ε ≫ pullback.snd c t = 𝟙 T := by
  simp only [rigSection, pullback.lift_snd]

/-- Pulling a base module to the curve and then back along the section recovers that module. -/
def sectionPullbackIso {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) (Q : T.Modules) :
    (Scheme.Modules.pullback (rigSection c t ε)).obj ((Scheme.Modules.pullback (pullback.snd c
      t)).obj Q) ≅ Q :=
  (Scheme.Modules.pullbackComp _ _).app Q ≪≫
    (Scheme.Modules.pullbackCongr (rigSection_snd t ε)).app Q ≪≫
    (Scheme.Modules.pullbackId _).app Q

end Modules

theorem nonempty_iso_unit_of_field {k : Type u} [Field k] (Q : (Spec (CommRingCat.of k)).Modules)
    (hQ : Scheme.Modules.IsInvertible Q) : Nonempty (Q ≅ 𝟙_ (Spec (CommRingCat.of k)).Modules) := by
  obtain ⟨U, hx, ⟨eU⟩⟩ := hQ.1 default
  have hU : U = ⊤ := by
    ext y
    simp only [TopologicalSpace.Opens.coe_top, Set.mem_univ, iff_true]
    rw [Subsingleton.elim y default]
    exact hx
  subst hU
  let X := Spec (CommRingCat.of k)
  let i : (⊤ : X.Opens).toScheme ≅ X := X.topIso
  have hi : i.inv ≫ (⊤ : X.Opens).ι = 𝟙 X := by
    rw [← Scheme.topIso_hom]; exact i.inv_hom_id
  exact ⟨((Scheme.Modules.pullbackId _).app Q).symm ≪≫
    (Scheme.Modules.pullbackCongr hi.symm).app Q ≪≫
    ((Scheme.Modules.pullbackComp _ _).app Q).symm ≪≫
    (Scheme.Modules.pullback i.inv).mapIso eU ≪≫
    Scheme.Modules.pullbackUnitIso i.inv⟩

section Twist

variable {R : Type u} [CommRing R] {C : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of R)}
  (ε₁ ε₂ : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)

/-- A chosen tensor inverse of the line bundle restricted to the second rigidifying section. -/
noncomputable def qinv {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    (M : RigidifiedLineBundle c ε₁ t) : T.Modules :=
  (M.isInvertible.pullback (rigSection c t ε₂)).exists_tensor_inverse.choose

theorem qinv_isInvertible {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    (M : RigidifiedLineBundle c ε₁ t) :
    Scheme.Modules.IsInvertible (qinv ε₁ ε₂ M) :=
  (M.isInvertible.pullback (rigSection c t ε₂)).exists_tensor_inverse.choose_spec.1

/-- The chosen inverse evaluates the restriction at the second section to the unit module. -/
noncomputable def qinvIso {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    (M : RigidifiedLineBundle c ε₁ t) :
    (Scheme.Modules.pullback (rigSection c t ε₂)).obj M.L ⊗ qinv ε₁ ε₂ M ≅ 𝟙_ _ :=
  (M.isInvertible.pullback (rigSection c t ε₂)).exists_tensor_inverse.choose_spec.2.some

/-- Change the rigidifying section using the inverse of the restricted line bundle. -/
noncomputable def twist {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    (M : RigidifiedLineBundle c ε₁ t) :
    RigidifiedLineBundle c ε₂ t where
  L := M.L ⊗ (Scheme.Modules.pullback (pullback.snd c t)).obj (qinv ε₁ ε₂ M)
  isInvertible := M.isInvertible.tensor ((qinv_isInvertible ε₁ ε₂ M).pullback _)
  rigidified := ⟨Scheme.Modules.pullbackTensorObjIso _ _ _ ≪≫
    whiskerLeftIso _ (sectionPullbackIso t ε₂ _) ≪≫ qinvIso ε₁ ε₂ M⟩

theorem twist_L {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} (M : RigidifiedLineBundle c ε₁ t)
    :
    (twist ε₁ ε₂ M).L = M.L ⊗ (Scheme.Modules.pullback (pullback.snd c t)).obj (qinv ε₁ ε₂ M) := rfl

theorem twist_cut {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (M : RigidifiedLineBundle c ε₁ t)
    (hM : FibrewiseAlgEquivZero M) : FibrewiseAlgEquivZero (twist ε₁ ε₂ M) := by
  intro k _ _ s
  let φ := pullback.fst (pullback.snd c t) s
  have hφ : φ ≫ pullback.snd c t = fibreAt c t s ≫ s := pullback.condition
  obtain ⟨e0⟩ := nonempty_iso_unit_of_field _ ((qinv_isInvertible ε₁ ε₂ M).pullback s)
  have e1 : (Scheme.Modules.pullback φ).obj ((Scheme.Modules.pullback (pullback.snd c t)).obj (qinv
    ε₁ ε₂ M)) ≅ 𝟙_ _ :=
    (Scheme.Modules.pullbackComp _ _).app _ ≪≫
      (Scheme.Modules.pullbackCongr hφ).app _ ≪≫
      ((Scheme.Modules.pullbackComp _ _).app _).symm ≪≫
      (Scheme.Modules.pullback (fibreAt c t s)).mapIso e0 ≪≫
      Scheme.Modules.pullbackTensorUnitObjIso _
  have e2 : (Scheme.Modules.pullback φ).obj (twist ε₁ ε₂ M).L ≅ (Scheme.Modules.pullback φ).obj M.L
    :=
    Scheme.Modules.pullbackTensorObjIso _ _ _ ≪≫ whiskerLeftIso _ e1 ≪≫ ρ_ _
  exact (hM k s).of_iso e2.symm

end Twist

section Rep

variable {R : Type u} [CommRing R] {C : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of R)}
  (ε₁ ε₂ : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
  {D₁ D₂ : RelativePic0Designation R c}
  (h₁ : RepresentsRelSubPic c ε₁ (algEquivZeroCut c ε₁) D₁)
  (h₂ : RepresentsRelSubPic c ε₂ (algEquivZeroCut c ε₂) D₂)

theorem classify_congr {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c} {P : SubPicCondition c ε}
    {D : RelativePic0Designation R c}
    (h : RepresentsRelSubPic c ε P D) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (M M' : RigidifiedLineBundle c ε t) (hM : P.P t M) (hM' : P.P t M') (i : Nonempty (M.L ≅ M'.L))
      :
    h.classify t M hM = h.classify t M' hM' :=
  h.classify_unique t M' hM' _ ⟨(h.classify_spec t M hM).some ≪≫ i.some⟩

end Rep

end Sub2c

namespace I2

section Transform

variable {R : Type u} [CommRing R] {C C' : Scheme.{u}}
  {c : C ⟶ Spec (CommRingCat.of R)} {c' : C' ⟶ Spec (CommRingCat.of R)}
  (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) (ε' : SchemeHomOver (𝟙 (Spec (CommRingCat.of
    R))) c')
  (f : C' ⟶ C) (g : C ⟶ C') (hf : f ≫ c = c') (hg : g ≫ c' = c) (hgf : g ≫ f = 𝟙 C)

/-- Transport the section along the specified inverse curve morphism. -/
def epsT : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c' :=
  ⟨ε.1 ≫ g, by rw [Category.assoc, hg]; exact ε.2⟩

include hgf in
theorem epsT_comp : (epsT ε g hg).1 ≫ f = ε.1 := by
  change (ε.1 ≫ g) ≫ f = ε.1
  rw [Category.assoc, hgf, Category.comp_id]

/-- Pull back the line bundle and adjust its rigidifying section. -/
def Phi {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (M : RigidifiedLineBundle c ε t) :
    RigidifiedLineBundle c' ε' t :=
  Sub2c.twist (epsT ε g hg) ε' (M.pullbackCurve f hf (epsT_comp ε f g hg hgf))

theorem Phi_L {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (M : RigidifiedLineBundle c ε t) :
    (Phi ε ε' f g hf hg hgf t M).L =
      (Scheme.Modules.pullback (curveChange f hf t)).obj M.L ⊗
        (Scheme.Modules.pullback (pullback.snd c' t)).obj
          (Sub2c.qinv (epsT ε g hg) ε' (M.pullbackCurve f hf (epsT_comp ε f g hg hgf))) := rfl

theorem Phi_cut {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (M : RigidifiedLineBundle c ε t)
    (hM : FibrewiseAlgEquivZero M) : FibrewiseAlgEquivZero (Phi ε ε' f g hf hg hgf t M) :=
  Sub2c.twist_cut _ _ t _ (FibrewiseAlgEquivZero.pullbackCurve f hf (epsT_comp ε f g hg hgf) hM)

include hgf in
theorem curveChange_comp_eq_id {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) :
    curveChange (c := c') (c' := c) g hg t ≫ curveChange (c := c) (c' := c') f hf t = 𝟙 _ := by
  apply pullback.hom_ext
  · simp only [curveChange, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc,
      Category.id_comp, hgf,
      Category.comp_id]
  · simp only [curveChange, Category.assoc, pullback.lift_snd, Category.id_comp, Category.comp_id]

end Transform

end I2

namespace AJT

theorem poincare_mul {R : Type u} [CommRing R] {C : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of R)}
    {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c}
    {P : SubPicGroupCondition c ε} {D : RelativePic0Designation R c}
    (h : RepresentsRelSubPic c ε P.toSubPicCondition D)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t D.toBase) :
    Nonempty ((h.poincare.pullbackAlong (h.relativeGroupLaw.mul t x y)).L ≅
      (h.poincare.pullbackAlong x).L ⊗ (h.poincare.pullbackAlong y).L) :=
  h.nonempty_poincare_pullbackAlong_mul_iso (T := Over.mk t)
    (schemeHomOverToOverHom x) (schemeHomOverToOverHom y)

section Transport

variable {R : Type u} [CommRing R] {C C' : Scheme.{u}}
  {c : C ⟶ Spec (CommRingCat.of R)} {c' : C' ⟶ Spec (CommRingCat.of R)}
  (e : C ≅ C') (he : e.hom ≫ c' = c) (he' : e.inv ≫ c = c')

include he in
theorem isIso_curveChange {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) :
    IsIso (curveChange (c := c) (c' := c') e.inv he' t) :=
  ⟨curveChange (c := c') (c' := c) e.hom he t,
    I2.curveChange_comp_eq_id e.hom e.inv he he' e.inv_hom_id t,
    I2.curveChange_comp_eq_id e.inv e.hom he' he e.hom_inv_id t⟩

theorem graphOver_comp_curveChange {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    (a : T ⟶ C) (ha : a ≫ c = t) (a' : T ⟶ C') (ha' : a' ≫ c' = t) (haa' : a' = a ≫ e.hom) :
    graphOver c' a' ha' ≫ curveChange (c := c) (c' := c') e.inv he' t = graphOver c a ha := by
  subst haa'
  apply pullback.hom_ext
  · simp only [graphOver, curveChange, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc,
      Iso.hom_inv_id, Category.comp_id]
  · simp only [graphOver, curveChange, Category.assoc, pullback.lift_snd, Category.comp_id]

include he in
theorem transport_ofPoint [IsSeparated c] [SmoothOfRelativeDimension 1 c]
    [IsSeparated c'] [SmoothOfRelativeDimension 1 c']
    {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    (a : T ⟶ C) (ha : a ≫ c = t) (a' : T ⟶ C') (ha' : a' ≫ c' = t) (haa' : a' = a ≫ e.hom) :
    Nonempty ((Scheme.Modules.pullback (curveChange (c := c) (c' := c') e.inv he' t)).obj
        (RelEffCartierDiv.ofPoint c a ha).lineBundle ≅ (RelEffCartierDiv.ofPoint c' a'
          ha').lineBundle) ∧
    Nonempty ((Scheme.Modules.pullback (curveChange (c := c) (c' := c') e.inv he' t)).obj
        (RelEffCartierDiv.ofPoint c a ha).idealModule ≅ (RelEffCartierDiv.ofPoint c' a'
          ha').idealModule) := by
  have := isIso_curveChange e he he' t
  have hI : (graphOver c a ha).ker.IsInvertible := (RelEffCartierDiv.ofPoint c a ha).isInvertible_I
  have hI' : (graphOver c' a' ha').ker.IsInvertible := (RelEffCartierDiv.ofPoint c' a'
    ha').isInvertible_I
  obtain ⟨⟨i1⟩, ⟨i2⟩⟩ := Scheme.Hom.nonempty_pullback_ker_pow_invModule_iso_of_isIso
    (curveChange (c := c) (c' := c') e.inv he' t) (graphOver c a ha) (graphOver c' a' ha')
    (graphOver_comp_curveChange e he' a ha a' ha' haa') hI hI' 1
  have h1 : (graphOver c a ha).ker ^ 1 = (graphOver c a ha).ker := pow_one _
  have h1' : (graphOver c' a' ha').ker ^ 1 = (graphOver c' a' ha').ker := pow_one _
  refine ⟨⟨?_⟩, ⟨?_⟩⟩
  · exact (Scheme.Modules.pullback _).mapIso (eqToIso (congrArg Scheme.IdealSheafData.invModule
      h1.symm)) ≪≫
      i1 ≪≫ eqToIso (congrArg Scheme.IdealSheafData.invModule h1')
  · exact (Scheme.Modules.pullback _).mapIso (eqToIso (congrArg Scheme.IdealSheafData.module
      h1.symm)) ≪≫
      i2 ≪≫ eqToIso (congrArg Scheme.IdealSheafData.module h1')

end Transport

theorem Phi_L_iso_of_field {R : Type u} [CommRing R] {C C' : Scheme.{u}}
    {c : C ⟶ Spec (CommRingCat.of R)} {c' : C' ⟶ Spec (CommRingCat.of R)}
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) (ε' : SchemeHomOver (𝟙 (Spec
      (CommRingCat.of R))) c')
    (f : C' ⟶ C) (g : C ⟶ C') (hf : f ≫ c = c') (hg : g ≫ c' = c) (hgf : g ≫ f = 𝟙 C)
    {K : Type u} [Field K] (t : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of R)) (M :
      RigidifiedLineBundle c ε t) :
    Nonempty ((I2.Phi ε ε' f g hf hg hgf t M).L ≅ (Scheme.Modules.pullback (curveChange f hf
      t)).obj M.L) := by
  obtain ⟨e0⟩ := Sub2c.nonempty_iso_unit_of_field _
    (Sub2c.qinv_isInvertible (I2.epsT ε g hg) ε' (M.pullbackCurve f hf (I2.epsT_comp ε f g hg hgf)))
  exact ⟨whiskerLeftIso _ ((Scheme.Modules.pullback _).mapIso e0 ≪≫
    Scheme.Modules.pullbackTensorUnitObjIso _) ≪≫
    ρ_ _⟩

end AJT

end
end JacobianVarieties.Picard.Proofs.AbelJacobiIsoComparison

namespace AlgebraicGeometry.RelPicard

open _root_.JacobianVarieties.Picard.Proofs.AbelJacobiIsoComparison
open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory
open _root_.AlgebraicGeometry
open _root_.NeronModelInfra
open _root_.GoodReductionJacobian
open _root_.AlgebraicGeometry.RelPicard
universe u

/-- Classified transport along a curve isomorphism compares the two Abel–Jacobi morphisms. -/
theorem abelJacobi_comp_eq_mul_abelJacobi_of_iso_of_classify
    {R : Type u} [CommRing R] {C C' : Scheme.{u}}
    {c : C ⟶ Spec (CommRingCat.of R)} {c' : C' ⟶ Spec (CommRingCat.of R)}
    [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    [IsProper c'] [SmoothOfRelativeDimension 1 c'] [GeometricallyIntegral c']
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) (ε' : SchemeHomOver (𝟙 (Spec
      (CommRingCat.of R))) c')
    (e : C ≅ C') (he : e.hom ≫ c' = c) (he' : e.inv ≫ c = c')
    {D : RelativePic0Designation R c} {D' : RelativePic0Designation R c'}
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
    (θ : SchemeHomOver D.toBase D'.toBase)
    (hθ : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
        (M : RigidifiedLineBundle c ε t) (hM : FibrewiseAlgEquivZero M)
        (N : RigidifiedLineBundle c' ε' t) (hN : FibrewiseAlgEquivZero N)
        (Q : T.Modules), Scheme.Modules.IsInvertible Q →
        Nonempty (N.L ≅ (Scheme.Modules.pullback (curveChange (c := c) (c' := c') e.inv he' t)).obj
          M.L ⊗
          (Scheme.Modules.pullback (pullback.snd c' t)).obj Q) →
        postComp θ (h.classify t M hM) = h'.classify t N hN)
    (K : Type u) [Field K] (t : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of R)) (x :
      SchemeHomOver t c) :
    (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c' ε') h').mul t
        ⟨x.1 ≫ aj.1 ≫ θ.1, by rw [Category.assoc, Category.assoc, θ.2, aj.2, x.2]⟩
        ⟨t ≫ ε.1 ≫ e.hom ≫ aj'.1, by
          rw [Category.assoc, Category.assoc, Category.assoc, aj'.2, he, ε.2, Category.comp_id]⟩ =
      ⟨(x.1 ≫ e.hom) ≫ aj'.1, by rw [Category.assoc, Category.assoc, aj'.2, he, x.2]⟩ := by
  let a : SchemeHomOver t D.toBase :=
    ⟨x.1 ≫ aj.1, (Category.assoc _ _ _).trans ((congrArg (x.1 ≫ ·) aj.2).trans x.2)⟩
  have hAa : (⟨x.1 ≫ aj.1 ≫ θ.1, by rw [Category.assoc, Category.assoc, θ.2, aj.2, x.2]⟩ :
      SchemeHomOver t D'.toBase) = postComp θ a := Subtype.ext (Category.assoc _ _ _).symm
  have pε : (t ≫ ε.1) ≫ c = t := (Category.assoc _ _ _).trans ((congrArg (t ≫ ·) ε.2).trans
    (Category.comp_id t))
  have peε : (t ≫ ε.1 ≫ e.hom) ≫ c' = t := by
    rw [Category.assoc, Category.assoc, he, ε.2, Category.comp_id]
  have pex : (x.1 ≫ e.hom) ≫ c' = t := by rw [Category.assoc, he, x.2]
  let xB : SchemeHomOver t c' := ⟨t ≫ ε.1 ≫ e.hom, peε⟩
  let xg : SchemeHomOver t c' := ⟨x.1 ≫ e.hom, pex⟩
  have hB : (⟨t ≫ ε.1 ≫ e.hom ≫ aj'.1, by
          rw [Category.assoc, Category.assoc, Category.assoc, aj'.2, he, ε.2, Category.comp_id]⟩ :
      SchemeHomOver t D'.toBase) =
      ⟨xB.1 ≫ aj'.1, (Category.assoc _ _ _).trans ((congrArg (xB.1 ≫ ·) aj'.2).trans xB.2)⟩ :=
    Subtype.ext (by simp only [xB, Category.assoc])
  rw [hAa, hB]
  let M : RigidifiedLineBundle c ε t := h.poincare.pullbackAlong a
  have hM : FibrewiseAlgEquivZero M := (algEquivZeroCut c ε).pullback_mem _ _ a _ h.poincare_mem
  have ha : a = h.classify t M hM := h.classify_unique _ M hM a ⟨Iso.refl _⟩
  have hθa : postComp θ a = h'.classify t (I2.Phi ε ε' e.inv e.hom he' he e.hom_inv_id t M)
      (I2.Phi_cut ε ε' e.inv e.hom he' he e.hom_inv_id t M hM) := by
    conv_lhs => rw [ha]
    exact hθ t M hM _ _ _ (Sub2c.qinv_isInvertible _ ε' _) ⟨Iso.refl _⟩
  obtain ⟨e1⟩ : Nonempty ((h'.poincare.pullbackAlong (postComp θ a)).L ≅
      (I2.Phi ε ε' e.inv e.hom he' he e.hom_inv_id t M).L) := by
    rw [hθa]
    exact h'.classify_spec _ _ _
  obtain ⟨e2⟩ := AJT.Phi_L_iso_of_field ε ε' e.inv e.hom he' he e.hom_inv_id t M
  obtain ⟨iM⟩ := haj K t x
  obtain ⟨iB⟩ := haj' K t xB
  obtain ⟨ig⟩ := haj' K t xg
  obtain ⟨⟨T1⟩, -⟩ := AJT.transport_ofPoint e he he' x.1 x.2 (x.1 ≫ e.hom) pex rfl
  obtain ⟨-, ⟨T2⟩⟩ := AJT.transport_ofPoint e he he' (t ≫ ε.1) pε (t ≫ ε.1 ≫ e.hom) peε
    (Category.assoc _ _ _).symm
  obtain ⟨dd⟩ := ((RelEffCartierDiv.ofPoint c' (t ≫ ε.1 ≫ e.hom)
    peε).isInvertible_I).isInvertible_module.dual.2
  have key : (I2.Phi ε ε' e.inv e.hom he' he e.hom_inv_id t M).L ⊗
      (h'.poincare.pullbackAlong
        ⟨xB.1 ≫ aj'.1, (Category.assoc _ _ _).trans ((congrArg (xB.1 ≫ ·) aj'.2).trans xB.2)⟩).L ≅
      (h'.poincare.pullbackAlong
        ⟨xg.1 ≫ aj'.1, (Category.assoc _ _ _).trans ((congrArg (xg.1 ≫ ·) aj'.2).trans xg.2)⟩).L :=
    ((e2 ≪≫ (Scheme.Modules.pullback _).mapIso iM ≪≫ Scheme.Modules.pullbackTensorObjIso _ _ _ ≪≫
        (T1 ⊗ᵢ T2)) ⊗ᵢ iB) ≪≫
      α_ _ _ _ ≪≫ whiskerLeftIso _ ((α_ _ _ _).symm ≪≫ (dd ⊗ᵢ Iso.refl _) ≪≫ λ_ _) ≪≫ ig.symm
  obtain ⟨emul⟩ := AJT.poincare_mul (P := algEquivZeroGroupCut c' ε') h' t (postComp θ a)
    ⟨xB.1 ≫ aj'.1, (Category.assoc _ _ _).trans ((congrArg (xB.1 ≫ ·) aj'.2).trans xB.2)⟩
  exact h'.ext_of_iso t _ _ ⟨emul ≪≫ (e1 ⊗ᵢ Iso.refl _) ≪≫ key⟩
end AlgebraicGeometry.RelPicard
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
