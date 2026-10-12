/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_kerPoints_baseChange_surjective_and_fibre.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.Algebra.DualNumber
import Mathlib.Algebra.TrivSqZeroExt.Basic
import Mathlib.Algebra.Algebra.Hom
import Mathlib.Algebra.Algebra.Tower
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.AlgebraicGeometry.Spec
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.LinearAlgebra.Quotient.Defs
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Ideal.Span
import Mathlib.Algebra.Module.Submodule.Pointwise
import Mathlib.Algebra.Module.NatInt
import Mathlib.Tactic.Abel
import Nyll.AlgebraicCurves.Geometry.Picard.Functor
import Nyll.JacobianVarieties.Picard.Representation
import Nyll.AlgebraicCurves.Geometry.Picard.AlgEquivZeroCut
import Nyll.AlgebraicCurves.Geometry.Picard.AlgEquivZeroGroupCut
import Nyll.AlgebraicCurves.Geometry.Picard.RelSubPic.Group
import Nyll.AlgebraicCurves.Geometry.Picard.RelSubPic.Presheaf
import Nyll.SchemeTheory.Cohomology.Cech.TwoChartCech
import Nyll.SchemeTheory.Cohomology.Cech.TwoAffineOpenCover
import Nyll.AlgebraicCurves.Geometry.Picard.RelativeGroupLaw
import Nyll.AlgebraicCurves.Geometry.AbelianSchemes.GroupLaw.Kernel
import Nyll.AlgebraicCurves.Geometry.Schemes.SchemeHomOver
import Nyll.AlgebraicCurves.Foundations.CommutativeAlgebra.RationalLocalization
import Nyll.AlgebraicCurves.Geometry.Deformation.RigKerDualNumber
import Nyll.AlgebraicCurves.Geometry.Picard.StageHom
import Nyll.JacobianVarieties.Picard.PicDualNumberDeformationClassSpec
import Nyll.AlgebraicCurves.Geometry.Schemes.TwoAffineOpenCoverH1BaseChange
import Nyll.JacobianVarieties.Picard.RepresentsRelSubPic_kerPointsToRigKer_bijective
import Nyll.JacobianVarieties.Picard.RepresentsRelSubPic_kerPointsToRigKer_mul
import Nyll.JacobianVarieties.Picard.RepresentsRelSubPic_kerPoints_mul_mem_and_comp_mem
import Nyll.JacobianVarieties.Picard.exists_isDeformationClassMap
import Nyll.JacobianVarieties.Picard.IsDeformationClassMap_injective
import Nyll.JacobianVarieties.Picard.IsDeformationClassMap_map_mul
import Nyll.JacobianVarieties.Picard.IsDeformationClassMap_natural
import Nyll.JacobianVarieties.Picard.IsDeformationClassMap_surjective
import Nyll.AlgebraicCurves.Geometry.Schemes.Scheme_TwoAffineOpenCover_H1baseChangeMap_surjective_and_eq_iff_of_surjective

import Nyll.JacobianVarieties.Picard.RepresentsRelSubPicPresheaf
import Nyll.JacobianVarieties.Picard.RepresentsRelSubPicGroup
import Nyll.JacobianVarieties.Picard.RepresentsRelSubPicKerPoints

/-!
Base change on infinitesimal Picard points is surjective, with fibres given by multiples.
-/

section ProofImplementation

namespace JacobianVarieties.Picard.Proofs.KernelBaseChange
attribute [-instance]
  AlgebraicGeometry.SmoothOfRelativeDimension.fiberToSpecResidueField
  AlgebraicGeometry.SmoothOfRelativeDimension.pullback_snd
  AlgebraicGeometry.SmoothOfRelativeDimension.pullback_fst
  AlgebraicGeometry.SmoothOfRelativeDimension.smooth_one
  AlgebraicGeometry.SmoothProperCurve.isIntegral_pullback_Spec_field
  AlgebraicGeometry.IsProper.fiberToSpecResidueField
  SheafOfModules.isIso_ihomModelToIhom
attribute [-simp]
  AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_hom_app_coe
  AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_inv_app_coe
  AlgebraicGeometry.RelPicard.BaseChange.restrict_P
  AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_snd
  AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_fst
  PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom
  SheafOfModules.ihomSectionsEquivFamily_unit
  AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply
  SheafOfModules.ihomEval_unit_app
  AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right
  AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left
  AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply
  SheafOfModules.unit_ihomSectionsEquivFamily
  AlgebraicGeometry.Scheme.Modules.familyOfHom_app
  AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply
  AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply
  AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply
  AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply
  AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg
  AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero
  AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub
  AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add
  AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app

universe u

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry
open _root_.AlgebraicGeometry.RelPicard
open _root_.NeronModelInfra
open _root_.GoodReductionJacobian
open _root_.AlgebraicGeometry.Scheme.TwoAffineOpenCover

noncomputable section

namespace AlgebraicGeometry

export _root_.AlgebraicGeometry (
  Spec.map_comp
  Surjective
  SmoothOfRelativeDimension
  IsProper
  GeometricallyIntegral
  Spec
  Spec.map
  Scheme
  Smooth
  Scheme.TwoAffineOpenCover
  Scheme.TwoAffineOpenCover.specMap
  RelPicard.LFP.stageHom)

namespace RelPicard

export _root_.AlgebraicGeometry.RelPicard (
  RepresentsRelSubPic
  algEquivZeroCut
  algEquivZeroGroupCut
  RepresentsRelSubPic.relativeGroupLaw
  dualNumberReduction
  dualNumberReduction_comp_specMap
  RigKerDualNumber.Carrier
  RigKerDualNumber
  RepresentsRelSubPic.kerPointsToRigKer
  LFP.stageHom
  H1StructureSheaf
  IsDeformationClassMap
  RepresentsRelSubPic.kerPoints_mul_mem_and_comp_mem
  exists_isDeformationClassMap
  IsDeformationClassMap.natural)

namespace KerBC

open _root_.AlgebraicGeometry.RelPicard
open _root_.AlgebraicGeometry

variable {R : Type u} [CommRing R] {X : Scheme.{u}} {c : X ⟶ Spec (.of R)}
  {ε : SchemeHomOver (𝟙 (Spec (.of R))) c} {D : RelativePic0Designation R c}

section Sigma
variable (R)
variable (A : Type u) [CommRing A] [Algebra R A]

/-- The homomorphism on dual numbers induced by the base algebra. -/
abbrev liftHom : DualNumber R →ₐ[R] DualNumber A :=
  DualNumber.lift ⟨(Algebra.ofId R (DualNumber A), DualNumber.eps), DualNumber.eps_mul_eps, fun _
    => Commute.all _ _⟩

/-- The morphism on dual number spectra induced by base change. -/
abbrev sigmaOver : SchemeHomOver (specMap R (DualNumber A)) (specMap R (DualNumber R)) :=
  LFP.stageHom R (liftHom R A)

theorem fstHom_comp_liftHom :
    (TrivSqZeroExt.fstHom R A A).comp (liftHom R A) = (Algebra.ofId R A).comp (TrivSqZeroExt.fstHom
      R R R) := by
  refine DualNumber.algHom_ext ?_
  simp only [AlgHom.comp_apply, DualNumber.lift_apply_eps, TrivSqZeroExt.fstHom_apply,
    DualNumber.fst_eps, map_zero]

theorem dualNumberReduction_comp_sigma :
    dualNumberReduction R A ≫ (sigmaOver R A).1 = specMap R A ≫ dualNumberReduction R R := by
  have h := congrArg AlgHom.toRingHom (fstHom_comp_liftHom R A)
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
  exact congrArg (fun f => Spec.map (CommRingCat.ofHom f)) h

theorem specMap_comp_specMap_self : specMap R A ≫ specMap R R = specMap R A := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]

theorem stageHom_toAlgHom_comp_ofId_eq :
    LFP.stageHom R (DualNumber.lift ⟨((IsScalarTower.toAlgHom R A (DualNumber A)).comp
      (Algebra.ofId R A),
        DualNumber.eps), DualNumber.eps_mul_eps, fun _ => Commute.all _ _⟩) = sigmaOver R A := by
  have ha : (IsScalarTower.toAlgHom R A (DualNumber A)).comp (Algebra.ofId R A) = Algebra.ofId R
    (DualNumber A) :=
    Subsingleton.elim _ _
  suffices ∀ (f : R →ₐ[R] DualNumber A) (p) (p'), f = Algebra.ofId R (DualNumber A) →
      LFP.stageHom R (DualNumber.lift ⟨(f, DualNumber.eps), p⟩) =
        LFP.stageHom R (DualNumber.lift ⟨(Algebra.ofId R (DualNumber A), DualNumber.eps), p'⟩) from
          this _ _ _ ha
  rintro f p p' rfl
  rfl

end Sigma

section K
variable (hD : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)

/-- Infinitesimal points reducing to the identity of the relative Picard group. -/
abbrev K (A : Type u) [CommRing A] [Algebra R A] : Type u :=
  { x : SchemeHomOver (specMap R (DualNumber A)) D.toBase //
      dualNumberReduction R A ≫ x.1 = ((RepresentsRelSubPic.relativeGroupLaw (P :=
        algEquivZeroGroupCut c ε) hD).one (specMap R A)).1 }

variable (A : Type u) [CommRing A] [Algebra R A]

theorem one_memK :
    dualNumberReduction R A ≫ ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c
      ε) hD).one (specMap R (DualNumber A))).1 = ((RepresentsRelSubPic.relativeGroupLaw (P :=
      algEquivZeroGroupCut c ε) hD).one (specMap R A)).1 :=
  congrArg Subtype.val ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε)
    hD).one_natural _ _ (dualNumberReduction R A) (dualNumberReduction_comp_specMap R A))

theorem mul_memK (x y : K hD A) :
    dualNumberReduction R A ≫ ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c
      ε) hD).mul (specMap R (DualNumber A)) x.1 y.1).1 = ((RepresentsRelSubPic.relativeGroupLaw (P
      := algEquivZeroGroupCut c ε) hD).one (specMap R A)).1 :=
  (RepresentsRelSubPic.kerPoints_mul_mem_and_comp_mem hD A).1 x.1 y.1 x.2 y.2

/-- The identity infinitesimal point. -/
def oneK : K hD A := ⟨(RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) hD).one
  _, one_memK hD A⟩

/-- Multiplication of infinitesimal points. -/
def mulK (x y : K hD A) :
    K hD A := ⟨(RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) hD).mul _ x.1
      y.1, mul_memK hD A x y⟩

/-- Natural multiples of infinitesimal points. -/
def nsmulK (n : ℕ) (x : K hD A) : K hD A := Nat.rec (oneK hD A) (fun _ ih => mulK hD A ih x) n

theorem nsmulK_zero (x : K hD A) : nsmulK hD A 0 x = oneK hD A := rfl
theorem nsmulK_succ (n : ℕ) (x : K hD A) :
    nsmulK hD A (n + 1) x = mulK hD A (nsmulK hD A n x) x := rfl

theorem nsmulK_val (n : ℕ) (x : K hD A) :
    (nsmulK hD A n x).1 = (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε)
      hD).nsmul _ n x.1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [nsmulK_succ, RelativeGroupLaw.nsmul_succ, ← ih]
      rfl

variable {A}
variable {𝒱 : X.TwoAffineOpenCover} {δ : RigKerDualNumber c ε A → H1StructureSheaf c A 𝒱}
  (hδ : IsDeformationClassMap c ε A 𝒱 δ)

/-- The deformation class of an infinitesimal Picard point. -/
abbrev Δ (x : K hD A) : H1StructureSheaf c A 𝒱 := δ (hD.kerPointsToRigKer A x)

include hδ in
theorem Δ_bijective : Function.Bijective (Δ hD (δ := δ)) :=
  Function.Bijective.comp ⟨hδ.injective, hδ.surjective⟩ (hD.kerPointsToRigKer_bijective A)

include hδ in
theorem Δ_mul (x y : K hD A) (h) :
    Δ hD (δ := δ) ⟨(RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) hD).mul _
      x.1 y.1, h⟩ = Δ hD (δ := δ) x + Δ hD (δ := δ) y := by
  unfold Δ
  rw [hD.kerPointsToRigKer_mul A x y h]
  exact hδ.map_mul _ _

include hδ in
theorem Δ_mulK (x y : K hD A) : Δ hD (δ := δ) (mulK hD A x y) = Δ hD (δ := δ) x + Δ hD (δ := δ) y :=
  Δ_mul hD hδ x y (mul_memK hD A x y)

include hδ in
theorem Δ_oneK : Δ hD (δ := δ) (oneK hD A) = 0 := by
  have h1 : mulK hD A (oneK hD A) (oneK hD A) = oneK hD A := Subtype.ext
    ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) hD).one_mul _ _)
  have h2 := Δ_mulK hD hδ (oneK hD A) (oneK hD A)
  rw [h1] at h2
  have h3 := congrArg (fun m => m - Δ hD (δ := δ) (oneK hD A)) h2
  simp only [sub_self, add_sub_cancel_right] at h3
  exact h3.symm

include hδ in
theorem Δ_nsmulK (n : ℕ) (x : K hD A) : Δ hD (δ := δ) (nsmulK hD A n x) = n • Δ hD (δ := δ) x := by
  induction n with
  | zero => rw [zero_smul, nsmulK_zero]; exact Δ_oneK hD hδ
  | succ n ih => rw [nsmulK_succ, Δ_mulK hD hδ, ih, succ_nsmul]

theorem kerPointsToRigKer_eq_mk (x : K hD A) :
    ∃ M : RigKerDualNumber.Carrier c ε A,
      hD.kerPointsToRigKer A x = Quotient.mk _ M ∧ M.1 = hD.poincare.pullbackAlong x.1 := by
  unfold RepresentsRelSubPic.kerPointsToRigKer
  exact ⟨_, rfl, rfl⟩

end K

section Restrict
variable (hD : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D) (A : Type u) [CommRing A] [Algebra
  R A]

theorem sigma_mem (x : SchemeHomOver (specMap R (DualNumber R)) D.toBase)
    (hx : dualNumberReduction R R ≫ x.1 = ((RepresentsRelSubPic.relativeGroupLaw (P :=
      algEquivZeroGroupCut c ε) hD).one (specMap R R)).1) :
    dualNumberReduction R A ≫ ((sigmaOver R A).1 ≫ x.1) = ((RepresentsRelSubPic.relativeGroupLaw (P
      := algEquivZeroGroupCut c ε) hD).one (specMap R A)).1 := by
  rw [← Category.assoc, dualNumberReduction_comp_sigma, Category.assoc, hx]
  exact congrArg Subtype.val ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε)
    hD).one_natural _ _ (specMap R A) (specMap_comp_specMap_self R A))

/-- Base change of infinitesimal Picard points. -/
def sigmaK (x : K hD R) : K hD A :=
  ⟨GoodReductionJacobian.schemeHomOverComp (sigmaOver R A).1 (sigmaOver R A).2 x.1, sigma_mem hD A
    x.1 x.2⟩

@[scoped simp] theorem sigmaK_val_val (x : K hD R) :
    (sigmaK hD A x).1.1 = (sigmaOver R A).1 ≫ x.1.1 := rfl

variable {A}
variable {𝒱 : X.TwoAffineOpenCover}
  {δR : RigKerDualNumber c ε R → H1StructureSheaf c R 𝒱} (hδR : IsDeformationClassMap c ε R 𝒱 δR)
  {δA : RigKerDualNumber c ε A → H1StructureSheaf c A 𝒱} (hδA : IsDeformationClassMap c ε A 𝒱 δA)

include hδR hδA in
theorem Δ_sigmaK (x : K hD R) :
    Δ hD (δ := δA) (sigmaK hD A x) = 𝒱.H1stageMap c (Algebra.ofId R A) (Δ hD (δ := δR) x) := by
  obtain ⟨M, hM, hM1⟩ := kerPointsToRigKer_eq_mk hD x
  obtain ⟨N, hN, hN1⟩ := kerPointsToRigKer_eq_mk hD (sigmaK hD A x)
  unfold Δ
  rw [hM, hN]
  refine IsDeformationClassMap.natural hδR hδA (Algebra.ofId R A) M N ?_
  rw [hM1, hN1, stageHom_toAlgHom_comp_ofId_eq]
  exact ⟨hD.poincare.pullbackAlongPullbackAlongIso x.1 (sigmaOver R A)⟩

end Restrict

end AlgebraicGeometry.RelPicard.KerBC

open AlgebraicGeometry.RelPicard.KerBC in
attribute [local simp] sigmaK_val_val

end

open AlgebraicGeometry.RelPicard.KerBC in
attribute [local simp] sigmaK_val_val
end JacobianVarieties.Picard.Proofs.KernelBaseChange

namespace AlgebraicGeometry.RelPicard.RepresentsRelSubPic

open _root_.JacobianVarieties.Picard.Proofs.KernelBaseChange
universe u
open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry
open _root_.AlgebraicGeometry.RelPicard
open _root_.NeronModelInfra
open _root_.GoodReductionJacobian
open _root_.AlgebraicGeometry.Scheme.TwoAffineOpenCover
open _root_.JacobianVarieties.Picard.Proofs
open KernelBaseChange.AlgebraicGeometry.RelPicard.KerBC in
attribute [local simp] sigmaK_val_val

open _root_.JacobianVarieties.Picard.Proofs
open KernelBaseChange.AlgebraicGeometry.RelPicard.KerBC in
/-- Base change on infinitesimal Picard points is surjective, with fibres given by multiples. -/
theorem kerPoints_baseChange_surjective_and_fibre
    {R : Type u} [CommRing R]
    {X : Scheme.{u}} (c : X ⟶ Spec (CommRingCat.of R)) [IsProper c]
    [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (D : RelativePic0Designation R c)
    (hD : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)
    (𝒱 : X.TwoAffineOpenCover)
    (A : Type u) [CommRing A] [Algebra R A] (hA : Function.Surjective (algebraMap R A))
    (q : ℕ) (hq : RingHom.ker (algebraMap R A) = Ideal.span {(q : R)}) :
    let L : RelativeGroupLaw R D.toBase := RepresentsRelSubPic.relativeGroupLaw (P :=
      algEquivZeroGroupCut c ε) hD
    let tR : Spec (CommRingCat.of (DualNumber R)) ⟶ Spec (CommRingCat.of R) :=
      Scheme.TwoAffineOpenCover.specMap R (DualNumber R)
    let tA : Spec (CommRingCat.of (DualNumber A)) ⟶ Spec (CommRingCat.of R) :=
      Scheme.TwoAffineOpenCover.specMap R (DualNumber A)
    let σ : Spec (CommRingCat.of (DualNumber A)) ⟶ Spec (CommRingCat.of (DualNumber R)) :=
      (RelPicard.LFP.stageHom R (DualNumber.lift ⟨(Algebra.ofId R (DualNumber A), DualNumber.eps),
      DualNumber.eps_mul_eps, fun _ => Commute.all _ _⟩)).1
    (∀ x : SchemeHomOver tR D.toBase,
        dualNumberReduction R R ≫ x.1 = (L.one (Scheme.TwoAffineOpenCover.specMap R R)).1 →
          dualNumberReduction R A ≫ (σ ≫ x.1) = (L.one (Scheme.TwoAffineOpenCover.specMap R A)).1) ∧
    (∀ x y : SchemeHomOver tR D.toBase,
        σ ≫ (L.mul tR x y).1 =
          (L.mul tA ⟨σ ≫ x.1, by
                rw [Category.assoc, x.2]
                exact (RelPicard.LFP.stageHom R (DualNumber.lift ⟨(Algebra.ofId R (DualNumber A),
                  DualNumber.eps), DualNumber.eps_mul_eps, fun _ => Commute.all _ _⟩)).2⟩
            ⟨σ ≫ y.1, by
                rw [Category.assoc, y.2]
                exact (RelPicard.LFP.stageHom R (DualNumber.lift ⟨(Algebra.ofId R (DualNumber A),
                  DualNumber.eps), DualNumber.eps_mul_eps, fun _ => Commute.all _ _⟩)).2⟩).1) ∧
    (∀ (φ : SchemeHomOver D.toBase D.toBase) (x : SchemeHomOver tR D.toBase), σ ≫ (x.1 ≫ φ.1) = (σ
      ≫ x.1) ≫ φ.1) ∧
    (∀ y : SchemeHomOver tA D.toBase,
        dualNumberReduction R A ≫ y.1 = (L.one (Scheme.TwoAffineOpenCover.specMap R A)).1 →
          ∃ x : SchemeHomOver tR D.toBase,
            dualNumberReduction R R ≫ x.1 = (L.one (Scheme.TwoAffineOpenCover.specMap R R)).1 ∧ σ ≫
              x.1 = y.1) ∧
    (∀ x x' : SchemeHomOver tR D.toBase,
        dualNumberReduction R R ≫ x.1 = (L.one (Scheme.TwoAffineOpenCover.specMap R R)).1 →
        dualNumberReduction R R ≫ x'.1 = (L.one (Scheme.TwoAffineOpenCover.specMap R R)).1 →
          (σ ≫ x.1 = σ ≫ x'.1 ↔
            ∃ z : SchemeHomOver tR D.toBase,
              dualNumberReduction R R ≫ z.1 = (L.one (Scheme.TwoAffineOpenCover.specMap R R)).1 ∧
                x' = L.mul tR x (L.nsmul tR q z))) := by
  intro L tR tA σ
  obtain ⟨δR, hδR⟩ := exists_isDeformationClassMap c ε R 𝒱
  obtain ⟨δA, hδA⟩ := exists_isDeformationClassMap c ε A 𝒱
  have hΔR := Δ_bijective hD hδR
  have hΔA := Δ_bijective hD hδA
  have hbcA := H1baseChangeMap_surjective_and_eq_iff_of_surjective 𝒱 c A hA
  have hbcR := H1baseChangeMap_surjective_and_eq_iff_of_surjective 𝒱 c R (fun r => ⟨r, rfl⟩)
  have hq0 : algebraMap R A q = 0 := by
    rw [← RingHom.mem_ker, hq]; exact Ideal.mem_span_singleton_self _
  have hstage_q : ∀ m : H1StructureSheaf c R 𝒱,
      𝒱.H1stageMap c (Algebra.ofId R A) ((q : R) • m) = 0 := fun m => by
    have h' : (Algebra.ofId R A).toRingHom (q : R) = 0 := hq0
    rw [LinearMap.map_smulₛₗ, h', zero_smul]
  refine ⟨fun x hx => sigma_mem hD A x hx, fun x y => ?_, fun φ x => (Category.assoc _ _ _).symm,
    fun y hy => ?_,
    fun x x' hx hx' => ?_⟩
  · exact congrArg Subtype.val
      ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) hD).mul_natural tR tA
        σ (sigmaOver R A).2 x y)
  · obtain ⟨u, hu⟩ := hbcA.1 (Δ hD (δ := δA) ⟨y, hy⟩)
    obtain ⟨xK, hxK⟩ := hΔR.2 (𝒱.H1baseChangeMap c R u)
    refine ⟨xK.1, xK.2, ?_⟩
    have key : Δ hD (δ := δA) (sigmaK hD A xK) = Δ hD (δ := δA) ⟨y, hy⟩ := by
      rw [Δ_sigmaK hD hδR hδA, hxK, H1stageMap_H1baseChangeMap, hu]
    exact congrArg (fun z : K hD A => z.1.1) (hΔA.1 key)
  · constructor
    · intro hσ
      have hK : sigmaK hD A ⟨x, hx⟩ = sigmaK hD A ⟨x', hx'⟩ := Subtype.ext (Subtype.ext hσ)
      obtain ⟨u, hu⟩ := hbcR.1 (Δ hD (δ := δR) ⟨x, hx⟩)
      obtain ⟨u', hu'⟩ := hbcR.1 (Δ hD (δ := δR) ⟨x', hx'⟩)
      have h1 : 𝒱.H1baseChangeMap c A u = 𝒱.H1baseChangeMap c A u' := by
        rw [← H1stageMap_H1baseChangeMap 𝒱 c (Algebra.ofId R A) u, ← H1stageMap_H1baseChangeMap 𝒱 c
          (Algebra.ofId R A) u',
          hu, hu', ← Δ_sigmaK hD hδR hδA, ← Δ_sigmaK hD hδR hδA, hK]
      have h2 : u - u' ∈ RingHom.ker (algebraMap R A) • (⊤ : Submodule R _) := (hbcA.2 u u').mp h1
      rw [hq, Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists] at h2
      obtain ⟨v, -, hv⟩ := h2
      obtain ⟨zK, hzK⟩ := hΔR.2 (𝒱.H1baseChangeMap c R (-v))
      refine ⟨zK.1, zK.2, ?_⟩
      have huu : u' = u + (q : R) • (-v) := by
        rw [smul_neg, hv]; abel
      have key : Δ hD (δ := δR) ⟨x', hx'⟩ =
          Δ hD (δ := δR) (mulK hD R ⟨x, hx⟩ (nsmulK hD R q zK)) := by
        rw [Δ_mulK hD hδR, Δ_nsmulK hD hδR, hzK, ← hu, ← hu', huu, map_add, LinearMap.map_smulₛₗ]
        congr 1
        exact Nat.cast_smul_eq_nsmul R q _
      have h3 := congrArg (fun z : K hD R => z.1) (hΔR.1 key)
      simp only at h3
      rw [h3]
      change (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) hD).mul _ x
        (nsmulK hD R q zK).1 = _
      rw [nsmulK_val]
    · rintro ⟨z, hz, rfl⟩
      have key : Δ hD (δ := δA) (sigmaK hD A (mulK hD R ⟨x, hx⟩ (nsmulK hD R q ⟨z, hz⟩))) =
          Δ hD (δ := δA) (sigmaK hD A ⟨x, hx⟩) := by
        rw [Δ_sigmaK hD hδR hδA, Δ_sigmaK hD hδR hδA, Δ_mulK hD hδR, Δ_nsmulK hD hδR, map_add,
          ← Nat.cast_smul_eq_nsmul R, hstage_q, add_zero]
      have h := congrArg (fun z : K hD A => z.1.1) (hΔA.1 key)
      simp only [sigmaK_val_val] at h
      rw [← h]
      change σ ≫ ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) hD).mul _ x
        (nsmulK hD R q ⟨z, hz⟩).1).1 = _
      rw [nsmulK_val]
end AlgebraicGeometry.RelPicard.RepresentsRelSubPic
end ProofImplementation

attribute [-simp]
  AlgebraicGeometry.Scheme.TwoAffineOpenCover.HomOver.mk.sizeOf_spec
  AlgebraicGeometry.Scheme.TwoAffineOpenCover.HomOver.mk.injEq
  AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right
  AlgebraicGeometry.Scheme.Modules.map_unitSection
  AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply
  AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero
  AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left
  AlgebraicGeometry.Scheme.Modules.tensorPow_zero
  AlgebraicGeometry.Scheme.Modules.tensorPow_succ
  AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_hom_app_coe
  AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_inv_app_coe
  AlgebraicGeometry.RelPicard.BaseChange.restrict_P
  AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_snd
  AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_fst
  PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom
  SheafOfModules.ihomSectionsEquivFamily_unit
  AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply
  SheafOfModules.ihomEval_unit_app
  AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right
  AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left
  AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply
  SheafOfModules.unit_ihomSectionsEquivFamily
  AlgebraicGeometry.Scheme.Modules.familyOfHom_app
  AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply
  AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply
  AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply
  AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply
  AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg
  AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero
  AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub
  AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add
  AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app
