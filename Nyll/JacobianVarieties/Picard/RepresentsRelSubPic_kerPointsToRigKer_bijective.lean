/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_kerPointsToRigKer_bijective.lean
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
import Nyll.SchemeTheory.Cohomology.Cech.TwoChartCech
import Nyll.SchemeTheory.Cohomology.Cech.TwoAffineOpenCover
import Nyll.AlgebraicCurves.Geometry.Picard.RelativeGroupLaw
import Nyll.AlgebraicCurves.Geometry.AbelianSchemes.GroupLaw.Kernel
import Nyll.AlgebraicCurves.Geometry.Schemes.SchemeHomOver
import Nyll.AlgebraicCurves.Foundations.CommutativeAlgebra.RationalLocalization
import Nyll.AlgebraicCurves.Geometry.Deformation.RigKerDualNumber

import Nyll.JacobianVarieties.Picard.RepresentsRelSubPicGroup
import Nyll.JacobianVarieties.Picard.RepresentsRelSubPicKerPoints
/-!
# Classification of rigidified line bundles trivial on the reduction

Kernel points of the representing Picard scheme correspond bijectively to rigidified
line bundles whose pullback to the dual-number reduction is trivial.
-/

section ProofImplementation

namespace JacobianVarieties.Picard.Proofs.KernelPointClassification

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard
open NeronModelInfra GoodReductionJacobian

private theorem fibrewiseAlgEquivZero_of_pullbackAlong_iso_unit_aux
    {R : Type u} [CommRing R] {C : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of R)}
    {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c}
    {T T₀ : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} {t₀ : T₀ ⟶ Spec (CommRingCat.of R)}
    (ψ : SchemeHomOver t₀ t)
    (hψ : ∀ (k : Type u) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ T),
      ∃ s₀ : Spec (CommRingCat.of k) ⟶ T₀, s₀ ≫ ψ.1 = s)
    (M : RigidifiedLineBundle c ε t)
    (hM : Nonempty ((M.pullbackAlong ψ).L ≅ (RigidifiedLineBundle.unit (c := c) (ε := ε) t₀).L)) :
    FibrewiseAlgEquivZero M := by
  intro k _ _ s
  obtain ⟨s₀, hs₀⟩ := hψ k s
  subst hs₀
  let P := Limits.pullback (pullback.snd c t) (s₀ ≫ ψ.1)
  have hcomm : (pullback.fst (pullback.snd c t) (s₀ ≫ ψ.1) ≫ pullback.fst c t) ≫ c =
      (pullback.snd (pullback.snd c t) (s₀ ≫ ψ.1) ≫ s₀) ≫ t₀ := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, pullback.condition, Category.assoc,
      Category.assoc, ψ.2, Category.assoc]
  let a : P ⟶ Limits.pullback c t₀ :=
    pullback.lift (pullback.fst _ _ ≫ pullback.fst c t) (pullback.snd _ _ ≫ s₀) hcomm
  let e' : P ⟶ Limits.pullback (pullback.snd c t₀) s₀ :=
    pullback.lift a (pullback.snd _ _) (by simp only [a, pullback.lift_snd])
  have he' : e' ≫ fibreAt c t₀ s₀ = fibreAt c t (s₀ ≫ ψ.1) := by
    simp only [e', fibreAt, pullback.lift_snd]
  have hfst' : e' ≫ pullback.fst (pullback.snd c t₀) s₀ ≫ baseChangeSnd c ψ =
      pullback.fst (pullback.snd c t) (s₀ ≫ ψ.1) := by
    apply pullback.hom_ext
    · simp only [e', a, baseChangeSnd, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc,
        Category.comp_id]
    · simp only [e', a, baseChangeSnd, Category.assoc, pullback.lift_snd, pullback.lift_fst_assoc,
        pullback.lift_snd_assoc]
      rw [pullback.condition]
  have h₀ : IsAlgEquivZero (fibreAt c t₀ s₀)
      ((Scheme.Modules.pullback (pullback.fst (pullback.snd c t₀) s₀)).obj (M.pullbackAlong ψ).L) :=
    (fibrewiseAlgEquivZero_unit (c := c) (ε := ε) t₀ k s₀).of_iso
      ((Scheme.Modules.pullback _).mapIso hM.some.symm)
  refine IsAlgEquivZero.of_iso ?_ (h₀.pullback e' he')
  exact (Scheme.Modules.pullbackComp _ _).app _ ≪≫
    (Scheme.Modules.pullbackComp _ _).app M.L ≪≫
    (Scheme.Modules.pullbackCongr (by simpa only [Category.assoc] using hfst')).app M.L

private theorem ker_restrict_iff_and_exists_unique_and_mul_aux
    {R : Type u} [CommRing R] {C : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of R)}
    {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c}
    {D : RelativePic0Designation R c} (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)
    {T T₀ : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (t₀ : T₀ ⟶ Spec (CommRingCat.of R))
    (ψ : SchemeHomOver t₀ t)
    (hψ : ∀ (k : Type u) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ T),
      ∃ s₀ : Spec (CommRingCat.of k) ⟶ T₀, s₀ ≫ ψ.1 = s) :
    let L := RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) h
    (∀ x : SchemeHomOver t D.toBase,
      GoodReductionJacobian.schemeHomOverComp ψ.1 ψ.2 x = L.one t₀ ↔
        Nonempty (((h.poincare.pullbackAlong x).pullbackAlong ψ).L ≅
          (RigidifiedLineBundle.unit (c := c) (ε := ε) t₀).L)) ∧
    (∀ M : RigidifiedLineBundle c ε t,
      Nonempty ((M.pullbackAlong ψ).L ≅ (RigidifiedLineBundle.unit (c := c) (ε := ε) t₀).L) →
        ∃! x : SchemeHomOver t D.toBase, Nonempty ((h.poincare.pullbackAlong x).L ≅ M.L)) ∧
    (∀ x y : SchemeHomOver t D.toBase,
      Nonempty ((h.poincare.pullbackAlong (L.mul t x y)).L ≅
        ((h.poincare.pullbackAlong x).tensor (h.poincare.pullbackAlong y)).L)) := by
  intro L
  let := RepresentsRelSubPic.grpObj (P := algEquivZeroGroupCut c ε) h
  refine ⟨fun x => ?_, fun M hM => ?_, fun x y => ?_⟩
  · let := (algEquivZeroGroupCut c ε).commGroupObj (Opposite.op (Over.mk t₀))
    have h1 := congrArg Subtype.val
      (RepresentsRelSubPic.homEquiv_one (P := algEquivZeroGroupCut c ε) h (Over.mk t₀))
    have one_iso : Nonempty ((h.poincare.pullbackAlong
        (L.one t₀)).L ≅
          (RigidifiedLineBundle.unit (c := c) (ε := ε) t₀).L) :=
      Quotient.exact h1
    have comp_iso : ((h.poincare.pullbackAlong x).pullbackAlong ψ).L ≅
        (h.poincare.pullbackAlong (GoodReductionJacobian.schemeHomOverComp ψ.1 ψ.2 x)).L :=
      h.poincare.pullbackAlongPullbackAlongIso x ψ
    constructor
    · intro hx
      rw [← hx] at one_iso
      exact ⟨comp_iso ≪≫ one_iso.some⟩
    · rintro ⟨e⟩
      exact h.ext_of_iso t₀ _ _ ⟨comp_iso.symm ≪≫ e ≪≫ one_iso.some.symm⟩
  · exact h.univ t M (fibrewiseAlgEquivZero_of_pullbackAlong_iso_unit_aux ψ hψ M hM)
  · let := (algEquivZeroGroupCut c ε).commGroupObj (Opposite.op (Over.mk t))
    have hm := congrArg Subtype.val
      (RepresentsRelSubPic.homEquiv_mul (P := algEquivZeroGroupCut c ε) h (Over.mk t)
        (schemeHomOverToOverHom x) (schemeHomOverToOverHom y))
    exact Quotient.exact hm

theorem _root_.AlgebraicGeometry.RelPicard.RepresentsRelSubPic.kerPointsToRigKer_bijective
    {R : Type u} [CommRing R] {C : Scheme.{u}} {c : C ⟶ Spec (.of R)}
    {ε : SchemeHomOver (𝟙 (Spec (.of R))) c} {D : RelativePic0Designation R c}
    (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D) (A : Type u) [CommRing A] [Algebra R A] :
    Function.Bijective (h.kerPointsToRigKer A) := by
  obtain ⟨hi, hii, -⟩ := ker_restrict_iff_and_exists_unique_and_mul_aux h
    (Scheme.TwoAffineOpenCover.specMap R (DualNumber A)) (Scheme.TwoAffineOpenCover.specMap R A)
    (dualNumberReductionOver R A) (dualNumberReduction_catches_geometric_points R A)
  constructor
  · rintro ⟨x, hx⟩ ⟨y, hy⟩ hxy
    have e : Nonempty ((h.poincare.pullbackAlong x).L ≅ (h.poincare.pullbackAlong y).L) :=
      Quotient.exact hxy
    exact Subtype.ext (h.ext_of_iso _ x y e)
  · intro q
    induction q using Quotient.ind with
    | _ M =>
      obtain ⟨x, hxM, -⟩ := hii M.1 M.2
      refine ⟨⟨x, ?_⟩, ?_⟩
      · have e : Nonempty (((h.poincare.pullbackAlong x).pullbackAlong
            (dualNumberReductionOver R A)).L ≅
            (RigidifiedLineBundle.unit (c := c) (ε := ε)
              (Scheme.TwoAffineOpenCover.specMap R A)).L) :=
          ⟨(RigidifiedLineBundle.pullbackAlong_congr (dualNumberReductionOver R A) hxM).some ≪≫
            M.2.some⟩
        exact congrArg Subtype.val ((hi x).mpr e)
      · exact Quotient.sound hxM
end JacobianVarieties.Picard.Proofs.KernelPointClassification
end ProofImplementation
