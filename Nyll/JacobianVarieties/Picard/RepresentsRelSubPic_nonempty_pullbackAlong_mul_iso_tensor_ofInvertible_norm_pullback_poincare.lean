/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_nonempty_pullbackAlong_mul_iso_tensor_ofInvertible_norm_pullback_poincare.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.CategoryTheory.Iso
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.CategoryTheory.Monoidal.Braided.Basic
import Mathlib.CategoryTheory.MorphismProperty.Limits
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
import Mathlib.CategoryTheory.Comma.Over.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_IsInvertible_nonempty_pullback_rigidify_iso
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_IsInvertible_nonempty_rigidify_pullback_tensor_iso
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_IsInvertible_rigidify
import Nyll.SchemeTheory.Modules.PullbackMonoidal
import Nyll.JacobianVarieties.Picard.RepresentsRelSubPic_flat_mul_fst_snd
import Nyll.AlgebraicCurves.Geometry.Picard.Functor
import Nyll.JacobianVarieties.Picard.Representation
import Nyll.AlgebraicCurves.Geometry.Picard.AlgEquivZeroCut
import Nyll.AlgebraicCurves.Geometry.Picard.AlgEquivZeroGroupCut
import Nyll.AlgebraicCurves.Geometry.Picard.Pullback
import Nyll.AlgebraicCurves.Geometry.Sheaves.ModulesRigidify
import Nyll.AlgebraicCurves.Geometry.Schemes.RigidifiedLineBundleOfInvertible
import Nyll.AlgebraicCurves.Geometry.Sheaves.ModulesNormModule
import Nyll.AlgebraicCurves.Geometry.Curves.SmoothProperCurveBase
import Nyll.JacobianVarieties.Pic0.RelativePic0DesignationBaseChange
import Nyll.AlgebraicCurves.Geometry.AbelianSchemes.GroupLaw.BaseChange
import Nyll.AlgebraicCurves.Geometry.Schemes.SchemeHomOver

import Nyll.JacobianVarieties.Picard.RepresentsRelSubPicPullback

/-!
# Multiplication and the rigidified norm of the Poincare bundle

The supplied norm comparisons commute with base change and tensor products.
After rigidification, these comparisons give the tensor law for pullback along
multiplication on the represented relative Picard group.
-/

section ProofImplementation

namespace JacobianVarieties.Picard.Proofs.NormTensorMultiplication


open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory
open _root_.AlgebraicGeometry
open _root_.NeronModelInfra
open _root_.GoodReductionJacobian
open _root_.AlgebraicGeometry.RelPicard
open _root_.AlgebraicGeometry.SmoothProperCurve



open _root_.AlgebraicGeometry.Scheme.Modules


namespace ModularCurve
namespace PrimBody


open _root_.AlgebraicGeometry.Scheme.Modules


variable {R : Type} [CommRing R] {C C' : Scheme.{0}}
  {c : C ⟶ Spec (CommRingCat.of R)} {c' : C' ⟶ Spec (CommRingCat.of R)}

theorem isFinite_curveChange' (π : C' ⟶ C) (hπ : π ≫ c = c') [IsFinite π] {T : Scheme.{0}}
    (t : T ⟶ Spec (CommRingCat.of R)) :
    IsFinite (curveChange π hπ t) :=
  MorphismProperty.pullbackMap (P := @IsFinite) ‹IsFinite π› (inferInstance : IsFinite (𝟙 T))
    hπ.symm
    (Category.id_comp t).symm

theorem surjective_curveChange' (π : C' ⟶ C) (hπ : π ≫ c = c') [Surjective π] {T : Scheme.{0}}
    (t : T ⟶ Spec (CommRingCat.of R)) :
    Surjective (curveChange π hπ t) := by
  have : MorphismProperty.IsStableUnderComposition (@AlgebraicGeometry.Surjective.{0}) :=
    { comp_mem _ _ hf hg := ⟨hg.surj.comp hf.surj⟩ }
  exact MorphismProperty.pullbackMap (P := @Surjective.{0}) ‹Surjective π› (inferInstance :
    Surjective (𝟙 T)) hπ.symm
    (Category.id_comp t).symm

theorem isPullback_curveChange_baseChangeSnd (π : C' ⟶ C) (hπ : π ≫ c = c')
    {T T' : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of R)} {t' : T' ⟶ Spec (CommRingCat.of R)}
    (ψ : SchemeHomOver t' t) :
    IsPullback (baseChangeSnd c' ψ) (curveChange π hπ t')
      (curveChange π hπ t) (baseChangeSnd c ψ) := by
  have sqC : ∀ {S : Scheme.{0}} (s : S ⟶ Spec (CommRingCat.of R)),
      IsPullback (curveChange π hπ s) (pullback.fst c' s) (pullback.fst c s) π := by
    intro S s
    have big : IsPullback (curveChange π hπ s ≫ pullback.snd c s)
        (pullback.fst c' s) s (π ≫ c) := by
      rw [curveChange_snd, hπ]
      exact (IsPullback.of_hasPullback c' s).flip
    have hcomm : curveChange π hπ s ≫ pullback.fst c s = pullback.fst c' s ≫ π := by
      simp only [curveChange, pullback.lift_fst]
    exact IsPullback.of_right big hcomm (IsPullback.of_hasPullback c s).flip
  have h1 : baseChangeSnd c' ψ ≫ pullback.fst c' t = pullback.fst c' t' := by
    simp only [baseChangeSnd, pullback.map]; rw [pullback.lift_fst, Category.comp_id]
  have h2 : baseChangeSnd c ψ ≫ pullback.fst c t = pullback.fst c t' := by
    simp only [baseChangeSnd, pullback.map]; rw [pullback.lift_fst, Category.comp_id]
  have big : IsPullback (baseChangeSnd c' ψ ≫ pullback.fst c' t) (curveChange π hπ t') π
      (baseChangeSnd c ψ ≫ pullback.fst c t) := by
    rw [h1, h2]; exact (sqC t').flip
  exact (IsPullback.of_right big (curveChange_baseChangeSnd π hπ ψ).symm (sqC t).flip)

theorem flat_baseChangeSnd {T T' : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of R)}
    {t' : T' ⟶ Spec (CommRingCat.of R)} (ψ : SchemeHomOver t' t) [Flat ψ.1] : Flat (baseChangeSnd c
      ψ) :=
  MorphismProperty.pullbackMap (P := @Flat) (inferInstance : Flat (𝟙 C)) ‹Flat ψ.1›
    (Category.id_comp c).symm
    (by simpa only [Category.comp_id, Category.id_comp] using ψ.2.symm)

/-- Reorder four tensor factors using the associator and the symmetry. -/
def shuffle {V : Type 1} [Category.{0} V] [MonoidalCategory V] [SymmetricCategory V] (A B X Y : V) :
    (A ⊗ B) ⊗ (X ⊗ Y) ≅ (A ⊗ X) ⊗ (B ⊗ Y) :=
  (α_ A B (X ⊗ Y)) ≪≫ (Iso.refl A ⊗ᵢ ((α_ B X Y).symm ≪≫ (β_ B X ⊗ᵢ Iso.refl Y) ≪≫ α_ X B Y)) ≪≫
    (α_ A X (B ⊗ Y)).symm

theorem nonempty_rigidify_tensor_iso {T P : Scheme.{0}} (σ : T ⟶ P) (q : P ⟶ T) {A B : P.Modules}
    (hA : Scheme.Modules.IsInvertible A) (hB : Scheme.Modules.IsInvertible B) :
    Nonempty (Scheme.Modules.rigidify σ q (A ⊗ B) ≅ Scheme.Modules.rigidify σ q A ⊗
      Scheme.Modules.rigidify σ q B) := by
  rw [Scheme.Modules.rigidify_def, Scheme.Modules.rigidify_def, Scheme.Modules.rigidify_def]
  obtain ⟨edual⟩ := (hA.pullback σ).dual_tensor (hB.pullback σ)
  refine ⟨(Iso.refl _ ⊗ᵢ ((Scheme.Modules.pullback q).mapIso
      (Scheme.Modules.dualMapIso (Scheme.Modules.pullbackTensorObjIso σ A B) ≪≫ edual) ≪≫
      Scheme.Modules.pullbackTensorObjIso q _ _)) ≪≫ shuffle _ _ _ _⟩

end ModularCurve.PrimBody

end JacobianVarieties.Picard.Proofs.NormTensorMultiplication

namespace AlgebraicGeometry.RelPicard.RepresentsRelSubPic

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory
open _root_.AlgebraicGeometry
open _root_.NeronModelInfra
open _root_.GoodReductionJacobian
open _root_.AlgebraicGeometry.RelPicard
open _root_.AlgebraicGeometry.SmoothProperCurve
open _root_.AlgebraicGeometry.Scheme.Modules
open JacobianVarieties.Picard.Proofs.NormTensorMultiplication

open ModularCurve.PrimBody in
theorem nonempty_pullbackAlong_mul_iso_tensor_ofInvertible_norm_pullback_poincare
    (R : Type) [CommRing R]
    {C C' : Scheme.{0}} (c : C ⟶ Spec (CommRingCat.of R)) (c' : C' ⟶ Spec (CommRingCat.of R))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (π₁ π₂ : SchemeHomOver c' c) [IsFinite π₂.1] [Surjective π₂.1]
    (D : RelativePic0Designation R c)
    (hD : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)
    [IsIntegral ↑(pullback c' D.toBase)] [IsIntegral ↑(pullback c D.toBase)]
    (hnorm : ∀ U : (pullback c D.toBase).Opens, IsAffineOpen U →
      IsIntegrallyClosed Γ(pullback c D.toBase, U))
    [Flat D.toBase] [LocallyOfFiniteType D.toBase]
    [IsIntegral ↑(pullback c' (pullback.fst D.toBase D.toBase ≫ D.toBase))]
    [IsIntegral ↑(pullback c (pullback.fst D.toBase D.toBase ≫ D.toBase))]
    (hnorm₂ : ∀ U : (pullback c (pullback.fst D.toBase D.toBase ≫ D.toBase)).Opens, IsAffineOpen U →
      IsIntegrallyClosed Γ(pullback c (pullback.fst D.toBase D.toBase ≫ D.toBase), U))
    (Nm : ∀ ⦃X Y : Scheme.{0}⦄, (X ⟶ Y) → X.Modules → Y.Modules)
    (hNm :
      ∀ ⦃X Y : Scheme.{0}⦄ (π : X ⟶ Y) [IsFinite π] [Surjective π] [IsIntegral X] [IsIntegral Y],
        (∀ U : Y.Opens, IsAffineOpen U → IsIntegrallyClosed Γ(Y, U)) →
        (∀ L : X.Modules, Scheme.Modules.IsInvertible L → Scheme.Modules.IsInvertible (Nm π L)) ∧
        (∀ L L' : X.Modules, Scheme.Modules.IsInvertible L → Nonempty (L ≅ L') →
          Nonempty (Nm π L ≅ Nm π L')) ∧
        (∀ L L' : X.Modules, Scheme.Modules.IsInvertible L → Scheme.Modules.IsInvertible L' →
          Nonempty (Nm π (L ⊗ L') ≅ Nm π L ⊗ Nm π L')) ∧
        Nonempty (Nm π (𝟙_ X.Modules) ≅ 𝟙_ Y.Modules) ∧
        (∀ ⦃X' Y' : Scheme.{0}⦄ (g : Y' ⟶ Y) (π' : X' ⟶ Y') (g' : X' ⟶ X), IsPullback g' π' π g →
          ∀ [Flat g] [IsIntegral X'] [IsIntegral Y'],
          (∀ U : Y'.Opens, IsAffineOpen U → IsIntegrallyClosed Γ(Y', U)) →
          ∀ L : X.Modules, Scheme.Modules.IsInvertible L →
            Nonempty ((Scheme.Modules.pullback g).obj (Nm π L) ≅
              Nm π' ((Scheme.Modules.pullback g').obj L))) ∧
        (∀ (V : Y.Opens) (d : ℕ), Flat (π ∣_ V) → LocallyOfFinitePresentation (π ∣_ V) →
          (∀ y : V, (π ∣_ V).finrank y = d) →
          ∀ L : X.Modules, Scheme.Modules.IsInvertible L →
            Nonempty ((Scheme.Modules.pullback V.ι).obj (Nm π L) ≅
              Scheme.Modules.normModule (π ∣_ V) d ((Scheme.Modules.pullback (π ⁻¹ᵁ V).ι).obj L))))
    (hinv : Scheme.Modules.IsInvertible
      (Nm (curveChange π₂.1 π₂.2 D.toBase) ((Scheme.Modules.pullback (curveChange π₁.1 π₁.2
        D.toBase)).obj hD.poincare.L)))
    {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver s D.toBase) :
    Nonempty (((RigidifiedLineBundle.ofInvertible (ε := ε) (Nm (curveChange π₂.1 π₂.2 D.toBase)
      ((Scheme.Modules.pullback (curveChange π₁.1 π₁.2 D.toBase)).obj hD.poincare.L))
      hinv).pullbackAlong
        ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD).mul s x y)).L ≅
      (((RigidifiedLineBundle.ofInvertible (ε := ε) (Nm (curveChange π₂.1 π₂.2 D.toBase)
        ((Scheme.Modules.pullback (curveChange π₁.1 π₁.2 D.toBase)).obj hD.poincare.L))
        hinv).pullbackAlong x).tensor
        ((RigidifiedLineBundle.ofInvertible (ε := ε) (Nm (curveChange π₂.1 π₂.2 D.toBase)
          ((Scheme.Modules.pullback (curveChange π₁.1 π₁.2 D.toBase)).obj hD.poincare.L))
          hinv).pullbackAlong y)).L) := by
  let M := (Nm (curveChange π₂.1 π₂.2 D.toBase) ((Scheme.Modules.pullback (curveChange π₁.1 π₁.2
    D.toBase)).obj hD.poincare.L))
  let M' := RigidifiedLineBundle.ofInvertible (ε := ε) M hinv
  let t₂ : pullback D.toBase D.toBase ⟶ Spec (CommRingCat.of R) := pullback.fst D.toBase D.toBase ≫
    D.toBase
  let pr₁D : SchemeHomOver t₂ D.toBase := ⟨pullback.fst D.toBase D.toBase, rfl⟩
  let pr₂D : SchemeHomOver t₂ D.toBase := ⟨pullback.snd D.toBase D.toBase, pullback.condition.symm⟩
  let G := RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) hD
  let mulD : SchemeHomOver t₂ D.toBase := G.mul t₂ pr₁D pr₂D
  have univ : Nonempty ((M'.pullbackAlong mulD).L ≅ ((M'.pullbackAlong pr₁D).tensor
    (M'.pullbackAlong pr₂D)).L) := by
    have := ModularCurve.PrimBody.isFinite_curveChange' π₂.1 π₂.2 D.toBase
    have := ModularCurve.PrimBody.surjective_curveChange' π₂.1 π₂.2 D.toBase
    have := ModularCurve.PrimBody.isFinite_curveChange' π₂.1 π₂.2 t₂
    have := ModularCurve.PrimBody.surjective_curveChange' π₂.1 π₂.2 t₂
    obtain ⟨h0, ha, hb, -, hd, -⟩ := hNm (curveChange π₂.1 π₂.2 D.toBase) hnorm
    obtain ⟨h0₂, ha₂, hb₂, -, -, -⟩ := hNm (curveChange π₂.1 π₂.2 t₂) hnorm₂
    let P : (pullback c D.toBase).Modules := hD.poincare.L
    let L₁ : (pullback c' D.toBase).Modules := (Scheme.Modules.pullback (curveChange π₁.1 π₁.2
      D.toBase)).obj P
    have hP : Scheme.Modules.IsInvertible P := hD.poincare.isInvertible
    have hL₁ : Scheme.Modules.IsInvertible L₁ := hP.pullback _
    have U1 : ∀ (g : SchemeHomOver t₂ D.toBase) [Flat g.1],
        Nonempty ((Scheme.Modules.pullback (baseChangeSnd c g)).obj M ≅
          Nm (curveChange π₂.1 π₂.2 t₂)
            ((Scheme.Modules.pullback (curveChange π₁.1 π₁.2 t₂)).obj ((Scheme.Modules.pullback
              (baseChangeSnd c g)).obj P))) := by
      intro g _
      have : Flat (baseChangeSnd c g) := ModularCurve.PrimBody.flat_baseChangeSnd g
      obtain ⟨e1⟩ := hd (baseChangeSnd c g) (curveChange π₂.1 π₂.2 t₂) (baseChangeSnd c' g)
        (ModularCurve.PrimBody.isPullback_curveChange_baseChangeSnd π₂.1 π₂.2 g) hnorm₂ L₁ hL₁
      have e2 : (Scheme.Modules.pullback (baseChangeSnd c' g)).obj L₁ ≅
          (Scheme.Modules.pullback (curveChange π₁.1 π₁.2 t₂)).obj ((Scheme.Modules.pullback
            (baseChangeSnd c g)).obj P) :=
        (Scheme.Modules.pullbackComp _ _).app P ≪≫
          (Scheme.Modules.pullbackCongr (curveChange_baseChangeSnd π₁.1 π₁.2 g).symm).app P ≪≫
          ((Scheme.Modules.pullbackComp _ _).app P).symm
      exact ⟨e1 ≪≫ (ha₂ _ _ (hL₁.pullback _) ⟨e2⟩).some⟩
    let := RepresentsRelSubPic.grpObj (P := algEquivZeroGroupCut c ε) hD
    let := (algEquivZeroGroupCut c ε).commGroupObj (Opposite.op (Over.mk t₂))
    have U2 : Nonempty ((Scheme.Modules.pullback (baseChangeSnd c mulD)).obj P ≅
        (Scheme.Modules.pullback (baseChangeSnd c pr₁D)).obj P ⊗ (Scheme.Modules.pullback
          (baseChangeSnd c pr₂D)).obj P) :=
      Quotient.exact (congrArg Subtype.val
        (RepresentsRelSubPic.homEquiv_mul (P := algEquivZeroGroupCut c ε) hD (Over.mk t₂)
          (schemeHomOverToOverHom pr₁D) (schemeHomOverToOverHom pr₂D)))
    have : Flat mulD.1 :=
      AlgebraicGeometry.RelPicard.RepresentsRelSubPic.flat_mul_fst_snd (P := algEquivZeroGroupCut c
        ε) hD
    have : Flat pr₁D.1 := by
      change Flat (pullback.fst D.toBase D.toBase)
      infer_instance
    have : Flat pr₂D.1 := by
      change Flat (pullback.snd D.toBase D.toBase)
      infer_instance
    let Q : SchemeHomOver t₂ D.toBase → (pullback c' t₂).Modules := fun g =>
      (Scheme.Modules.pullback (curveChange π₁.1 π₁.2 t₂)).obj ((Scheme.Modules.pullback
        (baseChangeSnd c g)).obj P)
    have hQ : ∀ g, Scheme.Modules.IsInvertible (Q g) := fun g => (hP.pullback _).pullback _
    have core : Nonempty ((Scheme.Modules.pullback (baseChangeSnd c mulD)).obj M ≅
        (Scheme.Modules.pullback (baseChangeSnd c pr₁D)).obj M ⊗ (Scheme.Modules.pullback
          (baseChangeSnd c pr₂D)).obj M) := by
      obtain ⟨em⟩ := U1 mulD
      obtain ⟨e1⟩ := U1 pr₁D
      obtain ⟨e2⟩ := U1 pr₂D
      have eQ : Q mulD ≅ Q pr₁D ⊗ Q pr₂D :=
        (Scheme.Modules.pullback (curveChange π₁.1 π₁.2 t₂)).mapIso U2.some ≪≫
          Scheme.Modules.pullbackTensorObjIso _ _ _
      obtain ⟨ea⟩ := ha₂ _ _ (hQ mulD) ⟨eQ⟩
      obtain ⟨ebb⟩ := hb₂ _ _ (hQ pr₁D) (hQ pr₂D)
      exact ⟨em ≪≫ ea ≪≫ ebb ≪≫ (e1.symm ⊗ᵢ e2.symm)⟩
    have F : ∀ g : SchemeHomOver t₂ D.toBase, Nonempty ((M'.pullbackAlong g).L ≅
        Scheme.Modules.rigidify (rigSection c t₂ ε) (pullback.snd c t₂) ((Scheme.Modules.pullback
          (baseChangeSnd c g)).obj M)) :=
      fun g => Scheme.Modules.IsInvertible.nonempty_pullback_rigidify_iso g.1 (baseChangeSnd c g)
        (rigSection_baseChangeSnd c ε g)
          (by simp only [baseChangeSnd, pullback.map]; exact pullback.lift_snd _ _ _) hinv
    obtain ⟨ec⟩ := core
    obtain ⟨ert⟩ := ModularCurve.PrimBody.nonempty_rigidify_tensor_iso (rigSection c t₂ ε)
      (pullback.snd c t₂)
      (hinv.pullback (baseChangeSnd c pr₁D)) (hinv.pullback (baseChangeSnd c pr₂D))
    exact ⟨(F mulD).some ≪≫ Scheme.Modules.rigidifyMapIso _ _ ec ≪≫ ert ≪≫ ((F pr₁D).some.symm ⊗ᵢ
      (F pr₂D).some.symm)⟩
  let pair : SchemeHomOver s t₂ :=
    ⟨pullback.lift x.1 y.1 (x.2.trans y.2.symm), by
      change pullback.lift x.1 y.1 _ ≫ (pullback.fst D.toBase D.toBase ≫ D.toBase) = s
      rw [pullback.lift_fst_assoc, x.2]⟩
  have hx : postComp pr₁D pair = x := Subtype.ext (pullback.lift_fst _ _ _)
  have hy : postComp pr₂D pair = y := Subtype.ext (pullback.lift_snd _ _ _)
  have hmul : postComp mulD pair = G.mul s x y := by
    have nat := G.mul_natural t₂ s pair.1 pair.2 pr₁D pr₂D
    have e0 : ∀ a : SchemeHomOver t₂ D.toBase,
        GoodReductionJacobian.schemeHomOverComp pair.1 pair.2 a = postComp a pair := fun a =>
          Subtype.ext rfl
    rw [e0, e0, e0, hx, hy] at nat
    exact nat
  have ecomp : ∀ a : SchemeHomOver t₂ D.toBase,
      (M'.pullbackAlong (postComp a pair)).L ≅
        ((M'.pullbackAlong a).pullbackAlong pair).L := fun a =>
    (Scheme.Modules.pullbackCongr (baseChangeSnd_comp c a pair).symm).app _ ≪≫
      ((Scheme.Modules.pullbackComp (baseChangeSnd c pair) (baseChangeSnd c a)).app _).symm
  have eL : (M'.pullbackAlong (G.mul s x y)).L ≅ ((M'.pullbackAlong mulD).pullbackAlong pair).L :=
    (Scheme.Modules.pullbackCongr (show baseChangeSnd c (G.mul s x y) = baseChangeSnd c (postComp
      mulD pair)
      by rw [hmul])).app _ ≪≫ ecomp mulD
  have eX : ((M'.pullbackAlong pr₁D).pullbackAlong pair).L ≅ (M'.pullbackAlong x).L :=
    (ecomp pr₁D).symm ≪≫ (Scheme.Modules.pullbackCongr (show baseChangeSnd c (postComp pr₁D pair) =
      baseChangeSnd c x by rw [hx])).app _
  have eY : ((M'.pullbackAlong pr₂D).pullbackAlong pair).L ≅ (M'.pullbackAlong y).L :=
    (ecomp pr₂D).symm ≪≫ (Scheme.Modules.pullbackCongr (show baseChangeSnd c (postComp pr₂D pair) =
      baseChangeSnd c y by rw [hy])).app _
  exact ⟨eL ≪≫ (Scheme.Modules.pullback (baseChangeSnd c pair)).mapIso univ.some ≪≫
    (RigidifiedLineBundle.nonempty_tensor_pullbackAlong_iso pair _ _).some ≪≫ (eX ⊗ᵢ eY)⟩
end AlgebraicGeometry.RelPicard.RepresentsRelSubPic
end ProofImplementation
