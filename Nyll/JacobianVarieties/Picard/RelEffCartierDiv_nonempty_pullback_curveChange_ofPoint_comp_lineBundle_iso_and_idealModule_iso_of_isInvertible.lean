/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_RelEffCartierDiv_nonempty_pullback_curveChange_ofPoint_comp_lineBundle_iso_and_idealModule_iso_of_isInvertible.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.Util.WithWeakNamespace
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
import Mathlib.Topology.Sheaves.SheafCondition.Sites
import Mathlib.Algebra.Category.Ring.Constructions
import Mathlib.Algebra.Category.ModuleCat.Presheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.Data.List.FinRange
import Nyll.AlgebraicCurves.Geometry.Picard.Pullback
import Nyll.AlgebraicCurves.Geometry.Sheaves.IdealSheafModule
import Nyll.AlgebraicCurves.RelativeDivisors.RelEffCartierDiv
import Nyll.AlgebraicCurves.RelativeDivisors.RelEffCartierDivOfPoint
import Nyll.AlgebraicCurves.RelativeDivisors.Cartier
import Nyll.SchemeTheory.Modules.Monoidal
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_nonempty_pullback_foldr_twist_iso
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_IdealSheafData_IsInvertible_nonempty_module_tensor_invModule_iso
import Nyll.AlgebraicCurves.Foundations.CategoryTheory.CategoryTheory_MonoidalCategory_nonempty_iso_of_tensor_iso_tensorUnit

import Nyll.JacobianVarieties.Picard.RepresentsRelSubPicPullback
/-!
# Pullback of point-divisor modules along a closed curve immersion

The graph squares identify the pulled-back point ideal. Express each ideal
module and inverse ideal module as the corresponding one-term tensor expression,
then apply the existing pullback comparison for invertible ideal twists.
-/

section ProofImplementation

namespace JacobianVarieties.Picard.Proofs.PointIdealPullback
attribute [-instance]
  AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap
  AlgebraicGeometry.Scheme.Modules.pullback_monoidal
  AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization'
  AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap
  AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal
  AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap
  AlgebraicGeometry.Scheme.Modules.sheafifyPullback_lifting
  PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ
  PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η
  PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal
  PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal
open _root_.PresheafOfModules.PullbackMonoidal in
attribute [-instance]
  instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb
attribute [-instance]
  PresheafOfModules.pullback_monoidal'
attribute [-simp]
  PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app
  AlgebraicGeometry.Scheme.Modules.toUnitSection_ofUnitSection
  AlgebraicGeometry.Scheme.Modules.pullbackSection_def
  AlgebraicGeometry.Scheme.Modules.ofUnitSection_toUnitSection

universe u


open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory
open _root_.AlgebraicGeometry
open _root_.AlgebraicGeometry.RelPicard
open _root_.NeronModelInfra


noncomputable section

namespace Ws50Restrict

section top
variable {X : Scheme.{u}}

theorem subsingleton_sections_of_isEmpty {Z : Scheme.{u}} [IsEmpty Z] (V : Z.Opens) :
    Subsingleton Γ(Z, V) := by
  obtain rfl : V = ⊥ := by
    ext x
    exact (IsEmpty.false x).elim
  exact CommRingCat.subsingleton_of_isTerminal (TopCat.Sheaf.isTerminalOfEmpty Z.sheaf)

theorem unitToPushforwardUnit_eq_zero_of_isEmpty {Z : Scheme.{u}} (i : Z ⟶ X) [IsEmpty Z] :
    i.unitToPushforwardUnit = 0 := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  ext
  have : Subsingleton Γ(Z, i ⁻¹ᵁ U.unop) := subsingleton_sections_of_isEmpty _
  exact Subsingleton.elim (α := Γ(Z, i ⁻¹ᵁ U.unop)) _ _

/-- The ideal module of the unit ideal is the unit module. -/
def topModuleIso : (⊤ : X.IdealSheafData).module ≅ 𝟙_ X.Modules :=
  (kernelIsoOfEq (unitToPushforwardUnit_eq_zero_of_isEmpty (⊤ : X.IdealSheafData).subschemeι) ≪≫
    kernelZeroIsoSource : (kernel ((⊤ : X.IdealSheafData).subschemeι.unitToPushforwardUnit) :
      SheafOfModules X.ringCatSheaf) ≅ SheafOfModules.unit X.ringCatSheaf)

theorem nonempty_topInvModuleIso : Nonempty ((⊤ : X.IdealSheafData).invModule ≅ 𝟙_ X.Modules) :=
  MonoidalCategory.nonempty_iso_of_tensor_iso_tensorUnit (topModuleIso (X := X))
    (Scheme.IdealSheafData.isInvertible_top (X := X)).nonempty_module_tensor_invModule_iso.1 ⟨λ_ _⟩

/-- The inverse module of the unit ideal is the unit module. -/
def topInvModuleIso : (⊤ : X.IdealSheafData).invModule ≅ 𝟙_ X.Modules :=
  nonempty_topInvModuleIso.some

/-- Insert unit factors to express an inverse ideal module as a one-term twist. -/
def shapeInv (K : X.IdealSheafData) :
    K.invModule ≅ (K ^ 1).invModule ⊗
      ((K ^ 0).module ⊗ ((1 : X.IdealSheafData).invModule ⊗ (1 : X.IdealSheafData).module)) :=
  (ρ_ K.invModule).symm ≪≫
    ((eqToIso (by rw [pow_one]) : K.invModule ≅ (K ^ 1).invModule) ⊗ᵢ
      ((λ_ (𝟙_ X.Modules)).symm ≪≫
        ((((eqToIso (by rw [pow_zero, Scheme.IdealSheafData.one_eq_top]) :
          (K ^ 0).module ≅
            (⊤ : X.IdealSheafData).module) ≪≫
            topModuleIso).symm) ⊗ᵢ
          ((λ_ (𝟙_ X.Modules)).symm ≪≫
            ((((eqToIso (by rw [Scheme.IdealSheafData.one_eq_top]) :
              (1 : X.IdealSheafData).invModule ≅
                (⊤ : X.IdealSheafData).invModule) ≪≫
                topInvModuleIso).symm) ⊗ᵢ
              (((eqToIso (by rw [Scheme.IdealSheafData.one_eq_top]) :
                (1 : X.IdealSheafData).module ≅
                  (⊤ : X.IdealSheafData).module) ≪≫
                topModuleIso).symm))))))

/-- Insert unit factors to express an ideal module as a one-term twist. -/
def shapeMod (K : X.IdealSheafData) :
    K.module ≅ (K ^ 0).invModule ⊗
      ((K ^ 1).module ⊗ ((1 : X.IdealSheafData).invModule ⊗ (1 : X.IdealSheafData).module)) :=
  (λ_ K.module).symm ≪≫
    ((((eqToIso (by rw [pow_zero, Scheme.IdealSheafData.one_eq_top]) :
      (K ^ 0).invModule ≅
        (⊤ : X.IdealSheafData).invModule) ≪≫
        topInvModuleIso).symm) ⊗ᵢ
      ((ρ_ K.module).symm ≪≫
        ((eqToIso (by rw [pow_one]) : K.module ≅ (K ^ 1).module) ⊗ᵢ
          ((λ_ (𝟙_ X.Modules)).symm ≪≫
            ((((eqToIso (by rw [Scheme.IdealSheafData.one_eq_top]) :
              (1 : X.IdealSheafData).invModule ≅
                (⊤ : X.IdealSheafData).invModule) ≪≫
                topInvModuleIso).symm) ⊗ᵢ
              (((eqToIso (by rw [Scheme.IdealSheafData.one_eq_top]) :
                (1 : X.IdealSheafData).module ≅
                  (⊤ : X.IdealSheafData).module) ≪≫
                topModuleIso).symm))))))

end top

theorem comap_ker_eq_ker_of_isPullback {X₀ X T Z : Scheme.{u}} {iX : Z ⟶ X₀} {g : Z ⟶ T}
    {f : X₀ ⟶ X}
    {iY : T ⟶ X} [IsClosedImmersion iY] (H : IsPullback iX g f iY) : iY.ker.comap f = iX.ker := by
  rw [← Scheme.IdealSheafData.ker_fst_of_isClosedImmersion, ← H.isoPullback_hom_fst,
    Scheme.Hom.ker_comp_of_isIso]

section squares
variable {R : Type u} [CommRing R] {X C : Scheme.{u}}
  {x : X ⟶ Spec (CommRingCat.of R)}
  {c : C ⟶ Spec (CommRingCat.of R)}
  (i : C ⟶ X) (hi : i ≫ x = c)

theorem isPullback_curveChange_fst {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) :
    IsPullback (curveChange i hi t) (pullback.fst c t) (pullback.fst x t) i := by
  have big : IsPullback (curveChange i hi t ≫ pullback.snd x t) (pullback.fst c t) t (i ≫ x) := by
    rw [curveChange_snd, hi]
    exact (IsPullback.of_hasPullback c t).flip
  have hcomm : curveChange i hi t ≫ pullback.fst x t = pullback.fst c t ≫ i := by
    simp only [curveChange, pullback.lift_fst]
  exact IsPullback.of_right big hcomm (IsPullback.of_hasPullback x t).flip

theorem isPullback_id_of_mono [Mono i] {T : Scheme.{u}} (d : T ⟶ C) :
    IsPullback (𝟙 T) d (d ≫ i) i := by
  refine IsPullback.of_isLimit' ⟨by rw [Category.id_comp]⟩ ?_
  refine PullbackCone.IsLimit.mk _ (fun s => s.fst) (fun s => Category.comp_id _)
    (fun s => ?_) (fun s m h₁ _ => ?_)
  · have h := s.condition
    rw [← Category.assoc] at h
    exact (cancel_mono i).mp h
  · rw [Category.comp_id] at h₁
    exact h₁

theorem isPullback_graphOver [IsSeparated x] [IsSeparated c] [Mono i] {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R))
    (d : T ⟶ C) (hd : d ≫ c = t) (hdi : (d ≫ i) ≫ x = t) :
    IsPullback (graphOver c d hd) (𝟙 T) (curveChange i hi t) (graphOver x (d ≫ i) hdi) := by
  have hcomm : 𝟙 T ≫ graphOver x (d ≫ i) hdi = graphOver c d hd ≫ curveChange i hi t := by
    apply pullback.hom_ext
    · rw [Category.id_comp, graphOver_fst, Category.assoc, (isPullback_curveChange_fst i hi t).w,
        ← Category.assoc, graphOver_fst]
    · rw [Category.id_comp, graphOver_snd, Category.assoc, curveChange_snd, graphOver_snd]
  have outer : IsPullback (𝟙 T) (graphOver c d hd ≫ pullback.fst c t)
      (graphOver x (d ≫ i) hdi ≫ pullback.fst x t) i := by
    rw [graphOver_fst, graphOver_fst]
    exact isPullback_id_of_mono i d
  exact (IsPullback.of_bot outer hcomm (isPullback_curveChange_fst i hi t)).flip

end squares

end Ws50Restrict

end

open Ws50Restrict in
with_weak_namespace _root_.AlgebraicGeometry.RelEffCartierDiv
theorem nonempty_curveChange_ofPoint_modules_iso_of_isInvertible
    {R : Type u} [CommRing R] {X C : Scheme.{u}}
    (x : X ⟶ Spec (CommRingCat.of R))
    (c : C ⟶ Spec (CommRingCat.of R)) [IsSeparated x] [IsSeparated c]
    (i : C ⟶ X) [IsClosedImmersion i] (hi : i ≫ x = c)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (d : T ⟶ C) (hd : d ≫ c = t)
    (hC : (RelEffCartierDiv.ofPoint c d hd).I.IsInvertible)
    (hX : (RelEffCartierDiv.ofPoint x (d ≫ i) (by rw [Category.assoc, hi, hd])).I.IsInvertible) :
    Nonempty ((Scheme.Modules.pullback (curveChange i hi t)).obj
        (RelEffCartierDiv.ofPoint x (d ≫ i) (by rw [Category.assoc, hi, hd])).lineBundle ≅
      (RelEffCartierDiv.ofPoint c d hd).lineBundle) ∧
    Nonempty ((Scheme.Modules.pullback (curveChange i hi t)).obj
        (RelEffCartierDiv.ofPoint x (d ≫ i) (by rw [Category.assoc, hi, hd])).idealModule ≅
      (RelEffCartierDiv.ofPoint c d hd).idealModule) := by
  classical
  set Φ := curveChange i hi t with hΦ
  set Kx := (RelEffCartierDiv.ofPoint x (d ≫ i) (by rw [Category.assoc, hi, hd])).I with hKx
  set Kc := (RelEffCartierDiv.ofPoint c d hd).I with hKc
  have hcomap : Kx.comap Φ = Kc := by
    rw [hKx, hKc, RelEffCartierDiv.ofPoint_I, RelEffCartierDiv.ofPoint_I]
    exact comap_ker_eq_ker_of_isPullback
      (isPullback_graphOver i hi t d hd (by rw [Category.assoc, hi, hd]))
  have hKc' : (Kx.comap Φ).IsInvertible := by rw [hcomap]; exact hC
  have h1inv : ∀ (Z : Scheme.{u}), (1 : Z.IdealSheafData).IsInvertible := fun Z => by
    rw [Scheme.IdealSheafData.one_eq_top]; exact Scheme.IdealSheafData.isInvertible_top
  have key : ∀ (pos neg : Fin 1 → ℕ),
      Nonempty ((Scheme.Modules.pullback Φ).obj
          ((Kx ^ pos 0).invModule ⊗
             ((Kx ^ neg 0).module ⊗ ((1 : (pullback x t).IdealSheafData).invModule ⊗
              (1 : (pullback x t).IdealSheafData).module))) ≅
        (Kc ^ pos 0).invModule ⊗
           ((Kc ^ neg 0).module ⊗ ((1 : (pullback c t).IdealSheafData).invModule ⊗
            (1 : (pullback c t).IdealSheafData).module))) := by
    intro pos neg
    obtain ⟨e⟩ := Scheme.Modules.nonempty_pullback_foldr_twist_iso Φ (m := 1) (fun _ => Kx) pos neg
      (ι := Fin 0) (fun _ => ⊤) (fun _ => 0) (fun _ => 0)
      (fun _ => hX) (fun F => F.elim0) (fun _ => hKc') (fun F => F.elim0)
    have hfr : List.finRange 1 = [(0 : Fin 1)] := rfl
    rw [hfr] at e
    simp only [List.foldr_cons, List.foldr_nil, Fintype.prod_empty, hcomap] at e
    exact ⟨e⟩
  refine ⟨?_, ?_⟩
  · obtain ⟨e⟩ := key ![1] ![0]
    exact ⟨(Scheme.Modules.pullback Φ).mapIso (shapeInv Kx) ≪≫ e ≪≫ (shapeInv Kc).symm⟩
  · obtain ⟨e⟩ := key ![0] ![1]
    exact ⟨(Scheme.Modules.pullback Φ).mapIso (shapeMod Kx) ≪≫ e ≪≫ (shapeMod Kc).symm⟩
end JacobianVarieties.Picard.Proofs.PointIdealPullback
end ProofImplementation
