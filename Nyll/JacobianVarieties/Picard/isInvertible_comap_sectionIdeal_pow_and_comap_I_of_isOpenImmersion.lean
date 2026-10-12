/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_RelPicard_isInvertible_comap_sectionIdeal_pow_and_comap_I_of_isOpenImmersion.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.Util.WithWeakNamespace
import Mathlib.CategoryTheory.Iso
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting
import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.Topology.Maps.Basic
import Nyll.AlgebraicCurves.Geometry.Picard.Functor
import Nyll.JacobianVarieties.Picard.ThetaBundle
import Nyll.AlgebraicCurves.Geometry.Picard.AlgEquivZeroCut
import Nyll.SchemeTheory.Cohomology.Cech.TwoAffineOpenCover
import Nyll.AlgebraicCurves.Cohomology.Cech.TwoChartCechSectionsOf
import Nyll.AlgebraicCurves.RelativeDivisors.RelEffCartierDiv
import Nyll.AlgebraicCurves.RelativeDivisors.RelEffCartierDivSupportedIn
import Nyll.AlgebraicCurves.Geometry.Sheaves.IdealSheafModule
import Nyll.SchemeTheory.Modules.Monoidal
import Nyll.AlgebraicCurves.Models.Basic
import Nyll.AlgebraicCurves.RelativeDivisors.Cartier
import Nyll.AlgebraicCurves.RelativeDivisors.RelEffCartierDivOfPoint
import Nyll.AlgebraicCurves.RelativeDivisors.RelEffCartierDiv_pullbackAlong_ofPoint
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_IdealSheafData_comap_mul
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_IdealSheafData_IsInvertible_comap_of_isOpenImmersion
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_IdealSheafData_IsInvertible_of_comap_of_support_subset_range
import Nyll.AlgebraicCurves.Geometry.Picard.isInvertible_sectionIdeal_of_range_subset
import Nyll.AlgebraicCurves.RelativeDivisors.RelEffCartierDiv_isInvertible_I_of_supportedIn
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_IdealSheafData_IsInvertible_pow

/-!
# Invertible ideals on open parts of a curve fibre

Compare an iterated fibre with the original fibre. Pull back the section ideal
and a relative Cartier divisor, then use their support conditions to extend
invertibility from the given open part of the curve model.
-/

section ProofImplementation

namespace JacobianVarieties.Picard.Proofs.OpenSectionIntersection
attribute [-instance]
  AlgebraicGeometry.RelEffCartierDiv.isClosedImmersion_subschemeι_resProdMap
  AlgebraicGeometry.RelEffCartierDiv.isOpenImmersion_resProdMap
attribute [-simp]
  AlgebraicGeometry.RelEffCartierDiv.restrictAlong_extendAlong
  AlgebraicGeometry.RelEffCartierDiv.extendAlong_I
  AlgebraicGeometry.RelEffCartierDiv.resProdMap_snd
  AlgebraicGeometry.RelEffCartierDiv.restrictAlong_I
  AlgebraicGeometry.RelEffCartierDiv.extendAlong_restrictAlong
  AlgebraicGeometry.RelEffCartierDiv.resProdMap_fst_assoc
  AlgebraicGeometry.RelEffCartierDiv.resProdMap_snd_assoc
  AlgebraicGeometry.RelEffCartierDiv.resProdMap_fst

universe u


open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.Opposite
open _root_.CategoryTheory.MonoidalCategory
open _root_.AlgebraicGeometry
open _root_.AlgebraicGeometry.RelPicard
open _root_.AlgebraicCurve
open _root_.NeronModelInfra


noncomputable section

namespace ChildA

variable {R : Type u} [CommRing R]

section FibreIso

variable {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
  {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
  {k : Type u} [Field k] (s : Spec (CommRingCat.of k) ⟶ T)
  (x : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R))
  (hx : s ≫ t = x)

/-- The comparison between the iterated base-change fibre and the original fibre. -/
def fibreIso : pullback (pullback.snd c t) s ≅ pullback c x :=
  pullbackLeftPullbackSndIso c t s ≪≫ pullback.congrHom rfl hx

@[reassoc]
theorem fibreIso_hom_snd : (fibreIso c t s x hx).hom ≫ pullback.snd c x = fibreAt c t s := by
  subst hx
  simp only [fibreIso, Iso.trans_hom, pullback.congrHom_hom, Category.assoc,
    pullback.lift_snd, Category.comp_id, pullbackLeftPullbackSndIso_hom_snd, fibreAt]

@[reassoc]
theorem fibreIso_hom_fst :
    (fibreIso c t s x hx).hom ≫ pullback.fst c x =
      pullback.fst (pullback.snd c t) s ≫ pullback.fst c t := by
  subst hx
  simp only [fibreIso, Iso.trans_hom, pullback.congrHom_hom, Category.assoc,
    pullback.lift_fst, Category.comp_id, pullbackLeftPullbackSndIso_hom_fst]

theorem fibreIso_inv_fibreAt : (fibreIso c t s x hx).inv ≫ fibreAt c t s = pullback.snd c x := by
  rw [← fibreIso_hom_snd c t s x hx, Iso.inv_hom_id_assoc]

theorem fibreIso_hom_baseChangeSnd :
    (fibreIso c t s x hx).hom ≫ baseChangeSnd c (⟨s, hx⟩ : SchemeHomOver x t)
      = pullback.fst (pullback.snd c t) s := by
  apply pullback.hom_ext
  · rw [Category.assoc]
    unfold baseChangeSnd
    rw [pullback.lift_fst, ← Category.assoc, fibreIso_hom_fst, Category.assoc, Category.comp_id]
  · rw [Category.assoc]
    unfold baseChangeSnd
    rw [pullback.lift_snd, ← Category.assoc, fibreIso_hom_snd, pullback.condition]
    rfl

end FibreIso

theorem comap_pow {X Y : Scheme.{u}} (I : Y.IdealSheafData) (f : X ⟶ Y) (n : ℕ) :
    (I ^ n).comap f = (I.comap f) ^ n := by
  induction n with
  | zero =>
    simp only [pow_zero, Scheme.IdealSheafData.one_eq_top, Scheme.IdealSheafData.comap_top]
  | succ n ih => rw [pow_succ, pow_succ, Scheme.IdealSheafData.comap_mul, ih]

variable {R : Type u} [CommRing R] {C : Scheme.{u}}

theorem sectionIdeal_comap (c : C ⟶ Spec (CommRingCat.of R)) [IsSeparated c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) {T T' : Scheme.{u}}
    {t : T ⟶ Spec (CommRingCat.of R)} {t' : T' ⟶ Spec (CommRingCat.of R)}
    (ψ : SchemeHomOver t' t) :
    (RelPicard.sectionIdeal c ε t).comap (RelPicard.baseChangeSnd c ψ) =
      RelPicard.sectionIdeal c ε t' := by
  have hpt : (t ≫ ε.1) ≫ c = t := by rw [Category.assoc, ε.2, Category.comp_id]
  have hpt'' : (t' ≫ ε.1) ≫ c = t' := by rw [Category.assoc, ε.2, Category.comp_id]
  have hpt' : ψ.1 ≫ t ≫ ε.1 = t' ≫ ε.1 := by rw [← Category.assoc, ψ.2]
  have key := congrArg RelEffCartierDiv.I
    (RelEffCartierDiv.pullbackAlong_ofPoint c (t ≫ ε.1) hpt ψ.1 ψ.2)
  have e₁ : RelPicard.sectionIdeal c ε t = (RelEffCartierDiv.ofPoint c (t ≫ ε.1) hpt).I := rfl
  have e₂ : RelPicard.sectionIdeal c ε t' = (RelEffCartierDiv.ofPoint c (t' ≫ ε.1) hpt'').I := rfl
  have e₃ : (RelEffCartierDiv.ofPoint c (t ≫ ε.1) hpt).I.comap (RelPicard.baseChangeSnd c ψ) =
      ((RelEffCartierDiv.ofPoint c (t ≫ ε.1) hpt).pullbackAlong ψ.1 ψ.2).I := rfl
  rw [e₁, e₂, e₃, key]
  simp only [hpt']

theorem isInvertible_comap_line {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    {k : Type u} [Field k] (pt : Spec (CommRingCat.of k) ⟶ T)
    {Y : Scheme.{u}} (i₁ : Y ⟶ pullback (pullback.snd c t) pt)
    (W₁ : (pullback (pullback.snd c t) pt).Opens) [IsOpenImmersion ((i₁ ⁻¹ᵁ W₁).ι ≫ i₁)]
    (K : (pullback c t).IdealSheafData)
    (hK : (K.comap (pullback.fst (pullback.snd c t) pt)).IsInvertible)
    (hW : ∀ y : ↥(pullback (pullback.snd c t) pt),
      (pullback.fst (pullback.snd c t) pt).base y ∈ K.support →
        y ∈ W₁) :
    (K.comap (i₁ ≫ pullback.fst (pullback.snd c t) pt)).IsInvertible := by
  refine Scheme.IdealSheafData.IsInvertible.of_comap_of_support_subset_range (i₁ ⁻¹ᵁ W₁).ι _ ?_ ?_
  · intro x hx
    rw [Scheme.IdealSheafData.support_comap] at hx
    rw [Scheme.Opens.range_ι]
    exact hW (i₁.base x) hx
  · rw [← Scheme.IdealSheafData.comap_comp, ← Category.assoc, Scheme.IdealSheafData.comap_comp]
    exact hK.comap_of_isOpenImmersion _

end ChildA

open ChildA in
with_weak_namespace _root_.AlgebraicGeometry.RelPicard
theorem isInvertible_comap_sectionIdeal_pow_and_comap_I_of_isOpenImmersion
    (R : Type u) [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) [IsSeparated c]
    (U : C.Opens) [SmoothOfRelativeDimension 1 (U.ι ≫ c)]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) (hεU : Set.range ε.1 ⊆ (U : Set C))
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (r : ℕ) {e : ℕ} (D : RelEffCartierDiv c e t) (hDU : D.SupportedIn U)
    {k : Type u} [Field k] (pt : Spec (CommRingCat.of k) ⟶ T)
    {F₁ : Type u} [Field F₁] [Algebra k F₁] (M₁ : CurveModel k F₁)
    (i₁ : M₁.C ⟶ pullback (pullback.snd c t) pt)
    (W₁ : (pullback (pullback.snd c t) pt).Opens) [IsOpenImmersion ((i₁ ⁻¹ᵁ W₁).ι ≫ i₁)]
    (hD : ∀ y : ↥(pullback (pullback.snd c t) pt),
      (pullback.fst (pullback.snd c t) pt).base y ∈ D.I.support →
        y ∈ W₁)
    (hε : ∀ y : ↥(pullback (pullback.snd c t) pt),
      (pullback.fst (pullback.snd c t) pt).base y ∈ Set.range (rigSection c t ε).base →
        y ∈ W₁) :
    (((sectionIdeal c ε t) ^ r).comap (i₁ ≫ pullback.fst (pullback.snd c t) pt)).IsInvertible ∧
      (D.I.comap (i₁ ≫ pullback.fst (pullback.snd c t) pt)).IsInvertible := by
  let φ := fibreIso c t pt (pt ≫ t) rfl
  have hpr : pullback.fst (pullback.snd c t) pt =
      φ.hom ≫ baseChangeSnd c (⟨pt, rfl⟩ : SchemeHomOver (pt ≫ t) t) :=
    (fibreIso_hom_baseChangeSnd c t pt (pt ≫ t) rfl).symm
  have hε1 : ((sectionIdeal c ε t) ^ r).comap (pullback.fst (pullback.snd c t) pt)
      = ((sectionIdeal c ε (pt ≫ t)) ^ r).comap φ.hom := by
    rw [hpr, Scheme.IdealSheafData.comap_comp, comap_pow, sectionIdeal_comap, comap_pow]
  have hKε :
      (((sectionIdeal c ε t) ^ r).comap (pullback.fst (pullback.snd c t) pt)).IsInvertible := by
    rw [hε1]
    exact
      ((isInvertible_sectionIdeal_of_range_subset
        c ε U hεU (pt ≫ t)).pow r).comap_of_isOpenImmersion _
  have hD1 : D.I.comap (pullback.fst (pullback.snd c t) pt) =
      (D.pullbackAlong pt rfl).I.comap φ.hom := by
    rw [hpr, Scheme.IdealSheafData.comap_comp]
    rfl
  have hKD : (D.I.comap (pullback.fst (pullback.snd c t) pt)).IsInvertible := by
    rw [hD1]
    exact
      ((D.pullbackAlong pt rfl).isInvertible_I_of_supportedIn
        U (hDU.pullbackAlong pt rfl)).comap_of_isOpenImmersion _
  have : IsClosedImmersion (rigSection c t ε) := by
    have : IsClosedImmersion (rigSection c t ε ≫ pullback.snd c t) := by
      rw [rigSection, pullback.lift_snd]; infer_instance
    exact .of_comp (rigSection c t ε) (pullback.snd c t)
  have hsuppε : ∀ y : ↥(pullback (pullback.snd c t) pt),
      (pullback.fst (pullback.snd c t) pt).base y ∈ ((sectionIdeal c ε t) ^ r).support →
        y ∈ W₁ := by
    intro y hy
    apply hε y
    rcases Nat.eq_zero_or_pos r with hr | hr
    · subst hr
      rw [pow_zero, Scheme.IdealSheafData.one_eq_top, Scheme.IdealSheafData.support_top] at hy
      exact absurd hy (fun h => h)
    · have hy' : (pullback.fst (pullback.snd c t) pt).base y ∈
        ((sectionIdeal c ε t).support : Set ↥(pullback c t)) := by
        rw [Scheme.IdealSheafData.support_pow _ _ hr.ne'] at hy; exact hy
      change _ ∈ ((rigSection c t ε).ker.support : Set ↥(pullback c t)) at hy'
      rwa [Scheme.Hom.support_ker,
        (rigSection c t ε).isClosedEmbedding.isClosed_range.closure_eq] at hy'
  exact ⟨isInvertible_comap_line c t pt i₁ W₁ _ hKε hsuppε,
    isInvertible_comap_line c t pt i₁ W₁ _ hKD hD⟩

end
end JacobianVarieties.Picard.Proofs.OpenSectionIntersection
end ProofImplementation

attribute [-instance]
  AlgebraicGeometry.RelEffCartierDiv.isIso_subschemeIota_snd_of_degree_one
  AlgebraicGeometry.isIso_ker_graphOver_subschemeIota_snd
  AlgebraicGeometry.isClosedImmersion_graphOver
  AlgebraicGeometry.RelEffCartierDiv.isClosedImmersion_subschemeι_resProdMap
  AlgebraicGeometry.RelEffCartierDiv.isOpenImmersion_resProdMap
attribute [-simp]
  AlgebraicGeometry.graphOver_fst_assoc
  AlgebraicGeometry.RelEffCartierDiv.toPoint_comp
  AlgebraicGeometry.RelEffCartierDiv.toPoint_comp_assoc
  AlgebraicGeometry.graphOver_fst
  AlgebraicGeometry.RelEffCartierDiv.ofPoint_I
  AlgebraicGeometry.graphOver_snd
  AlgebraicGeometry.graphOver_snd_assoc
  AlgebraicGeometry.RelEffCartierDiv.restrictAlong_extendAlong
  AlgebraicGeometry.RelEffCartierDiv.extendAlong_I
  AlgebraicGeometry.RelEffCartierDiv.resProdMap_snd
  AlgebraicGeometry.RelEffCartierDiv.restrictAlong_I
  AlgebraicGeometry.RelEffCartierDiv.extendAlong_restrictAlong
  AlgebraicGeometry.RelEffCartierDiv.resProdMap_fst_assoc
  AlgebraicGeometry.RelEffCartierDiv.resProdMap_snd_assoc
  AlgebraicGeometry.RelEffCartierDiv.resProdMap_fst
