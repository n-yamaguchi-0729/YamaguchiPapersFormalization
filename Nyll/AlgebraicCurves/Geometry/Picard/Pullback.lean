/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicGeometry_RelPicardPullback.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Geometry.Picard.Functor
import Nyll.AlgebraicCurves.Geometry.Picard.SubPicCondition
import Nyll.AlgebraicCurves.Geometry.Picard.AlgEquivZeroCut
import Nyll.AlgebraicCurves.Geometry.AbelianSchemes.AbelianSchemePropertyBundle

/-!
# Pullback
-/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

noncomputable section

namespace AlgebraicGeometry.RelPicard

variable {R : Type u} [CommRing R] {C C' : Scheme.{u}}
  {c : C ⟶ Spec (CommRingCat.of R)} {c' : C' ⟶ Spec (CommRingCat.of R)}
  {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c} {ε' : SchemeHomOver (𝟙 (Spec (CommRingCat.of
    R))) c'}
  (f : C' ⟶ C) (hf : f ≫ c = c') (hε : ε'.1 ≫ f = ε.1)

/-- The base-changed morphism induced by a morphism of curves over the common base. -/
def curveChange {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) : pullback c' t ⟶ pullback c t :=
  pullback.map c' t c t f (𝟙 T) (𝟙 _) (by rw [Category.comp_id, hf]) (by simp)

include hε in
theorem rigSection_curveChange {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) :
    rigSection c' t ε' ≫ curveChange f hf t = rigSection c t ε := by
  apply pullback.hom_ext
  · simp only [rigSection, curveChange, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc,
      hε]
  · simp only [rigSection, curveChange, Category.assoc, pullback.lift_snd, Category.comp_id]

theorem curveChange_baseChangeSnd {T T' : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    {t' : T' ⟶ Spec (CommRingCat.of R)} (ψ : SchemeHomOver t' t) :
    curveChange f hf t' ≫ baseChangeSnd c ψ = baseChangeSnd c' ψ ≫ curveChange f hf t := by
  apply pullback.hom_ext <;>
    simp only [curveChange, baseChangeSnd, Category.assoc, pullback.lift_fst,
      pullback.lift_fst_assoc,
      pullback.lift_snd, pullback.lift_snd_assoc, Category.comp_id]

theorem curveChange_snd {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) :
    curveChange f hf t ≫ pullback.snd c t = pullback.snd c' t := by
  simp only [curveChange, pullback.lift_snd, Category.comp_id]

/-- Pull back the line bundle and its rigidification along a morphism of pointed curves. -/
def RigidifiedLineBundle.pullbackCurve {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    (M : RigidifiedLineBundle c ε t) : RigidifiedLineBundle c' ε' t where
  L := (Scheme.Modules.pullback (curveChange f hf t)).obj M.L
  isInvertible := M.isInvertible.pullback _
  rigidified := ⟨(Scheme.Modules.pullbackComp _ _).app M.L ≪≫
    (Scheme.Modules.pullbackCongr (rigSection_curveChange f hf hε t)).app M.L ≪≫ M.rigidified.some⟩

theorem RigidifiedLineBundle.pullbackCurve_congr {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    {M M' : RigidifiedLineBundle c ε t} (h : Nonempty (M.L ≅ M'.L)) :
    Nonempty ((M.pullbackCurve f hf hε).L ≅ (M'.pullbackCurve f hf hε).L) :=
  ⟨(Scheme.Modules.pullback _).mapIso h.some⟩

/-- The canonical comparison between pullback of the curve and pullback along a base morphism. -/
def RigidifiedLineBundle.pullbackCurvePullbackAlongIso {T T' : Scheme.{u}} {t : T ⟶ Spec
  (CommRingCat.of R)}
    {t' : T' ⟶ Spec (CommRingCat.of R)} (M : RigidifiedLineBundle c ε t) (ψ : SchemeHomOver t' t) :
    ((M.pullbackCurve f hf hε).pullbackAlong ψ).L ≅ ((M.pullbackAlong ψ).pullbackCurve f hf hε).L :=
  (Scheme.Modules.pullbackComp _ _).app M.L ≪≫
    (Scheme.Modules.pullbackCongr (curveChange_baseChangeSnd f hf ψ).symm).app M.L ≪≫
    ((Scheme.Modules.pullbackComp _ _).app M.L).symm

/-- The comparison between successive pullbacks and pullback along the composite base morphism. -/
def RigidifiedLineBundle.pullbackAlongPullbackAlongIso' {T T' T'' : Scheme.{u}} {t : T ⟶ Spec
  (CommRingCat.of R)}
    {t' : T' ⟶ Spec (CommRingCat.of R)} {t'' : T'' ⟶ Spec (CommRingCat.of R)}
    (M : RigidifiedLineBundle c ε t) (ψ : SchemeHomOver t' t) (φ : SchemeHomOver t'' t') :
    ((M.pullbackAlong ψ).pullbackAlong φ).L ≅ (M.pullbackAlong (postComp ψ φ)).L :=
  (Scheme.Modules.pullbackComp _ _).app M.L ≪≫
    (Scheme.Modules.pullbackCongr (baseChangeSnd_comp c ψ φ)).app M.L

/-- The canonical identification of the pulled-back unit line bundle with the unit line bundle. -/
def RigidifiedLineBundle.unitPullbackCurveIso {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) :
    ((RigidifiedLineBundle.unit (c := c) (ε := ε) t).pullbackCurve f hf hε).L ≅
      (RigidifiedLineBundle.unit (c := c') (ε := ε') t).L :=
  Scheme.Modules.pullbackUnitIso _

include hf in
theorem FibrewiseAlgEquivZero.pullbackCurve {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    {M : RigidifiedLineBundle c ε t} (hM : FibrewiseAlgEquivZero M) :
    FibrewiseAlgEquivZero (M.pullbackCurve f hf hε) := by
  intro k _ _ s
  let e : Limits.pullback (pullback.snd c' t) s ⟶ Limits.pullback (pullback.snd c t) s :=
    pullback.map _ _ _ _ (curveChange f hf t) (𝟙 _) (𝟙 T)
      (by rw [Category.comp_id, curveChange_snd]) (by simp)
  have he : e ≫ fibreAt c t s = fibreAt c' t s := by
    simp only [e, fibreAt, pullback.lift_snd, Category.comp_id]
  have hfst : e ≫ pullback.fst (pullback.snd c t) s =
      pullback.fst (pullback.snd c' t) s ≫ curveChange f hf t := by
    simp only [e, pullback.lift_fst]
  refine IsAlgEquivZero.of_iso ?_ ((hM k s).pullback e he)
  exact (Scheme.Modules.pullbackComp _ _).app M.L ≪≫
    (Scheme.Modules.pullbackCongr hfst).app M.L ≪≫
    ((Scheme.Modules.pullbackComp _ _).app M.L).symm

end AlgebraicGeometry.RelPicard

end
