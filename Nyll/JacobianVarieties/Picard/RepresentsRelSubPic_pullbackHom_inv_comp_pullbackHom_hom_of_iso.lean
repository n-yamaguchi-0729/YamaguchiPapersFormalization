/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_pullbackHom_inv_comp_pullbackHom_hom_of_iso.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Util.WithWeakNamespace
import Mathlib.CategoryTheory.Iso
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Nyll.AlgebraicCurves.Geometry.Picard.Functor
import Nyll.JacobianVarieties.Picard.Representation
import Nyll.AlgebraicCurves.Geometry.Picard.AlgEquivZeroCut
import Nyll.AlgebraicCurves.Geometry.Picard.Pullback

import Nyll.JacobianVarieties.Picard.RepresentsRelSubPicPullback
/-!
# Pullback by inverse curve isomorphisms

Composition and identity comparisons for curve pullback show that the induced
morphisms of the represented relative Picard functors are mutually inverse.
-/

section ProofImplementation

namespace JacobianVarieties.Picard.Proofs.PullbackInverse

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open NeronModelInfra GoodReductionJacobian AlgebraicGeometry.RelPicard

universe u

namespace Sub2

variable {R : Type u} [CommRing R]

theorem classify_congr {C : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of R)}
    {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c}
    {P : SubPicCondition c ε} {D : RelativePic0Designation R c}
    (h : RepresentsRelSubPic c ε P D) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (M M' : RigidifiedLineBundle c ε t) (hM : P.P t M) (hM' : P.P t M')
    (i : Nonempty (M.L ≅ M'.L)) :
    h.classify t M hM = h.classify t M' hM' :=
  h.classify_unique t M' hM' _ ⟨(h.classify_spec t M hM).some ≪≫ i.some⟩

variable {C C' : Scheme.{u}}
  {c : C ⟶ Spec (CommRingCat.of R)} {c' : C' ⟶ Spec (CommRingCat.of R)}
  {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c}
  {ε' : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c'}

theorem curveChange_comp {C'' : Scheme.{u}} {c'' : C'' ⟶ Spec (CommRingCat.of R)}
    (f : C' ⟶ C) (hf : f ≫ c = c') (g : C'' ⟶ C') (hg : g ≫ c' = c'')
    (k : C'' ⟶ C) (hk : k ≫ c = c'') (hgf : g ≫ f = k)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) :
    curveChange (c := c') (c' := c'') g hg t ≫ curveChange (c := c) (c' := c') f hf t
      = curveChange (c := c) (c' := c'') k hk t := by
  subst hgf
  apply pullback.hom_ext <;>
    simp only [curveChange, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc,
      pullback.lift_snd,
      Category.comp_id]

theorem curveChange_id {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) :
    curveChange (c := c) (c' := c) (𝟙 C) (Category.id_comp c) t = 𝟙 _ := by
  apply pullback.hom_ext <;>
    simp only [curveChange, pullback.lift_fst, pullback.lift_snd, Category.comp_id,
      Category.id_comp]

theorem comp_eq_id (f : C' ⟶ C) (hf : f ≫ c = c') (hεf : ε'.1 ≫ f = ε.1)
    (g : C ⟶ C') (hg : g ≫ c' = c) (hεg : ε.1 ≫ g = ε'.1) (hgf : g ≫ f = 𝟙 C)
    {D : RelativePic0Designation R c} {D' : RelativePic0Designation R c'}
    (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)
    (h' : RepresentsRelSubPic c' ε' (algEquivZeroCut c' ε') D') :
    (RepresentsRelSubPic.pullbackHom f hf hεf h h').1 ≫
      (RepresentsRelSubPic.pullbackHom g hg hεg h' h).1 = 𝟙 D.P := by
  have hid : ε.1 ≫ 𝟙 C = ε.1 := Category.comp_id _
  have e1 : postComp (RepresentsRelSubPic.pullbackHom g hg hεg h' h)
      (RepresentsRelSubPic.pullbackHom f hf hεf h h')
      = RepresentsRelSubPic.pullbackHom (𝟙 C) (Category.id_comp c) hid h h := by
    apply RepresentsRelSubPic.pullbackHom_unique
    intro T t M hM
    have step1 : postComp (postComp (RepresentsRelSubPic.pullbackHom g hg hεg h' h)
        (RepresentsRelSubPic.pullbackHom f hf hεf h h')) (h.classify t M hM)
        = postComp (RepresentsRelSubPic.pullbackHom g hg hεg h' h)
          (postComp (RepresentsRelSubPic.pullbackHom f hf hεf h h') (h.classify t M hM)) :=
      Subtype.ext (Category.assoc _ _ _).symm
    have hMf : (algEquivZeroCut c' ε').P t (M.pullbackCurve f hf hεf) :=
      FibrewiseAlgEquivZero.pullbackCurve f hf hεf hM
    have eF := RepresentsRelSubPic.postComp_pullbackHom_classify f hf hεf h h' t M hM
    have eG := RepresentsRelSubPic.postComp_pullbackHom_classify g hg hεg h' h t
      (M.pullbackCurve f hf hεf) hMf
    have eC := classify_congr h t
      ((M.pullbackCurve f hf hεf).pullbackCurve g hg hεg)
      (M.pullbackCurve (𝟙 C) (Category.id_comp c) hid)
      (FibrewiseAlgEquivZero.pullbackCurve g hg hεg hMf)
      (FibrewiseAlgEquivZero.pullbackCurve (𝟙 C) (Category.id_comp c) hid hM)
      ⟨(Scheme.Modules.pullbackComp _ _).app M.L ≪≫
        (Scheme.Modules.pullbackCongr
          (curveChange_comp f hf g hg (𝟙 C) (Category.id_comp c) hgf t)).app M.L⟩
    exact step1.trans ((congrArg
      (postComp (RepresentsRelSubPic.pullbackHom g hg hεg h' h)) eF).trans (eG.trans eC))
  have e2 : (⟨𝟙 D.P, Category.id_comp _⟩ : SchemeHomOver D.toBase D.toBase)
      = RepresentsRelSubPic.pullbackHom (𝟙 C) (Category.id_comp c) hid h h := by
    apply RepresentsRelSubPic.pullbackHom_unique
    intro T t M hM
    have : postComp (⟨𝟙 D.P, Category.id_comp _⟩ : SchemeHomOver D.toBase D.toBase)
        (h.classify t M hM) = h.classify t M hM := Subtype.ext (Category.comp_id _)
    exact this.trans (classify_congr h t M
      (M.pullbackCurve (𝟙 C) (Category.id_comp c) hid) hM
      (FibrewiseAlgEquivZero.pullbackCurve (𝟙 C) (Category.id_comp c) hid hM)
      ⟨((Scheme.Modules.pullbackCongr (curveChange_id (c := c) t)).app M.L ≪≫
        (Scheme.Modules.pullbackId _).app M.L).symm⟩)
  have := congrArg Subtype.val (e1.trans e2.symm)
  exact this

end Sub2

open Sub2 renaming comp_eq_id → pullback_comp_eq_id in
with_weak_namespace _root_.AlgebraicGeometry.RelPicard.RepresentsRelSubPic
theorem pullbackHom_inv_comp_pullbackHom_hom_of_iso
    {R : Type u} [CommRing R] {C C' : Scheme.{u}}
    {c : C ⟶ Spec (CommRingCat.of R)} {c' : C' ⟶ Spec (CommRingCat.of R)}
    {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c}
    {ε' : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c'}
    (e : C ≅ C') (he : e.hom ≫ c' = c) (he' : e.inv ≫ c = c')
    (hε : ε.1 ≫ e.hom = ε'.1) (hε' : ε'.1 ≫ e.inv = ε.1)
    {D : RelativePic0Designation R c} {D' : RelativePic0Designation R c'}
    (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)
    (h' : RepresentsRelSubPic c' ε' (algEquivZeroCut c' ε') D') :
    (RepresentsRelSubPic.pullbackHom e.inv he' hε' h h').1 ≫
      (RepresentsRelSubPic.pullbackHom e.hom he hε h' h).1 = 𝟙 D.P ∧
    (RepresentsRelSubPic.pullbackHom e.hom he hε h' h).1 ≫
      (RepresentsRelSubPic.pullbackHom e.inv he' hε' h h').1 = 𝟙 D'.P :=
  ⟨pullback_comp_eq_id e.inv he' hε' e.hom he hε e.hom_inv_id h h',
    pullback_comp_eq_id e.hom he hε e.inv he' hε' e.inv_hom_id h' h⟩
end JacobianVarieties.Picard.Proofs.PullbackInverse
end ProofImplementation
