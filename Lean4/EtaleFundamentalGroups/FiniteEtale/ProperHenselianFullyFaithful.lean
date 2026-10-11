/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import AlgebraicCurves.Geometry.Schemes.exists_section_of_isFinite_of_etale_of_isProper_of_henselianLocalRing_of_isNoetherianRing
import SchemeTheory.FiniteEtale.Basic
import SchemeTheory.FiniteEtale.ProperClosedFiberFaithful
import SchemeTheory.WeilRestriction.FiniteEtale
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.CategoryTheory.Functor.FullyFaithful
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
import Mathlib.CategoryTheory.Yoneda

/-!
# Full faithfulness over a Noetherian henselian local base

This is the full-faithfulness part of the proper henselian-local comparison,
with a Noetherian hypothesis. It does not assert essential surjectivity or
the unrestricted statement of Stacks 0A48.

Fullness uses the existing finite étale internal Hom and henselian section
lift. Faithfulness is supplied by the arbitrary-local proper closed-fibre
comparison. The proper morphism is not assumed flat.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory

namespace AlgebraicGeometry.FiniteEtale

/-- Henselian lifting of sections of the actual finite étale internal Hom
makes the canonical closed-fibre pullback full over a Noetherian henselian local ring. -/
theorem pullback_full_closedFiber_of_isProper_of_henselianLocalRing_of_isNoetherianRing
    {R : Type u} [CommRing R] [IsNoetherianRing R] [HenselianLocalRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [IsProper f] :
    (FiniteEtale.pullback
      (pullback.fst f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))))).Full where
  map_surjective {A B} φ := by
    let i := pullback.fst f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))
    let U : Over X := A.toComma
    let V : Over X := B.toComma
    let T : Over X := Over.mk i
    let T₁ : Over X := Over.mk (𝟙 X)
    let W : FiniteEtale X :=
      SchemeTheory.WeilRestriction.finiteEtaleInternalHomRepresenter X A B
    let e : (SchemeTheory.WeilRestriction.relativeInternalHomFunctor U V).RepresentableBy
        W.toComma := SchemeTheory.WeilRestriction.finiteEtaleInternalHomRepresentable X A B
    let pA : U.left ⟶ X := U.hom
    let pB : V.left ⟶ X := V.hom
    let φ₀ : Limits.pullback pA i ⟶ Limits.pullback pB i := φ.left
    let q : Limits.pullback pA i ≅ Limits.pullback i pA := pullbackSymmetry pA i
    have hφ : φ₀ ≫ pullback.snd pB i = pullback.snd pA i :=
      MorphismProperty.Over.w φ
    have hφB : (φ₀ ≫ pullback.fst pB i) ≫ pB = pullback.snd pA i ≫ i := by
      rw [Category.assoc, pullback.condition, ← Category.assoc, hφ]
    have hc₀ : (q.inv ≫ φ₀ ≫ pullback.fst pB i) ≫ pB =
        pullback.fst i pA ≫ i := by
      rw [Category.assoc, hφB, ← Category.assoc, pullbackSymmetry_inv_comp_snd]
    let c₀ : T ⊗ U ⟶ V := Over.homMk
      (q.inv ≫ φ₀ ≫ pullback.fst pB i) hc₀
    let s₀ : T ⟶ W.toComma := e.homEquiv.symm c₀
    obtain ⟨s, hs, hsi⟩ :=
      exists_section_of_isFinite_of_etale_of_isProper_of_henselianLocalRing_of_isNoetherianRing
        f W.hom s₀.left s₀.w
    let σ : T₁ ⟶ W.toComma := Over.homMk s hs
    let d : T ⟶ T₁ := Over.homMk i (Category.comp_id i)
    have hd : d ≫ σ = s₀ := CategoryTheory.Over.OverMorphism.ext hsi
    let c : T₁ ⊗ U ⟶ V := e.homEquiv σ
    have hn : e.homEquiv (d ≫ σ) = (d ▷ U) ≫ c := e.homEquiv_comp d σ
    have heq : e.homEquiv (d ≫ σ) = e.homEquiv s₀ :=
      congrArg (fun z : T ⟶ W.toComma ↦ e.homEquiv z) hd
    have hc : (d ▷ U) ≫ c = c₀ :=
      hn.symm.trans (heq.trans (e.homEquiv.apply_symm_apply c₀))
    let a : U ⟶ V := (λ_ U).inv ≫ c
    have ht : pullback.fst pA i ≫ (λ_ U).inv.left =
        q.hom ≫ (d ▷ U).left := by
      let l : U.left ⟶ Limits.pullback (𝟙 X) pA := (λ_ U).inv.left
      let k : Limits.pullback i pA ⟶ Limits.pullback (𝟙 X) pA := (d ▷ U).left
      have hl₁ : l ≫ pullback.fst (𝟙 X) pA = pA :=
        Over.leftUnitor_inv_left_fst U
      have hl₂ : l ≫ pullback.snd (𝟙 X) pA = 𝟙 U.left :=
        Over.leftUnitor_inv_left_snd U
      have hk₁ : k ≫ pullback.fst (𝟙 X) pA = pullback.fst i pA ≫ i :=
        Over.whiskerRight_left_fst (R := U) d
      have hk₂ : k ≫ pullback.snd (𝟙 X) pA = pullback.snd i pA :=
        Over.whiskerRight_left_snd (R := U) d
      have hq₁ : q.hom ≫ pullback.fst i pA = pullback.snd pA i :=
        pullbackSymmetry_hom_comp_fst pA i
      have hq₂ : q.hom ≫ pullback.snd i pA = pullback.fst pA i :=
        pullbackSymmetry_hom_comp_snd pA i
      change pullback.fst pA i ≫ l = q.hom ≫ k
      apply pullback.hom_ext
      · rw [Category.assoc, hl₁, Category.assoc, hk₁, ← Category.assoc, hq₁]
        exact (pullback.condition :
          pullback.fst pA i ≫ pA = pullback.snd pA i ≫ i)
      · rw [Category.assoc, hl₂, Category.comp_id, Category.assoc, hk₂, hq₂]
    have ha : pullback.fst pA i ≫ a.left = φ₀ ≫ pullback.fst pB i := by
      calc
        pullback.fst pA i ≫ a.left =
            (pullback.fst pA i ≫ (λ_ U).inv.left) ≫ c.left :=
          (Category.assoc _ _ _).symm
        _ = q.hom ≫ ((d ▷ U) ≫ c).left := by
          rw [ht, Over.comp_left, Category.assoc]
        _ = q.hom ≫ c₀.left := congrArg (fun z : T ⊗ U ⟶ V ↦ q.hom ≫ z.left) hc
        _ = φ₀ ≫ pullback.fst pB i := by
          change q.hom ≫ q.inv ≫ φ₀ ≫ pullback.fst pB i =
            φ₀ ≫ pullback.fst pB i
          rw [Iso.hom_inv_id_assoc]
    let aFE : A ⟶ B := MorphismProperty.Over.homMk a.left a.w
    let m : Limits.pullback pA i ⟶ Limits.pullback pB i :=
      ((FiniteEtale.pullback i).map aFE).left
    have hm₁ : m ≫ pullback.fst pB i = pullback.fst pA i ≫ a.left :=
      pullback.lift_fst _ _ _
    have hm₂ : m ≫ pullback.snd pB i = pullback.snd pA i :=
      pullback.lift_snd _ _ _
    refine ⟨aFE, ?_⟩
    apply MorphismProperty.Over.Hom.ext
    change m = φ₀
    exact pullback.hom_ext (hm₁.trans ha) (hm₂.trans hφ.symm)

/-- The canonical finite étale pullback is fully faithful for a proper scheme
over a Noetherian henselian local ring. This is an intermediate comparison,
not the unrestricted proper henselian equivalence. -/
def pullbackFullyFaithful_closedFiber_of_isProper_of_henselianLocalRing_of_isNoetherianRing
    {R : Type u} [CommRing R] [IsNoetherianRing R] [HenselianLocalRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [IsProper f] :
    (FiniteEtale.pullback
      (pullback.fst f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))))).FullyFaithful := by
  let i := pullback.fst f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))
  let hfull : (FiniteEtale.pullback i).Full :=
    pullback_full_closedFiber_of_isProper_of_henselianLocalRing_of_isNoetherianRing f
  let hfaithful : (FiniteEtale.pullback i).Faithful :=
    pullback_faithful_closedFiber_of_isProper f
  exact Functor.FullyFaithful.ofFullyFaithful (FiniteEtale.pullback i)

end AlgebraicGeometry.FiniteEtale
