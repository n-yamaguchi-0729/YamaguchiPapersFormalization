/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Purity.RetrocompactSectionExtension
import Nyll.SchemeTheory.FiniteEtale.Basic
import Nyll.SchemeTheory.FiniteEtale.DensePullback
import Nyll.SchemeTheory.WeilRestriction.FiniteEtale
import Nyll.SchemeTheory.WeilRestriction.Sheaf
import Mathlib.CategoryTheory.Functor.FullyFaithful
import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
import Mathlib.CategoryTheory.Yoneda
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact

/-!
# Full faithfulness over a retrocompact dense open

The finite etale internal Hom turns lifting a morphism into extending a
section. The constructed global extension applies exactly to the original
hypotheses of Stacks 0BSA: retrocompactness, closed complement points, and
connected punctured strict stalks. The ambient scheme is arbitrary.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open EtaleFundamentalGroups.StrictHenselian
open scoped MonoidalCategory

namespace AlgebraicGeometry.FiniteEtale

/-- Original retrocompact local connectedness criterion for restriction
of finite etale covers. -/
@[stacks 0BSA]
def denseOpenPullbackFullyFaithful_of_retrocompact_closed_complement
    {S : Scheme.{u}}
    (U : S.Opens) [QuasiCompact U.ι] (hU : Dense (U : Set S))
    (hclosed : ∀ x : S, x ∉ U → IsClosed ({x} : Set S))
    (Ω : S → Type u) [∀ x : S, Field (Ω x)] [∀ x : S, IsSepClosed (Ω x)]
    (φ : ∀ x : S, S.presheaf.stalk x →+* Ω x) [∀ x : S, IsLocalHom (φ x)]
    (hconn : ∀ x : S, x ∉ U → ConnectedSpace (Scheme.puncturedSpectrum
      (geometricStalk (Spec.map (CommRingCat.ofHom (φ x)))))) :
    (FiniteEtale.pullback U.ι).FullyFaithful := by
  let j : U.toScheme ⟶ S := U.ι
  let F := FiniteEtale.pullback j
  have hfull : F.Full := by
    constructor
    intro A B v
    let v₀ : Limits.pullback A.hom j ⟶ Limits.pullback B.hom j := v.left
    have hv₀ : v₀ ≫ pullback.snd B.hom j = pullback.snd A.hom j :=
      MorphismProperty.Over.w v
    let swap : Limits.pullback j A.hom ≅ Limits.pullback A.hom j := pullbackSymmetry j A.hom
    let m₀ : Limits.pullback j A.hom ⟶ B.left :=
      swap.hom ≫ v₀ ≫ pullback.fst B.hom j
    have hm₀ : m₀ ≫ B.hom = pullback.fst j A.hom ≫ j := by
      change (swap.hom ≫ v₀ ≫ pullback.fst B.hom j) ≫ B.hom = _
      rw [Category.assoc, Category.assoc, pullback.condition,
        ← Category.assoc v₀, hv₀, ← Category.assoc,
        pullbackSymmetry_hom_comp_snd]
    let m : Over.mk j ⊗ A.toComma ⟶ B.toComma := Over.homMk m₀ hm₀
    let W : FiniteEtale S :=
      SchemeTheory.WeilRestriction.finiteEtaleInternalHomRepresenter S A B
    let hW : (SchemeTheory.WeilRestriction.relativeInternalHomFunctor
        A.toComma B.toComma).RepresentableBy W.toComma :=
      SchemeTheory.WeilRestriction.finiteEtaleInternalHomRepresentable S A B
    let aU : Over.mk j ⟶ W.toComma := hW.homEquiv.symm m
    let aU₀ : U.toScheme ⟶ W.left := aU.left
    have haU : aU₀ ≫ W.hom = j := Over.w aU
    obtain ⟨t, ht⟩ := exists_section_of_retrocompact_closed_complement
      U hU hclosed Ω φ hconn W.hom aU₀ haU
    let aS : Over.mk (𝟙 S) ⟶ W.toComma := Over.homMk t ht.1
    let ι : Over.mk j ⟶ Over.mk (𝟙 S) := Over.homMk j (Category.comp_id j)
    have hι : ι ≫ aS = aU := Over.OverMorphism.ext ht.2
    let n : Over.mk (𝟙 S) ⊗ A.toComma ⟶ B.toComma := hW.homEquiv aS
    have hnatural : (ι ▷ A.toComma) ≫ n = m := by
      calc
        (ι ▷ A.toComma) ≫ n = hW.homEquiv (ι ≫ aS) :=
          (hW.homEquiv_comp ι aS).symm
        _ = hW.homEquiv aU := congrArg hW.homEquiv hι
        _ = m := hW.homEquiv.apply_symm_apply m
    let n₀ : Limits.pullback (𝟙 S) A.hom ⟶ B.left := n.left
    have hn₀ : n₀ ≫ B.hom = pullback.fst (𝟙 S) A.hom := by
      have h : n₀ ≫ B.hom = pullback.fst (𝟙 S) A.hom ≫ 𝟙 S := Over.w n
      exact h.trans (Category.comp_id _)
    let z : A.left ⟶ Limits.pullback (𝟙 S) A.hom :=
      pullback.lift A.hom (𝟙 _) (by rw [Category.comp_id, Category.id_comp])
    have hzfst : z ≫ pullback.fst (𝟙 S) A.hom = A.hom := pullback.lift_fst _ _ _
    have hzsnd : z ≫ pullback.snd (𝟙 S) A.hom = 𝟙 _ := pullback.lift_snd _ _ _
    let g₀ : A.left ⟶ B.left := z ≫ n₀
    have hg₀ : g₀ ≫ B.hom = A.hom := by
      change (z ≫ n₀) ≫ B.hom = A.hom
      rw [Category.assoc, hn₀, hzfst]
    let k : Limits.pullback j A.hom ⟶ Limits.pullback (𝟙 S) A.hom := (ι ▷ A.toComma).left
    have hkfst : k ≫ pullback.fst (𝟙 S) A.hom = pullback.fst j A.hom ≫ j :=
      Over.whiskerRight_left_fst ι
    have hksnd : k ≫ pullback.snd (𝟙 S) A.hom = pullback.snd j A.hom :=
      Over.whiskerRight_left_snd ι
    have hk : k = pullback.snd j A.hom ≫ z := by
      apply pullback.hom_ext
      · rw [hkfst, Category.assoc, hzfst]
        exact pullback.condition
      · rw [hksnd, Category.assoc, hzsnd]
        exact (Category.comp_id (pullback.snd j A.hom)).symm
    have hkn : k ≫ n₀ = m₀ :=
      congrArg (fun a : Over.mk j ⊗ A.toComma ⟶ B.toComma => a.left) hnatural
    have hrestrict : pullback.fst A.hom j ≫ g₀ = v₀ ≫ pullback.fst B.hom j := by
      apply (cancel_epi swap.hom).mp
      rw [← Category.assoc swap.hom, pullbackSymmetry_hom_comp_fst]
      change pullback.snd j A.hom ≫ (z ≫ n₀) = m₀
      rw [← Category.assoc, ← hk]
      exact hkn
    let g : A ⟶ B := MorphismProperty.Over.homMk g₀ hg₀
    refine ⟨g, ?_⟩
    apply MorphismProperty.Over.Hom.ext
    change pullback.lift (pullback.fst A.hom j ≫ g₀) (pullback.snd A.hom j) _ = v₀
    apply pullback.hom_ext
    · exact (pullback.lift_fst _ _ _).trans hrestrict
    · exact (pullback.lift_snd _ _ _).trans hv₀.symm
  have : IsDominant j := Opens.isDominant_ι hU
  have : F.Faithful := pullback_faithful_of_isDominant j
  exact Functor.FullyFaithful.ofFullyFaithful F

end AlgebraicGeometry.FiniteEtale
