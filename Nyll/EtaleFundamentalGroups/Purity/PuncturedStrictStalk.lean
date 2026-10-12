/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.StrictHenselian.GeometricStalkPuncture
import Nyll.EtaleFundamentalGroups.StrictHenselian.GeometricStalkPuncturedSections
import Nyll.SchemeTheory.Pi1.FiniteEtale.Basic
import Nyll.SchemeTheory.FiniteEtale.DensePullback
import Nyll.SchemeTheory.LocalGeometry.PuncturedSpectrum
import Nyll.SchemeTheory.LocalGeometry.PuncturedSpectrumFlat
import Nyll.SchemeTheory.WeilRestriction.Affine
import Nyll.SchemeTheory.WeilRestriction.Sheaf
import Mathlib.CategoryTheory.Functor.FullyFaithful
import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
import Mathlib.CategoryTheory.Yoneda

/-!
# Full faithfulness from connected punctured strict henselization

For an arbitrary local ring, connectedness of its actual punctured geometric
étale stalk makes restriction to the punctured local spectrum fully faithful
on finite étale schemes. The finite étale internal Hom turns a morphism on
the puncture into a section. Actual strict-stalk fpqc descent extends that
section, and naturality of the same representer recovers the original map.

This is the original arbitrary-local-ring statement of Stacks Project 0BLQ.
The puncture need not be quasi-compact. No domain, reducedness, normality,
Noetherianity, or dimension hypothesis is imposed.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits EtaleFundamentalGroups.StrictHenselian
open scoped MonoidalCategory

namespace AlgebraicGeometry.FiniteEtale

universe u

/-- Restriction to the puncture of an arbitrary local ring is fully faithful
when the puncture of its actual strict stalk is connected. -/
@[stacks 0BLQ]
def puncturedSpectrumPullbackFullyFaithful_of_connected_geometricStalk
    {R Ω : Type u} [CommRing R] [IsLocalRing R] [Field Ω] [IsSepClosed Ω]
    (φ : R →+* Ω) [IsLocalHom φ]
    [ConnectedSpace
      (Scheme.puncturedSpectrum
        (geometricStalk
          (Spec.map (CommRingCat.ofHom φ))))] :
    (FiniteEtale.pullback (Scheme.puncturedSpectrumInclusion R)).FullyFaithful := by
  let S : Scheme.{u} := Spec (.of R)
  have : IsAffine S := inferInstanceAs (IsAffine (Spec (.of R)))
  let j : Scheme.puncturedSpectrum R ⟶ S := Scheme.puncturedSpectrumInclusion R
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
      SchemeTheory.WeilRestriction.affineFiniteEtaleInternalHomRepresenter S A B
    let hW : (SchemeTheory.WeilRestriction.relativeInternalHomFunctor
        A.toComma B.toComma).RepresentableBy W.toComma :=
      SchemeTheory.WeilRestriction.affineFiniteEtaleInternalHomRepresentable S A B
    let aU : Over.mk j ⟶ W.toComma := hW.homEquiv.symm m
    let aU₀ : Scheme.puncturedSpectrum R ⟶ W.left := aU.left
    have haU : aU₀ ≫ W.hom = j := Over.w aU
    obtain ⟨t, ht, _⟩ :=
      existsUnique_section_of_connected_geometricStalk_puncture
        φ W.hom aU₀ haU
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
  let H := geometricStalk
    (Spec.map (CommRingCat.ofHom φ))
  let π : Spec H ⟶ S := Spec.map (CommRingCat.ofHom
    (geometricStalkStructureMap φ))
  let e : Limits.pullback π j ≅ Scheme.puncturedSpectrum H :=
    geometricStalkPuncturedSpectrumPullbackIso φ
  have : Nonempty (Scheme.puncturedSpectrum R) :=
    Nonempty.map (fun x => pullback.snd π j (e.inv x))
      (inferInstance : Nonempty (Scheme.puncturedSpectrum H))
  have hdense : Dense (Scheme.puncturedSpectrumOpen R : Set S) :=
    Scheme.dense_preimage_puncturedSpectrumOpen_of_flat R (𝟙 S)
  have : IsDominant j := by
    constructor
    change Dense (Set.range (Scheme.puncturedSpectrumOpen R).ι)
    rw [Scheme.Opens.range_ι]
    exact hdense
  have : F.Faithful := pullback_faithful_of_isDominant j
  exact Functor.FullyFaithful.ofFullyFaithful F

end AlgebraicGeometry.FiniteEtale
