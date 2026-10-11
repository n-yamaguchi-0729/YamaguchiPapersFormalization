/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Inertia.NormalizationComponent
import SchemeTheory.FiniteEtale.Forget.FiniteCoproducts
import SchemeTheory.FiniteEtale.Basic
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.Normalization
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.CategoryTheory.Galois.Basic
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts

/-!
# Lifting deck transformations from normalized components

The inverse image of a normalized component is the original finite-etale
component. This supplies the passage from component preservation on the
normalization to component preservation on the cover itself.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CategoryTheory.PreGaloisCategory EtaleFundamentalGroups.Inertia

namespace EtaleFundamentalGroups.Inertia

universe u

variable {U S : Scheme.{u}}
variable {W Z : FiniteEtale U}

/-- Normalization preserves the actual decomposition into finite-etale
components, including the inverse image of each component. -/
theorem preimage_normalizationComponentInclusion_range
    (f : W.left ⟶ S) [QuasiCompact f] [QuasiSeparated f]
    (i : Z ⟶ W) [Mono i] :
    f.toNormalization ⁻¹' Set.range (normalizationComponentInclusion f i) =
      Set.range i.left := by
  obtain ⟨Z', j, ⟨hcoprod⟩⟩ :=
    PreGaloisCategory.monoInducesIsoOnDirectSummand i
  let F := FiniteEtale.forget U ⋙ Over.forget U
  have hscheme : IsColimit (BinaryCofan.mk i.left j.left) :=
    mapIsColimitOfPreservesOfIsColimit F i j hcoprod
  have hcomponents : IsCompl (Set.range i.left) (Set.range j.left) :=
    ((TopCat.binaryCofan_isColimit_iff _).mp
      ⟨mapIsColimitOfPreservesOfIsColimit Scheme.forgetToTop
        i.left j.left hscheme⟩).2.2
  let e : (i.left ≫ f).normalization ⨿ (j.left ≫ f).normalization ≅
      f.normalization := f.normalizationCoprodIso hscheme
  have hi : normalizationComponentInclusion f i = coprod.inl ≫ e.hom := by
    dsimp only [e, Scheme.Hom.normalizationCoprodIso]
    rw [coprod.inl_desc]
    rfl
  have hj : normalizationComponentInclusion f j = coprod.inr ≫ e.hom := by
    dsimp only [e, Scheme.Hom.normalizationCoprodIso]
    rw [coprod.inr_desc]
    rfl
  ext w
  constructor
  · rintro ⟨z, hz⟩
    have hw : w ∈ Set.range i.left ∪ Set.range j.left := by
      rw [show Set.range i.left ∪ Set.range j.left = Set.univ from
        hcomponents.sup_eq_top]
      exact Set.mem_univ w
    rcases hw with hw | ⟨w', rfl⟩
    · exact hw
    · exfalso
      have hjp := congrArg (fun q : Z'.left ⟶ f.normalization => q w')
        (toNormalization_normalizationComponentInclusion f j)
      simp only [Scheme.Hom.comp_apply] at hjp
      have hij := hz.trans hjp.symm
      rw [hi, hj] at hij
      change e.hom ((coprod.inl : (i.left ≫ f).normalization ⟶
          (i.left ≫ f).normalization ⨿ (j.left ≫ f).normalization) z) =
        e.hom ((coprod.inr : (j.left ≫ f).normalization ⟶
          (i.left ≫ f).normalization ⨿ (j.left ≫ f).normalization)
            ((j.left ≫ f).toNormalization w')) at hij
      exact AlgebraicGeometry.inl_ne_inr _ _ z ((j.left ≫ f).toNormalization w')
        (e.hom.isOpenEmbedding.injective hij)
  · rintro ⟨z, rfl⟩
    refine ⟨(i.left ≫ f).toNormalization z, ?_⟩
    exact congrArg (fun q : Z.left ⟶ f.normalization => q z)
      (toNormalization_normalizationComponentInclusion f i)

/-- Fixing a geometric point on a normalized component forces preservation
of the original finite-etale component, before normalization. -/
theorem range_comp_subset_of_fixes_normalized_component_geometricPoint
    (f : W.left ⟶ S) [QuasiCompact f] [QuasiSeparated f]
    (i : Z ⟶ W) [Mono i] [IsIntegral Z.left]
    {Omega : Type u} [Field Omega]
    (z : Spec (.of Omega) ⟶ (i.left ≫ f).normalization)
    (sigma : W.left ⟶ W.left) (hsigma : sigma ≫ f = f)
    (hfix : z ≫ normalizationComponentInclusion f i ≫
        normalizationEndomorphism f sigma hsigma =
      z ≫ normalizationComponentInclusion f i) :
    Set.range (i.left ≫ sigma) ⊆ Set.range i.left := by
  have hnormalized :=
    normalizationComponentInclusion_range_comp_subset_of_fixes_geometricPoint
      f i z sigma hsigma hfix
  have hmap :
      (i.left ≫ f).toNormalization ≫ normalizationComponentInclusion f i ≫
          normalizationEndomorphism f sigma hsigma =
        i.left ≫ sigma ≫ f.toNormalization := by
    rw [← Category.assoc, toNormalization_normalizationComponentInclusion,
      Category.assoc, toNormalization_normalizationEndomorphism]
  rintro w ⟨a, rfl⟩
  rw [← preimage_normalizationComponentInclusion_range f i]
  change f.toNormalization ((i.left ≫ sigma) a) ∈
    Set.range (normalizationComponentInclusion f i)
  have h := hnormalized ⟨(i.left ≫ f).toNormalization a, rfl⟩
  have heval := congrArg (fun q : Z.left ⟶ f.normalization => q a) hmap
  exact heval ▸ h

/-- A deck transformation preserving a connected component lifts to an
actual deck transformation of that component. The lift is constructed using
the open immersion of the component and the connected-object axiom. -/
theorem exists_aut_component_lift_of_preserves_range
    (i : Z ⟶ W) [Mono i] [IsConnected Z]
    (sigma : Aut W)
    (hpreserve : Set.range (i.left ≫ sigma.hom.left) ⊆ Set.range i.left) :
    ∃ tau : Aut Z, tau.hom ≫ i = i ≫ sigma.hom := by
  let : IsOpenImmersion i.left := (FiniteEtale.mono_iff U Z W i).mp inferInstance |>.1
  let l : Z.left ⟶ Z.left :=
    IsOpenImmersion.lift i.left (i.left ≫ sigma.hom.left) hpreserve
  have hl : l ≫ i.left = i.left ≫ sigma.hom.left :=
    IsOpenImmersion.lift_fac i.left (i.left ≫ sigma.hom.left) hpreserve
  have hiw : i.left ≫ W.hom = Z.hom := i.w
  have hsigmaw : sigma.hom.left ≫ W.hom = W.hom := sigma.hom.w
  have hbase : l ≫ Z.hom = Z.hom := by
    calc
      l ≫ Z.hom = l ≫ i.left ≫ W.hom := by rw [hiw]
      _ = (i.left ≫ sigma.hom.left) ≫ W.hom := by rw [← Category.assoc, hl]
      _ = Z.hom := by rw [Category.assoc, hsigmaw, hiw]
  let t : Z ⟶ Z := MorphismProperty.Over.homMk l hbase
  have ht : t ≫ i = i ≫ sigma.hom :=
    MorphismProperty.Over.Hom.ext hl
  let : Mono t := by
    constructor
    intro T a b hab
    apply (cancel_mono i).mp
    have hsig : (a ≫ i) ≫ sigma.hom = (b ≫ i) ≫ sigma.hom := by
      calc
        (a ≫ i) ≫ sigma.hom = (a ≫ t) ≫ i := by
          rw [Category.assoc, ← ht, ← Category.assoc]
        _ = (b ≫ t) ≫ i := congrArg (fun q : T ⟶ Z => q ≫ i) hab
        _ = (b ≫ i) ≫ sigma.hom := by
          rw [Category.assoc, ht, ← Category.assoc]
    have hsigmaId : sigma.hom ≫ sigma.inv = 𝟙 W := sigma.hom_inv_id
    have hcancel := congrArg (fun q : T ⟶ W => q ≫ sigma.inv) hsig
    simpa only [Category.assoc, hsigmaId, Category.comp_id] using hcancel
  let : IsIso t := IsConnected.noTrivialComponent Z t (IsConnected.notInitial (X := Z))
  exact ⟨asIso t, ht⟩

/-- Normalization of a component inclusion intertwines any commuting
endomorphisms of the actual covers. -/
theorem normalizationComponentInclusion_endomorphism
    (f : W.left ⟶ S) [QuasiCompact f] [QuasiSeparated f]
    (i : Z ⟶ W)
    (sigma : W.left ⟶ W.left) (hsigma : sigma ≫ f = f)
    (tau : Z.left ⟶ Z.left) (htau : tau ≫ i.left = i.left ≫ sigma) :
    normalizationEndomorphism (i.left ≫ f) tau
        (by rw [← Category.assoc, htau, Category.assoc, hsigma]) ≫
      normalizationComponentInclusion f i =
    normalizationComponentInclusion f i ≫ normalizationEndomorphism f sigma hsigma := by
  refine Scheme.Hom.normalization.hom_ext (i.left ≫ f)
    _ _ f.fromNormalization ?_ ?_ ?_
  · simp only [toNormalization_normalizationEndomorphism_assoc,
      toNormalization_normalizationComponentInclusion_assoc,
      toNormalization_normalizationComponentInclusion,
      toNormalization_normalizationEndomorphism]
    rw [← Category.assoc, htau, Category.assoc]
  · simp only [normalizationComponentInclusion, Category.assoc,
      Scheme.Hom.normalizationDesc_comp,
      normalizationEndomorphism_fromNormalization]
  · simp only [normalizationComponentInclusion, Category.assoc,
      normalizationEndomorphism_fromNormalization,
      Scheme.Hom.normalizationDesc_comp]

/-- A deck transformation fixing a geometric point on a normalized
component lifts to a component deck transformation fixing that very point. -/
theorem exists_aut_component_lift_of_fixes_normalized_geometricPoint
    (f : W.left ⟶ S) [QuasiCompact f] [QuasiSeparated f]
    (i : Z ⟶ W) [Mono i] [IsConnected Z] [IsIntegral Z.left]
    {Omega : Type u} [Field Omega]
    (z : Spec (.of Omega) ⟶ (i.left ≫ f).normalization)
    (sigma : Aut W) (hsigma : sigma.hom.left ≫ f = f)
    (hfix : z ≫ normalizationComponentInclusion f i ≫
        normalizationEndomorphism f sigma.hom.left hsigma =
      z ≫ normalizationComponentInclusion f i) :
    ∃ (tau : Aut Z) (htau : tau.hom ≫ i = i ≫ sigma.hom),
      z ≫ normalizationEndomorphism (i.left ≫ f) tau.hom.left (by
        have h := congrArg (fun q : Z ⟶ W => q.left) htau
        change tau.hom.left ≫ i.left = i.left ≫ sigma.hom.left at h
        rw [← Category.assoc, h, Category.assoc, hsigma]) = z := by
  obtain ⟨tau, htau⟩ := exists_aut_component_lift_of_preserves_range i sigma
    (range_comp_subset_of_fixes_normalized_component_geometricPoint
      f i z sigma.hom.left hsigma hfix)
  refine ⟨tau, htau, ?_⟩
  have htauLeft : tau.hom.left ≫ i.left = i.left ≫ sigma.hom.left :=
    congrArg (fun q : Z ⟶ W => q.left) htau
  apply (cancel_mono (normalizationComponentInclusion f i)).mp
  rw [Category.assoc,
    normalizationComponentInclusion_endomorphism f i sigma.hom.left hsigma
      tau.hom.left htauLeft]
  exact hfix

end EtaleFundamentalGroups.Inertia
