/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Purity.PuncturedSpectrumCechTriple
import Mathlib.AlgebraicGeometry.RelativeGluing

/-!
# A directed principal-open refinement of a punctured spectrum

The nonempty finite subsets of a chosen finite generating set, ordered by
reverse inclusion, index the principal opens obtained by inverting the product
of the selected generators.  Singleton subsets recover the original cover,
while union represents intersection.  This makes the refinement locally
directed and suitable as the base cover of relative gluing data.
-/

noncomputable section

open CategoryTheory Limits IsLocalRing TopologicalSpace
open scoped BigOperators

namespace AlgebraicGeometry.Scheme

universe u

variable (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

/-- Nonempty finite subsets of the chosen generators, ordered by reverse
inclusion.  Thus a morphism of indices points from a smaller principal open to
a larger one. -/
abbrev puncturedSpectrumRefinementIndex :=
  OrderDual
    {s : Finset (puncturedSpectrumGeneratorIndex R) // s.Nonempty}

/-- The index corresponding to one member of the original principal cover. -/
def puncturedSpectrumRefinementSingleton
    (i : puncturedSpectrumGeneratorIndex R) :
    puncturedSpectrumRefinementIndex R :=
  ⟨{i}, by simp⟩

/-- Union is a common lower bound for the reverse-inclusion order. -/
def puncturedSpectrumRefinementUnion
    (s t : puncturedSpectrumRefinementIndex R) :
    puncturedSpectrumRefinementIndex R := by
  classical
  exact ⟨s.1 ∪ t.1, s.2.inl⟩

omit [IsNoetherianRing R] in
theorem puncturedSpectrumRefinementUnion_le_left
    (s t : puncturedSpectrumRefinementIndex R) :
    puncturedSpectrumRefinementUnion R s t ≤ s := by
  classical
  exact Finset.subset_union_left

omit [IsNoetherianRing R] in
theorem puncturedSpectrumRefinementUnion_le_right
    (s t : puncturedSpectrumRefinementIndex R) :
    puncturedSpectrumRefinementUnion R s t ≤ t := by
  classical
  exact Finset.subset_union_right

/-- The product of the generators selected by an index. -/
def puncturedSpectrumGeneratorProduct
    (s : puncturedSpectrumRefinementIndex R) : R :=
  ∏ i ∈ s.1, puncturedSpectrumGenerator R i

/-- The ambient principal open belonging to a finite generator product. -/
def puncturedSpectrumAmbientRefinementOpen
    (s : puncturedSpectrumRefinementIndex R) :
    (Spec (.of R)).Opens :=
  PrimeSpectrum.basicOpen (puncturedSpectrumGeneratorProduct R s)

omit [IsNoetherianRing R] in
theorem mem_puncturedSpectrumAmbientRefinementOpen_iff
    (s : puncturedSpectrumRefinementIndex R) (x : Spec (.of R)) :
    x ∈ puncturedSpectrumAmbientRefinementOpen R s ↔
      ∀ i ∈ s.1, puncturedSpectrumGenerator R i ∉ x.asIdeal := by
  let : x.asIdeal.IsPrime := x.isPrime
  change (∏ i ∈ s.1, puncturedSpectrumGenerator R i) ∉ x.asIdeal ↔ _
  rw [Ideal.IsPrime.prod_mem_iff]
  simp only [not_exists, not_and]

omit [IsNoetherianRing R] in
theorem puncturedSpectrumAmbientRefinementOpen_singleton
    (i : puncturedSpectrumGeneratorIndex R) :
    puncturedSpectrumAmbientRefinementOpen R
        (puncturedSpectrumRefinementSingleton R i) =
      puncturedSpectrumAmbientBasicOpen R i := by
  simp [puncturedSpectrumAmbientRefinementOpen,
    puncturedSpectrumGeneratorProduct, puncturedSpectrumRefinementSingleton,
    puncturedSpectrumAmbientBasicOpen]
  rfl

omit [IsNoetherianRing R] in
theorem puncturedSpectrumAmbientRefinementOpen_union
    (s t : puncturedSpectrumRefinementIndex R) :
    puncturedSpectrumAmbientRefinementOpen R
        (puncturedSpectrumRefinementUnion R s t) =
      puncturedSpectrumAmbientRefinementOpen R s ⊓
        puncturedSpectrumAmbientRefinementOpen R t := by
  classical
  ext x
  change
    x ∈ puncturedSpectrumAmbientRefinementOpen R
        (puncturedSpectrumRefinementUnion R s t) ↔
      x ∈ puncturedSpectrumAmbientRefinementOpen R s ∧
        x ∈ puncturedSpectrumAmbientRefinementOpen R t
  rw [mem_puncturedSpectrumAmbientRefinementOpen_iff,
    mem_puncturedSpectrumAmbientRefinementOpen_iff,
    mem_puncturedSpectrumAmbientRefinementOpen_iff]
  change
    (∀ i ∈ s.1 ∪ t.1,
      puncturedSpectrumGenerator R i ∉ x.asIdeal) ↔
      (∀ i ∈ s.1, puncturedSpectrumGenerator R i ∉ x.asIdeal) ∧
        ∀ i ∈ t.1, puncturedSpectrumGenerator R i ∉ x.asIdeal
  constructor
  · intro h
    exact ⟨fun i hi ↦ h i (Finset.mem_union_left _ hi),
      fun i hi ↦ h i (Finset.mem_union_right _ hi)⟩
  · rintro ⟨hs, ht⟩ i hi
    rcases Finset.mem_union.mp hi with hi | hi
    · exact hs i hi
    · exact ht i hi

/- Every finite-product chart avoids the closed point. -/
omit [IsNoetherianRing R] in
theorem puncturedSpectrumAmbientRefinementOpen_le
    (s : puncturedSpectrumRefinementIndex R) :
    puncturedSpectrumAmbientRefinementOpen R s ≤
      puncturedSpectrumOpen R := by
  intro x hx
  change x ≠ closedPoint R
  intro hclosed
  subst x
  apply (PrimeSpectrum.mem_basicOpen _ _).mp hx
  obtain ⟨i, hi⟩ := s.2
  exact Ideal.prod_mem (maximalIdeal R) hi
    (puncturedSpectrumGenerator_mem_maximalIdeal R i)

/-- A product principal open, regarded inside the punctured spectrum. -/
def puncturedSpectrumRefinementOpen
    (s : puncturedSpectrumRefinementIndex R) :
    (puncturedSpectrum R).Opens :=
  puncturedSpectrumInclusion R ⁻¹ᵁ
    puncturedSpectrumAmbientRefinementOpen R s

omit [IsNoetherianRing R] in
theorem puncturedSpectrumRefinementOpen_singleton
    (i : puncturedSpectrumGeneratorIndex R) :
    puncturedSpectrumRefinementOpen R
        (puncturedSpectrumRefinementSingleton R i) =
      puncturedSpectrumBasicOpen R i := by
  rw [puncturedSpectrumRefinementOpen,
    puncturedSpectrumAmbientRefinementOpen_singleton]
  rfl

omit [IsNoetherianRing R] in
theorem puncturedSpectrumRefinementOpen_union
    (s t : puncturedSpectrumRefinementIndex R) :
    puncturedSpectrumRefinementOpen R
        (puncturedSpectrumRefinementUnion R s t) =
      puncturedSpectrumRefinementOpen R s ⊓
        puncturedSpectrumRefinementOpen R t := by
  rw [puncturedSpectrumRefinementOpen,
    puncturedSpectrumAmbientRefinementOpen_union,
    Scheme.Hom.preimage_inf]
  rfl

omit [IsNoetherianRing R] in
theorem puncturedSpectrumAmbientRefinementOpen_mono
    {s t : puncturedSpectrumRefinementIndex R} (hst : s ≤ t) :
    puncturedSpectrumAmbientRefinementOpen R s ≤
      puncturedSpectrumAmbientRefinementOpen R t := by
  intro x hx
  rw [mem_puncturedSpectrumAmbientRefinementOpen_iff] at hx ⊢
  intro i hi
  exact hx i (show i ∈ s.1 from hst hi)

omit [IsNoetherianRing R] in
theorem puncturedSpectrumRefinementOpen_mono
    {s t : puncturedSpectrumRefinementIndex R} (hst : s ≤ t) :
    puncturedSpectrumRefinementOpen R s ≤
      puncturedSpectrumRefinementOpen R t :=
  (puncturedSpectrumInclusion R).preimage_mono
    (puncturedSpectrumAmbientRefinementOpen_mono R hst)

/-- Every product chart is canonically the spectrum of the localization away
from the corresponding generator product. -/
def puncturedSpectrumRefinementOpenIsoSpecAway
    (s : puncturedSpectrumRefinementIndex R) :
    (puncturedSpectrumRefinementOpen R s).toScheme ≅
      Spec (.of (Localization.Away
        (puncturedSpectrumGeneratorProduct R s))) := by
  change
    (((puncturedSpectrumOpen R).ι ⁻¹ᵁ
      PrimeSpectrum.basicOpen
        (puncturedSpectrumGeneratorProduct R s)).toScheme) ≅ _
  exact Opens.isoOfLE
      (puncturedSpectrumAmbientRefinementOpen_le R s) ≪≫
    basicOpenIsoSpecAway
      (R := .of R) (puncturedSpectrumGeneratorProduct R s)

omit [IsNoetherianRing R] in
theorem puncturedSpectrumRefinementOpen_isAffine
    (s : puncturedSpectrumRefinementIndex R) :
    IsAffineOpen (puncturedSpectrumRefinementOpen R s) := by
  exact IsAffine.of_isIso
    (puncturedSpectrumRefinementOpenIsoSpecAway R s).hom

/- The product charts cover because their singleton members are the original
finite principal cover. -/
omit [IsNoetherianRing R] in
theorem puncturedSpectrumRefinementOpen_isOpenCover :
    IsOpenCover (puncturedSpectrumRefinementOpen R) := by
  change (⨆ s, puncturedSpectrumRefinementOpen R s) = ⊤
  apply top_unique
  rw [← puncturedSpectrumBasicOpen_isOpenCover R]
  refine iSup_le fun i ↦ ?_
  rw [← puncturedSpectrumRefinementOpen_singleton R i]
  exact le_iSup (puncturedSpectrumRefinementOpen R)
    (puncturedSpectrumRefinementSingleton R i)

/-- The open cover by all nonempty finite products of chosen generators. -/
abbrev puncturedSpectrumDirectedOpenCover :
    (puncturedSpectrum R).OpenCover :=
  { I₀ := puncturedSpectrumRefinementIndex R
    X := fun s ↦ (puncturedSpectrumRefinementOpen R s).toScheme
    f := fun s ↦ (puncturedSpectrumRefinementOpen R s).ι
    mem₀ := ((puncturedSpectrum R).openCoverOfIsOpenCover
      (puncturedSpectrumRefinementOpen R)
      (puncturedSpectrumRefinementOpen_isOpenCover R)).mem₀ }

/-- The inclusion associated to an inequality in the reverse-inclusion
indexing order. -/
def puncturedSpectrumRefinementTransition
    {s t : puncturedSpectrumRefinementIndex R} (hst : s ≤ t) :
    (puncturedSpectrumRefinementOpen R s).toScheme ⟶
      (puncturedSpectrumRefinementOpen R t).toScheme :=
  (puncturedSpectrum R).homOfLE
    (puncturedSpectrumRefinementOpen_mono R hst)

/-- The union chart maps to the left member of the intersection. -/
def puncturedSpectrumRefinementUnionToLeft
    (s t : puncturedSpectrumRefinementIndex R) :
    (puncturedSpectrumRefinementOpen R
      (puncturedSpectrumRefinementUnion R s t)).toScheme ⟶
        (puncturedSpectrumRefinementOpen R s).toScheme :=
  puncturedSpectrumRefinementTransition R
    (puncturedSpectrumRefinementUnion_le_left R s t)

/-- The union chart maps to the right member of the intersection. -/
def puncturedSpectrumRefinementUnionToRight
    (s t : puncturedSpectrumRefinementIndex R) :
    (puncturedSpectrumRefinementOpen R
      (puncturedSpectrumRefinementUnion R s t)).toScheme ⟶
        (puncturedSpectrumRefinementOpen R t).toScheme :=
  puncturedSpectrumRefinementTransition R
    (puncturedSpectrumRefinementUnion_le_right R s t)

omit [IsNoetherianRing R] in
@[reassoc]
theorem puncturedSpectrumRefinementTransition_comp_ι
    {s t : puncturedSpectrumRefinementIndex R} (hst : s ≤ t) :
    puncturedSpectrumRefinementTransition R hst ≫
        (puncturedSpectrumRefinementOpen R t).ι =
      (puncturedSpectrumRefinementOpen R s).ι := by
  exact Scheme.homOfLE_ι _ _

omit [IsNoetherianRing R] in
theorem puncturedSpectrumRefinementTransition_id
    (s : puncturedSpectrumRefinementIndex R) :
    puncturedSpectrumRefinementTransition R (le_refl s) = 𝟙 _ := by
  exact Scheme.homOfLE_rfl _ _

omit [IsNoetherianRing R] in
theorem puncturedSpectrumRefinementTransition_comp
    {s t v : puncturedSpectrumRefinementIndex R}
    (hst : s ≤ t) (htv : t ≤ v) :
    puncturedSpectrumRefinementTransition R (hst.trans htv) =
      puncturedSpectrumRefinementTransition R hst ≫
        puncturedSpectrumRefinementTransition R htv := by
  exact (Scheme.homOfLE_homOfLE _ _ _).symm

omit [IsNoetherianRing R] in
theorem puncturedSpectrumRefinementUnion_maps_comm
    (s t : puncturedSpectrumRefinementIndex R) :
    puncturedSpectrumRefinementUnionToLeft R s t ≫
        (puncturedSpectrumRefinementOpen R s).ι =
      puncturedSpectrumRefinementUnionToRight R s t ≫
        (puncturedSpectrumRefinementOpen R t).ι := by
  rw [puncturedSpectrumRefinementUnionToLeft,
    puncturedSpectrumRefinementUnionToRight,
    puncturedSpectrumRefinementTransition_comp_ι,
    puncturedSpectrumRefinementTransition_comp_ι]

/- The union of two singleton indices recovers the previously constructed
pairwise overlap. -/
omit [IsNoetherianRing R] in
theorem puncturedSpectrumRefinementOpen_union_singleton
    (i j : puncturedSpectrumGeneratorIndex R) :
    puncturedSpectrumRefinementOpen R
        (puncturedSpectrumRefinementUnion R
          (puncturedSpectrumRefinementSingleton R i)
          (puncturedSpectrumRefinementSingleton R j)) =
      puncturedSpectrumOverlap R i j := by
  rw [puncturedSpectrumRefinementOpen_union,
    puncturedSpectrumRefinementOpen_singleton,
    puncturedSpectrumRefinementOpen_singleton]
  rfl

omit [IsNoetherianRing R] in
theorem puncturedSpectrumRefinementUnion_exists_pullback_lift
    (s t : puncturedSpectrumRefinementIndex R)
    (x : (pullback
      (puncturedSpectrumRefinementOpen R s).ι
      (puncturedSpectrumRefinementOpen R t).ι).carrier) :
    ∃ y : (puncturedSpectrumRefinementOpen R
        (puncturedSpectrumRefinementUnion R s t)).toScheme,
      pullback.lift
        (puncturedSpectrumRefinementTransition R
          (puncturedSpectrumRefinementUnion_le_left R s t))
        (puncturedSpectrumRefinementTransition R
          (puncturedSpectrumRefinementUnion_le_right R s t))
        (by simp only [puncturedSpectrumRefinementTransition_comp_ι]) y = x := by
  let xs := pullback.fst
    (puncturedSpectrumRefinementOpen R s).ι
    (puncturedSpectrumRefinementOpen R t).ι x
  let xt := pullback.snd
    (puncturedSpectrumRefinementOpen R s).ι
    (puncturedSpectrumRefinementOpen R t).ι x
  have hbase : xs.1 = xt.1 := by
    change
      (puncturedSpectrumRefinementOpen R s).ι xs =
        (puncturedSpectrumRefinementOpen R t).ι xt
    dsimp only [xs, xt]
    have hcondition :
        pullback.fst
            (puncturedSpectrumRefinementOpen R s).ι
            (puncturedSpectrumRefinementOpen R t).ι ≫
              (puncturedSpectrumRefinementOpen R s).ι =
          pullback.snd
            (puncturedSpectrumRefinementOpen R s).ι
            (puncturedSpectrumRefinementOpen R t).ι ≫
              (puncturedSpectrumRefinementOpen R t).ι :=
      pullback.condition
    simpa only [Scheme.Hom.comp_apply] using
      congrArg (fun f :
        pullback
            (puncturedSpectrumRefinementOpen R s).ι
            (puncturedSpectrumRefinementOpen R t).ι ⟶
          puncturedSpectrum R ↦ f x) hcondition
  have hxt : xs.1 ∈ puncturedSpectrumRefinementOpen R t := by
    rw [hbase]
    exact xt.2
  let y : (puncturedSpectrumRefinementOpen R
      (puncturedSpectrumRefinementUnion R s t)).toScheme :=
    ⟨xs.1, by
      rw [puncturedSpectrumRefinementOpen_union]
      exact ⟨xs.2, hxt⟩⟩
  refine ⟨y, ?_⟩
  apply ((pullback.fst
    (puncturedSpectrumRefinementOpen R s).ι
    (puncturedSpectrumRefinementOpen R t).ι) ≫
      (puncturedSpectrumRefinementOpen R s).ι).isOpenEmbedding.injective
  rw [← Scheme.Hom.comp_apply, pullback.lift_fst_assoc,
    puncturedSpectrumRefinementTransition_comp_ι]
  rfl

noncomputable instance puncturedSpectrumDirectedOpenCover_locallyDirected :
    (puncturedSpectrumDirectedOpenCover R).LocallyDirected where
  trans {s t} hst :=
    puncturedSpectrumRefinementTransition R (leOfHom hst)
  trans_id s := by
    rw [← cancel_mono
      (puncturedSpectrumRefinementOpen R s).ι]
    simp only [puncturedSpectrumRefinementTransition_comp_ι,
      Category.id_comp]
  trans_comp {s t v} hst htv := by
    rw [← cancel_mono
      (puncturedSpectrumRefinementOpen R v).ι]
    simp only [Category.assoc,
      puncturedSpectrumRefinementTransition_comp_ι]
  w {s t} hst := by
    exact puncturedSpectrumRefinementTransition_comp_ι R (leOfHom hst)
  directed {s t} x := by
    let k := puncturedSpectrumRefinementUnion R s t
    let hks : k ⟶ s := homOfLE
      (puncturedSpectrumRefinementUnion_le_left R s t)
    let hkt : k ⟶ t := homOfLE
      (puncturedSpectrumRefinementUnion_le_right R s t)
    refine ⟨k, hks, hkt, ?_⟩
    simpa only [k, hks, hkt] using
      puncturedSpectrumRefinementUnion_exists_pullback_lift R s t x
  property_trans {s t} hst := by
    dsimp only [puncturedSpectrumRefinementTransition]
    infer_instance

theorem puncturedSpectrumDirectedOpenCover_index_finite :
    Finite (puncturedSpectrumDirectedOpenCover R).I₀ := by
  infer_instance

omit [IsNoetherianRing R] in
theorem puncturedSpectrumDirectedOpenCover_chart_isAffine
    (s : (puncturedSpectrumDirectedOpenCover R).I₀) :
    IsAffine ((puncturedSpectrumDirectedOpenCover R).X s) := by
  exact puncturedSpectrumRefinementOpen_isAffine R s

omit [IsNoetherianRing R] in
@[simp]
theorem puncturedSpectrumDirectedOpenCover_trans
    {s t : (puncturedSpectrumDirectedOpenCover R).I₀} (hst : s ≤ t) :
    (puncturedSpectrumDirectedOpenCover R).trans (homOfLE hst) =
      puncturedSpectrumRefinementTransition R hst := rfl

omit [IsNoetherianRing R] in
@[reassoc]
theorem puncturedSpectrumDirectedOpenCover_trans_comp_ι
    {s t : (puncturedSpectrumDirectedOpenCover R).I₀}
    (hst : s ⟶ t) :
    (puncturedSpectrumDirectedOpenCover R).trans hst ≫
        (puncturedSpectrumRefinementOpen R t).ι =
      (puncturedSpectrumRefinementOpen R s).ι := by
  exact (puncturedSpectrumDirectedOpenCover R).trans_map hst

/-- The canonical cartesian diagram of the base charts, expressed in the
exact format consumed by relative gluing.  This contains no descent or
effectivity hypothesis: its natural transformation is the identity. -/
def puncturedSpectrumDirectedOpenCoverBaseRelativeGluingData :
    Cover.RelativeGluingData (puncturedSpectrumDirectedOpenCover R) where
  functor :=
    (puncturedSpectrumDirectedOpenCover R).functorOfLocallyDirected
  natTrans := 𝟙 _
  equifibered := NatTrans.Equifibered.of_isIso _

end AlgebraicGeometry.Scheme

end
