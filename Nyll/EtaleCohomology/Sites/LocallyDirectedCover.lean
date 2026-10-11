/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.WeilRestriction.CoverHypercover
import Mathlib.AlgebraicGeometry.Cover.Directed
import Mathlib.AlgebraicGeometry.Cover.Open
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Sites.Etale
import Mathlib.AlgebraicGeometry.Sites.Pretopology
import Mathlib.AlgebraicGeometry.Sites.Small
import Mathlib.CategoryTheory.Sites.Hypercover.One
import Mathlib.CategoryTheory.MorphismProperty.Comma
import Mathlib.CategoryTheory.Sites.Sieves.Presieve

/-!
# Locally directed open covers in the small étale site

An open cover of a scheme étale over the base gives a covering hypercover in
the small étale site. The overlap covers are supplied by the existing
`SchemeTheory.WeilRestriction.locallyDirectedCoverHypercover`. Every scheme
in a covering witness is étale over the base by composition, so the covering
witnesses lift to the small site.

The chosen structural maps keep local objects definitionally compatible with
local representers. This adapts the relative construction in
`SchemeTheory.WeilRestriction.CoverHypercover`; no bound on the index universe
and no separation or quasi-compactness condition on the base are needed.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u v w

namespace EtaleCohomology.Sites

variable {S : Scheme.{u}} (W : S.Etale) (𝒰 : Scheme.OpenCover.{w} W.left)
  [Category.{v} 𝒰.I₀] [h𝒰 : 𝒰.LocallyDirected]
  (g : ∀ i : 𝒰.I₀, 𝒰.X i ⟶ S) (hg : ∀ i, 𝒰.f i ≫ W.hom = g i)

include hg in
omit [Category.{v} 𝒰.I₀] [𝒰.LocallyDirected] in
/-- A cover component with its specified structural map is étale over the base. -/
lemma locallyDirectedOpenCover_etale (i : 𝒰.I₀) : Etale (g i) := by
  rw [← hg i]
  infer_instance

/-- The categorical hypercover data, with chosen structure maps on its components. -/
def locallyDirectedOpenCoverPreHypercover : PreOneHypercover.{max v w} W where
  I₀ := ULift.{v} 𝒰.I₀
  X i := MorphismProperty.Over.mk ⊤ (g i.down)
    (locallyDirectedOpenCover_etale W 𝒰 g hg i.down)
  f i := MorphismProperty.Over.homMk (𝒰.f i.down) (hg i.down)
  I₁ i j := Σ k : 𝒰.I₀, (k ⟶ i.down) × (k ⟶ j.down)
  Y {_ _} k := MorphismProperty.Over.mk ⊤ (g k.1)
    (locallyDirectedOpenCover_etale W 𝒰 g hg k.1)
  p₁ {i j} k := MorphismProperty.Over.homMk (𝒰.trans k.2.1) (by
    change 𝒰.trans k.2.1 ≫ g i.down = g k.1
    rw [← hg i.down, ← Category.assoc, Scheme.Cover.trans_map, hg k.1])
  p₂ {i j} k := MorphismProperty.Over.homMk (𝒰.trans k.2.2) (by
    change 𝒰.trans k.2.2 ≫ g j.down = g k.1
    rw [← hg j.down, ← Category.assoc, Scheme.Cover.trans_map, hg k.1])
  w {i j} k := by
    apply MorphismProperty.Over.Hom.ext
    change 𝒰.trans k.2.1 ≫ 𝒰.f i.down = 𝒰.trans k.2.2 ≫ 𝒰.f j.down
    rw [Scheme.Cover.trans_map, Scheme.Cover.trans_map]

/-- The common lower indices of the cover give a covering hypercover in the small site. -/
def locallyDirectedOpenCoverHypercover :
    S.smallEtaleTopology.OneHypercover.{max v w} W where
  __ := locallyDirectedOpenCoverPreHypercover W 𝒰 g hg
  mem₀ := by
    apply (Scheme.ofArrows_mem_smallEtaleTopology_iff _).mpr
    ext x
    simp only [Set.mem_iUnion, Set.mem_range, Set.mem_univ, iff_true]
    obtain ⟨i, y, hy⟩ := 𝒰.exists_eq x
    exact ⟨ULift.up i, y, hy⟩
  mem₁ i j T p₁ p₂ h := by
    have h' : p₁.left ≫ 𝒰.f i.down = p₂.left ≫ 𝒰.f j.down :=
      congrArg (fun k : T ⟶ W => k.left) h
    obtain ⟨𝒱, h𝒱⟩ := Scheme.mem_grothendieckTopology_iff.mp
      ((SchemeTheory.WeilRestriction.locallyDirectedCoverHypercover 𝒰).mem₁
        i j p₁.left p₂.left h')
    change _ ∈ S.smallGrothendieckTopology (P := @Etale) T
    rw [Scheme.smallGrothendieckTopology_eq_toGrothendieck_smallPretopology
      (P := (show MorphismProperty Scheme.{u} from @Etale))
      (Q := (show MorphismProperty Scheme.{u} from @Etale)) S le_rfl]
    apply (Scheme.mem_toGrothendieck_smallPretopology
      (P := (show MorphismProperty Scheme.{u} from @Etale))
      (Q := (show MorphismProperty Scheme.{u} from @Etale)) T _).mpr
    intro x
    obtain ⟨a, y, hy⟩ := 𝒱.exists_eq x
    let V : S.Etale := MorphismProperty.Over.mk ⊤ (𝒱.f a ≫ T.hom) inferInstance
    let q : V ⟶ T := MorphismProperty.Over.homMk (𝒱.f a) (by rfl)
    refine ⟨V, q, y, ?_, inferInstance, hy⟩
    obtain ⟨k, b, hb₁, hb₂⟩ := h𝒱 _ _ (Presieve.ofArrows.mk a)
    have hb : b ≫ g k.1 = 𝒱.f a ≫ T.hom := by
      have ht : 𝒰.trans k.2.1 ≫ g i.down = g k.1 := by
        rw [← hg i.down, ← Category.assoc, Scheme.Cover.trans_map, hg k.1]
      calc
        b ≫ g k.1 = b ≫ (𝒰.trans k.2.1 ≫ g i.down) := congrArg (b ≫ ·) ht.symm
        _ = (b ≫ 𝒰.trans k.2.1) ≫ g i.down :=
          (Category.assoc b (𝒰.trans k.2.1) (g i.down)).symm
        _ = (𝒱.f a ≫ p₁.left) ≫ g i.down := congrArg (· ≫ g i.down) hb₁.symm
        _ = 𝒱.f a ≫ (p₁.left ≫ g i.down) := Category.assoc _ _ _
        _ = 𝒱.f a ≫ T.hom := congrArg (𝒱.f a ≫ ·) p₁.w
    exact ⟨k, MorphismProperty.Over.homMk b hb,
      MorphismProperty.Over.Hom.ext hb₁, MorphismProperty.Over.Hom.ext hb₂⟩

/-- The covering arrow has the original underlying scheme morphism. -/
lemma locallyDirectedOpenCoverHypercover_f_left (i : ULift.{v} 𝒰.I₀) :
    ((locallyDirectedOpenCoverHypercover W 𝒰 g hg).f i).left = 𝒰.f i.down := rfl

/-- The first overlap projection has the original transition morphism. -/
lemma locallyDirectedOpenCoverHypercover_p₁_left
    {i j : ULift.{v} 𝒰.I₀} (k : Σ l : 𝒰.I₀, (l ⟶ i.down) × (l ⟶ j.down)) :
    ((locallyDirectedOpenCoverHypercover W 𝒰 g hg).p₁ (i₁ := i) (i₂ := j) k).left =
      𝒰.trans k.2.1 := rfl

/-- The second overlap projection has the original transition morphism. -/
lemma locallyDirectedOpenCoverHypercover_p₂_left
    {i j : ULift.{v} 𝒰.I₀} (k : Σ l : 𝒰.I₀, (l ⟶ i.down) × (l ⟶ j.down)) :
    ((locallyDirectedOpenCoverHypercover W 𝒰 g hg).p₂ (i₁ := i) (i₂ := j) k).left =
      𝒰.trans k.2.2 := rfl

end EtaleCohomology.Sites
