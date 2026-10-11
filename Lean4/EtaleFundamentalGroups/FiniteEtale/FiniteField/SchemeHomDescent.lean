/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Mathlib.AlgebraicGeometry.AffineTransitionLimit
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import EtaleFundamentalGroups.FiniteEtale.FiniteField.ConstantFieldLimit

/-!
# Descent of scheme morphisms to a finite constant field

For a qcqs scheme over a field, a morphism from an algebraic constant extension
to a fixed locally finitely presented scheme descends to an actual finite
intermediate field. The structure map and recovery equality use the native
constant-field pullbacks.
-/

noncomputable section

open CategoryTheory Limits Opposite AlgebraicGeometry

universe u v

namespace EtaleFundamentalGroups

variable (k L : Type u) [Field k] [Field L] [Algebra k L]

/-- An `X`-morphism from `X_L` to a locally finitely presented `X`-scheme
descends to a finite intermediate field of an algebraic extension `L/k`. -/
theorem exists_finiteIntermediateField_schemeHom
    [Algebra.IsAlgebraic k L]
    (X Y : Scheme.{u}) (f : X ⟶ Spec (CommRingCat.of k)) (h : Y ⟶ X)
    [CompactSpace X] [QuasiSeparatedSpace X] [LocallyOfFinitePresentation h]
    (a : pullback (Spec.map (CommRingCat.ofHom (algebraMap k L))) f ⟶ Y)
    (ha : a ≫ h = pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap k L))) f) :
    ∃ s : Finset L, FiniteDimensional k (IntermediateField.adjoin k (s : Set L)) ∧
      ∃ g : pullback (Spec.map (CommRingCat.ofHom
          (algebraMap k (IntermediateField.adjoin k (s : Set L))))) f ⟶ Y,
        (constantFieldInverseLimitCone k L X f).π.app (op s) ≫ g = a ∧
        g ≫ h = pullback.snd (Spec.map (CommRingCat.ofHom
          (algebraMap k (IntermediateField.adjoin k (s : Set L))))) f := by
  let D := constantFieldInverseLimitDiagram k L X f
  let c := constantFieldInverseLimitCone k L X f
  let t := constantFieldInverseLimitProjection k L X f
  let : ∀ {i j : (Finset L)ᵒᵖ} (g : i ⟶ j), IsAffineHom (D.map g) :=
    fun g ↦ constantFieldInverseLimitDiagram_map_isAffineHom k L X f g
  let : ∀ i : (Finset L)ᵒᵖ, CompactSpace (D.obj i) :=
    fun i ↦ constantFieldInverseLimitDiagram_obj_compactSpace k L X f i
  let : ∀ i : (Finset L)ᵒᵖ, QuasiSeparatedSpace (D.obj i) :=
    fun i ↦ constantFieldInverseLimitDiagram_obj_quasiSeparatedSpace k L X f i
  have hcompat : c.π ≫ t = (Functor.const _).map (a ≫ h) := by
    rw [ha]
    exact constantFieldInverseLimitCone_π_projection k L X f
  obtain ⟨i, g, hg, hg'⟩ := Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation
    D t h c (constantFieldInverseLimitConeIsLimit k L X f) a hcompat
  refine ⟨i.unop, ?_, g, hg, hg'⟩
  exact IntermediateField.finiteDimensional_adjoin
    (fun x _ ↦ (Algebra.IsAlgebraic.isAlgebraic (R := k) x).isIntegral)

/-- Two maps from finite coefficient stages which agree over the extension field
already agree over an actual common finite coefficient stage. -/
theorem exists_constantFieldStage_hom_eq
    (X : Scheme.{u}) (f : X ⟶ Spec (CommRingCat.of k)) [CompactSpace X]
    {Y : Scheme.{u}} (h : Y ⟶ X) [LocallyOfFiniteType h]
    (s r : Finset L)
    (a : pullback (Spec.map (CommRingCat.ofHom
      (algebraMap k (IntermediateField.adjoin k (s : Set L))))) f ⟶ Y)
    (b : pullback (Spec.map (CommRingCat.ofHom
      (algebraMap k (IntermediateField.adjoin k (r : Set L))))) f ⟶ Y)
    (ha : a ≫ h = pullback.snd (Spec.map (CommRingCat.ofHom
      (algebraMap k (IntermediateField.adjoin k (s : Set L))))) f)
    (hb : b ≫ h = pullback.snd (Spec.map (CommRingCat.ofHom
      (algebraMap k (IntermediateField.adjoin k (r : Set L))))) f)
    (hab : (constantFieldInverseLimitCone k L X f).π.app (op s) ≫ a =
      (constantFieldInverseLimitCone k L X f).π.app (op r) ≫ b) :
    ∃ (t : Finset L) (hst : s ⊆ t) (hrt : r ⊆ t),
      (constantFieldInverseLimitDiagram k L X f).map (homOfLE hst).op ≫ a =
        (constantFieldInverseLimitDiagram k L X f).map (homOfLE hrt).op ≫ b := by
  let D := constantFieldInverseLimitDiagram k L X f
  let (i : (Finset L)ᵒᵖ) : CompactSpace (D.obj i) :=
    constantFieldInverseLimitDiagram_obj_compactSpace k L X f i
  let {i j : (Finset L)ᵒᵖ} (g : i ⟶ j) : IsAffineHom (D.map g) :=
    constantFieldInverseLimitDiagram_map_isAffineHom k L X f g
  obtain ⟨t, hst, hrt, heq⟩ :=
    Scheme.exists_hom_hom_comp_eq_comp_of_locallyOfFiniteType
      D (constantFieldInverseLimitProjection k L X f) h
      (constantFieldInverseLimitCone k L X f)
      (constantFieldInverseLimitConeIsLimit k L X f)
      a ha.symm b hb.symm hab
  refine ⟨t.unop, leOfHom hst.unop, leOfHom hrt.unop, ?_⟩
  change D.map (homOfLE (leOfHom hst.unop)).op ≫ a =
    D.map (homOfLE (leOfHom hrt.unop)).op ≫ b
  exact heq

/-- A finite family of equalities over the extension holds simultaneously at
one actual coefficient stage, including when the family is empty. -/
theorem exists_constantFieldStage_hom_eq_family
    {ι : Type v} [Finite ι]
    (X Y : ι → Scheme.{u}) (f : ∀ i, X i ⟶ Spec (CommRingCat.of k))
    [∀ i, CompactSpace (X i)] (h : ∀ i, Y i ⟶ X i)
    [∀ i, LocallyOfFiniteType (h i)] (s : Finset L)
    (a b : ∀ i, (constantFieldInverseLimitDiagram k L (X i) (f i)).obj (op s) ⟶ Y i)
    (ha : ∀ i, a i ≫ h i = (constantFieldInverseLimitProjection k L (X i) (f i)).app (op s))
    (hb : ∀ i, b i ≫ h i = (constantFieldInverseLimitProjection k L (X i) (f i)).app (op s))
    (hab : ∀ i, (constantFieldInverseLimitCone k L (X i) (f i)).π.app (op s) ≫ a i =
      (constantFieldInverseLimitCone k L (X i) (f i)).π.app (op s) ≫ b i) :
    ∃ (t : Finset L) (hst : s ⊆ t), ∀ i,
      (constantFieldInverseLimitDiagram k L (X i) (f i)).map (homOfLE hst).op ≫ a i =
        (constantFieldInverseLimitDiagram k L (X i) (f i)).map (homOfLE hst).op ≫ b i := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  have H (i : ι) : ∃ (t : Finset L) (hst : s ⊆ t),
      (constantFieldInverseLimitDiagram k L (X i) (f i)).map (homOfLE hst).op ≫ a i =
        (constantFieldInverseLimitDiagram k L (X i) (f i)).map (homOfLE hst).op ≫ b i := by
    obtain ⟨t, ht, _, heq⟩ := exists_constantFieldStage_hom_eq k L (X i) (f i)
      (h i) s s (a i) (b i) (ha i) (hb i) (hab i)
    exact ⟨t, ht, heq⟩
  choose t ht heq using H
  let T : Finset L := s ∪ Finset.univ.biUnion t
  have hsT : s ⊆ T := Finset.subset_union_left
  have hiT (i : ι) : t i ⊆ T := by
    intro x hx
    exact Finset.mem_union_right s (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hx⟩)
  refine ⟨T, hsT, ?_⟩
  intro i
  have hcomp : (homOfLE hsT).op = (homOfLE (hiT i)).op ≫ (homOfLE (ht i)).op :=
    Subsingleton.elim _ _
  rw [hcomp, Functor.map_comp, Category.assoc, Category.assoc, heq i]

end EtaleFundamentalGroups

end
