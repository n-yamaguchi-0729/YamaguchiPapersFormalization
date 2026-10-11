/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleCohomology.Constructible.FiniteEtaleSheaf
import EtaleCohomology.Sites.ConstantRepresentable
import EtaleCohomology.Sites.SetSheafFunctors
import EtaleCohomology.Sites.SetPullbackComposition
import SchemeTheory.FiniteEtale.LocalSplitting
import SchemeTheory.FiniteEtale.Forget.FiniteCoproducts
import Mathlib.AlgebraicGeometry.Cover.MorphismProperty
import Mathlib.AlgebraicGeometry.Sites.Etale
import Mathlib.CategoryTheory.MorphismProperty.Comma
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.CategoryTheory.Sites.Hypercover.Zero

/-!
# Finite locally constant étale sheaves of sets

A sheaf is finite locally constant if it is a constant sheaf of a finite set
on an actual étale cover. The model may depend on the member of the cover.
This property is local for the étale topology and is preserved by arbitrary
inverse image.

The sheaf represented by any finite étale morphism has this property: its
scheme-theoretic local splitting identifies its inverse image with the sheaf
represented by a finite disjoint union of copies of the base, which is the
corresponding finite constant sheaf. No assumption on a ground field,
connectedness, or noetherianity is needed.

Finite constant sheaves are explicitly represented by finite étale schemes.
The full converse for locally constant sheaves requires effective descent.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Limits

universe u

namespace EtaleCohomology

variable {X Y : Scheme.{u}}

private lemma finite_copies_projection (X : Scheme.{u}) (ι : Type u) [Finite ι] :
    IsFinite (Sigma.desc (fun _ : ι => 𝟙 X)) := by
  let T : FiniteEtale X := MorphismProperty.Over.mk ⊤ (𝟙 X)
    (show IsFiniteEtale (𝟙 X) from ⟨⟩)
  let F := FiniteEtale.forget X ⋙ CategoryTheory.Over.forget X
  let W : FiniteEtale X := ∐ fun _ : ι => T
  let S : Over X := (FiniteEtale.forget X).obj W
  have : PreservesFiniteCoproducts F :=
    inferInstanceAs (PreservesFiniteCoproducts (FiniteEtale.forget X ⋙ Over.forget X))
  have : IsIso (sigmaComparison F (fun _ : ι => T)) := inferInstance
  have : IsFinite S.hom := W.prop.toIsFinite
  have he : sigmaComparison F (fun _ : ι => T) ≫ S.hom =
      Sigma.desc (fun _ : ι => ((FiniteEtale.forget X).obj T).hom) := by
    apply Sigma.hom_ext
    intro i
    rw [Sigma.ι_comp_desc, ← Category.assoc, ι_comp_sigmaComparison]
    exact Over.w ((FiniteEtale.forget X).map (Sigma.ι (fun _ : ι => T) i))
  have hfin : IsFinite (sigmaComparison F (fun _ : ι => T) ≫ S.hom) := inferInstance
  rw [he] at hfin
  exact hfin

/-- A finite disjoint union of copies of the base as a finite étale scheme.
Finiteness follows from the existing finite-coproduct preservation theorem. -/
def finiteEtaleCopies (X : Scheme.{u}) (ι : Type u) [Finite ι] : FiniteEtale X := by
  have : IsFinite (etaleCopies X ι).hom := finite_copies_projection X ι
  have : Etale (etaleCopies X ι).hom := (etaleCopies X ι).prop
  exact MorphismProperty.Over.mk ⊤ (etaleCopies X ι).hom ⟨⟩

/-- The finite constant sheaf is represented by the corresponding finite étale scheme. -/
def finiteEtaleCopiesSheafIso (X : Scheme.{u}) (ι : Type u) [Finite ι] :
    (finiteEtaleSheaf X).obj (finiteEtaleCopies X ι) ≅
      (constantSheaf X.smallEtaleTopology (Type u)).obj ι :=
  etaleCopiesSheafIso X ι

/-- An actual étale cover trivializes the sheaf with finite set models. -/
def IsEtaleFiniteLocallyConstantSet (G : Sheaf X.smallEtaleTopology (Type u)) : Prop :=
  ∃ 𝒰 : X.Cover.{u} (Scheme.precoverage (show MorphismProperty Scheme.{u} from @Etale)),
    ∀ a : 𝒰.I₀, ∃ A : Type u, Finite A ∧
      Nonempty ((etaleSetPullback (𝒰.f a)).obj G ≅
        (constantSheaf (𝒰.X a).smallEtaleTopology (Type u)).obj A)

/-- Finite local constancy is invariant under isomorphisms of sheaves. -/
lemma IsEtaleFiniteLocallyConstantSet.of_iso
    {G H : Sheaf X.smallEtaleTopology (Type u)}
    (hG : IsEtaleFiniteLocallyConstantSet G) (e : G ≅ H) :
    IsEtaleFiniteLocallyConstantSet H := by
  obtain ⟨𝒰, h𝒰⟩ := hG
  refine ⟨𝒰, fun a => ?_⟩
  obtain ⟨A, hA, ⟨eA⟩⟩ := h𝒰 a
  exact ⟨A, hA, ⟨(etaleSetPullback (𝒰.f a)).mapIso e.symm ≪≫ eA⟩⟩

/-- A finite constant sheaf is trivialized by the identity cover. -/
lemma IsEtaleFiniteLocallyConstantSet.constant (A : Type u) [Finite A] :
    IsEtaleFiniteLocallyConstantSet ((constantSheaf X.smallEtaleTopology (Type u)).obj A) := by
  refine ⟨Scheme.coverOfIsIso (P := show MorphismProperty Scheme.{u} from @Etale) (𝟙 X), ?_⟩
  intro a
  exact ⟨A, inferInstance, ⟨(etaleSetPullbackConstantIso (𝟙 X)).app A⟩⟩

/-- Pulling back a trivializing cover preserves its finite constant models. -/
lemma IsEtaleFiniteLocallyConstantSet.pullback (f : X ⟶ Y)
    {G : Sheaf Y.smallEtaleTopology (Type u)} (hG : IsEtaleFiniteLocallyConstantSet G) :
    IsEtaleFiniteLocallyConstantSet ((etaleSetPullback f).obj G) := by
  obtain ⟨𝒰, h𝒰⟩ := hG
  refine ⟨𝒰.pullback₁ f, fun a => ?_⟩
  obtain ⟨A, hA, ⟨eA⟩⟩ := h𝒰 a
  let ecomp : etaleSetPullback ((𝒰.pullback₁ f).f a ≫ f) ≅
      etaleSetPullback (𝒰.pullbackHom f a ≫ 𝒰.f a) :=
    eqToIso (congrArg (fun k => etaleSetPullback k) (𝒰.pullbackHom_map f a).symm)
  exact ⟨A, hA, ⟨((etaleSetPullbackCompIso ((𝒰.pullback₁ f).f a) f).app G).symm ≪≫
    ecomp.app G ≪≫ (etaleSetPullbackCompIso (𝒰.pullbackHom f a) (𝒰.f a)).app G ≪≫
    (etaleSetPullback (𝒰.pullbackHom f a)).mapIso eA ≪≫
    (etaleSetPullbackConstantIso (𝒰.pullbackHom f a)).app A⟩⟩

/-- Finite local constancy descends through an étale cover by composing covers. -/
lemma IsEtaleFiniteLocallyConstantSet.of_cover
    (𝒰 : X.Cover.{u} (Scheme.precoverage (show MorphismProperty Scheme.{u} from @Etale)))
    {G : Sheaf X.smallEtaleTopology (Type u)}
    (hG : ∀ a : 𝒰.I₀, IsEtaleFiniteLocallyConstantSet ((etaleSetPullback (𝒰.f a)).obj G)) :
    IsEtaleFiniteLocallyConstantSet G := by
  choose 𝒱 h𝒱 using hG
  refine ⟨𝒰.bind 𝒱, ?_⟩
  rintro ⟨a, b⟩
  obtain ⟨A, hA, ⟨eA⟩⟩ := h𝒱 a b
  exact ⟨A, hA, ⟨(etaleSetPullbackCompIso ((𝒱 a).f b) (𝒰.f a)).app G ≪≫ eA⟩⟩

/-- The sheaf represented by a finite étale cover is finite locally constant. -/
theorem finiteEtaleSheaf_isEtaleFiniteLocallyConstantSet (W : FiniteEtale X) :
    IsEtaleFiniteLocallyConstantSet ((finiteEtaleSheaf X).obj W) := by
  have : IsFiniteEtale ((FiniteEtale.forget X).obj W).hom := W.prop
  obtain ⟨𝒰, _, h𝒰⟩ :=
    IsFiniteEtale.exists_etale_splitting_cover ((FiniteEtale.forget X).obj W).hom
  refine ⟨𝒰, fun a => ?_⟩
  obtain ⟨n, E, hE⟩ := h𝒰 a
  let e : etaleCopies (𝒰.X a) (ULift.{u} (Fin n)) ≅
      (etaleBaseChange (𝒰.f a)).obj ((finiteEtaleToEtale X).obj W) :=
    MorphismProperty.Over.isoMk E hE
  exact ⟨ULift.{u} (Fin n), inferInstance,
    ⟨etaleSetPullbackYonedaObjIso (𝒰.f a) ((finiteEtaleToEtale X).obj W) ≪≫
      (𝒰.X a).smallEtaleTopology.yoneda.mapIso e.symm ≪≫
      etaleCopiesSheafIso (𝒰.X a) (ULift.{u} (Fin n))⟩⟩

end EtaleCohomology
