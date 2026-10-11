/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleCohomology.Constructible.Basic
import EtaleCohomology.Constructible.LocallyConstant
import EtaleCohomology.Constructible.Stratification
import EtaleCohomology.Sites.PullbackComposition
import EtaleCohomology.Sites.SheafFunctors
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.AlgebraicGeometry.Restrict
import Mathlib.AlgebraicGeometry.Sites.Etale
import Mathlib.Data.Set.Disjoint
import Mathlib.Topology.Constructible

/-!
# Restriction of constructible étale sheaves

Finite adapted stratifications transport along scheme isomorphisms. This
identifies affine-local constructibility with finite stratifiability on an
affine scheme and proves restriction to an arbitrary open subscheme preserves
constructibility. No noetherianity or quasi-compactness of the open immersion
is required.
-/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory

namespace EtaleCohomology

variable {X Y : Scheme.{u}}

/-- Transport a finite stratification along an actual scheme isomorphism. -/
def ConstructibleStratification.mapIso (S : ConstructibleStratification X) (e : X ≅ Y) :
    ConstructibleStratification Y where
  I := S.I
  finite := S.finite
  stratum := S.stratum
  map i := S.map i ≫ e.hom
  isImmersion i := by
    have : IsImmersion (S.map i) := S.isImmersion i
    infer_instance
  constructible_range i := by
    change Topology.IsConstructible (Set.range (e.hom ∘ S.map i))
    rw [Set.range_comp]
    apply (S.constructible_range i).image_of_isOpenEmbedding e.hom.isOpenEmbedding
    rw [Set.range_eq_univ.mpr e.hom.surjective]
    exact IsRetrocompact.univ
  disjoint := by
    intro i j hij
    apply Set.disjoint_left.mpr
    rintro y ⟨x, hx⟩ ⟨z, hz⟩
    have hxz : S.map i x = S.map j z :=
      e.hom.isOpenEmbedding.injective (hx.trans hz.symm)
    exact (S.disjoint hij).notMem_of_mem_left ⟨x, rfl⟩ ⟨z, hxz.symm⟩
  cover y := by
    obtain ⟨i, x, hx⟩ := S.cover (e.inv y)
    refine ⟨i, x, ?_⟩
    change e.hom (S.map i x) = y
    rw [hx]
    exact congrArg (fun f : Y ⟶ Y => f y) e.inv_hom_id

variable {R : Type u} [CommRing R]

/-- Transport an adapted stratification back from the inverse image by an isomorphism. -/
lemma HasFiniteConstructibleStratification.of_pullbackIso
    (e : X ≅ Y) {G : Sheaf Y.smallEtaleTopology (ModuleCat.{u} R)}
    (hG : HasFiniteConstructibleStratification R ((etalePullback e.hom R).obj G)) :
    HasFiniteConstructibleStratification R G := by
  obtain ⟨S, hS⟩ := hG
  refine ⟨S.mapIso e, fun i => ?_⟩
  exact (hS i).of_iso ((etalePullbackCompIso (S.map i) e.hom R).app G).symm

/-- Finite stratifiability is preserved by inverse image along an isomorphism. -/
lemma HasFiniteConstructibleStratification.pullbackIso
    (e : X ≅ Y) {G : Sheaf Y.smallEtaleTopology (ModuleCat.{u} R)}
    (hG : HasFiniteConstructibleStratification R G) :
    HasFiniteConstructibleStratification R ((etalePullback e.hom R).obj G) := by
  obtain ⟨S, hS⟩ := hG
  refine ⟨S.mapIso e.symm, fun i => ?_⟩
  have hi : (S.map i ≫ e.inv) ≫ e.hom = S.map i := by
    rw [Category.assoc, e.inv_hom_id, Category.comp_id]
  let ei : (etalePullback (S.map i ≫ e.inv) R).obj ((etalePullback e.hom R).obj G) ≅
      (etalePullback (S.map i) R).obj G :=
    ((etalePullbackCompIso (S.map i ≫ e.inv) e.hom R).app G).symm ≪≫
      eqToIso (congrArg (fun f : S.stratum i ⟶ Y => (etalePullback f R).obj G) hi)
  exact (hS i).of_iso ei.symm

/-- On an affine scheme, the affine-local definition is equivalent to one
finite adapted stratification of the whole scheme. -/
theorem isEtaleConstructible_iff_hasFiniteConstructibleStratification [IsAffine X]
    (G : Sheaf X.smallEtaleTopology (ModuleCat.{u} R)) :
    IsEtaleConstructible R G ↔ HasFiniteConstructibleStratification R G := by
  constructor
  · intro hG
    exact HasFiniteConstructibleStratification.of_pullbackIso X.topIso
      (hG ⟨⊤, isAffineOpen_top X⟩)
  · exact HasFiniteConstructibleStratification.isEtaleConstructible

/-- Restriction to any open subscheme preserves affine-local constructibility. -/
lemma IsEtaleConstructible.restrict
    {G : Sheaf X.smallEtaleTopology (ModuleCat.{u} R)}
    (hG : IsEtaleConstructible R G) (U : X.Opens) :
    IsEtaleConstructible R ((etalePullback U.ι R).obj G) := by
  intro V
  let W : X.Opens := U.ι ''ᵁ V.1
  let e : V.1.toScheme ≅ W.toScheme := U.ι.isoImage V.1
  have hW : IsAffineOpen W := IsAffine.of_isIso e.inv
  have h := HasFiniteConstructibleStratification.pullbackIso e (hG ⟨W, hW⟩)
  let ei : (etalePullback e.hom R).obj ((etalePullback W.ι R).obj G) ≅
      (etalePullback V.1.ι R).obj ((etalePullback U.ι R).obj G) :=
    ((etalePullbackCompIso e.hom W.ι R).app G).symm ≪≫
      eqToIso (congrArg (fun f : V.1.toScheme ⟶ X => (etalePullback f R).obj G)
        (U.ι.isoImage_hom_ι V.1)) ≪≫
      (etalePullbackCompIso V.1.ι U.ι R).app G
  exact h.of_iso ei

end EtaleCohomology
