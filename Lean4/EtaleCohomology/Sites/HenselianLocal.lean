/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import SchemeTheory.Etale.HenselianLocalSection
import EtaleCohomology.Sites.ConstantPresentation
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Category.ModuleCat.Adjunctions
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.AlgebraicGeometry.Sites.AffineEtale
import Mathlib.AlgebraicGeometry.Sites.Etale
import Mathlib.CategoryTheory.MorphismProperty.Comma
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.ConcreteCategory.Basic
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.CategoryTheory.Sites.LocallySurjective
import Mathlib.CategoryTheory.Sites.Sieves.Basic
import Mathlib.CategoryTheory.Sites.Whiskering


/-!
# Global lifting on a strictly local small étale site

Every covering sieve on the identity object of a strictly local spectrum is
maximal: a neighborhood over its closed point has a section. Consequently an
epimorphism of actual module sheaves is surjective on global sections. This
is the exactness ingredient for the local cohomology calculation in proper
base change; no proper base-change theorem is assumed here.
-/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Opposite

namespace EtaleCohomology

variable (R : Type u) [CommRing R] [HenselianLocalRing R]
  [IsSepClosed (IsLocalRing.ResidueField R)]

/-- A covering sieve on the identity object of a strictly local small étale
site contains its identity, and hence is the maximal sieve. -/
theorem sieve_eq_top_of_henselianLocalRing
    (S : Sieve (Scheme.Etale.mk (𝟙 (Spec.{u} (CommRingCat.of R)))))
    (hS : S ∈ (Spec.{u} (CommRingCat.of R)).smallEtaleTopology _) : S = ⊤ := by
  let W : (Spec.{u} (CommRingCat.of R)).Etale := Scheme.Etale.mk (𝟙 (Spec.{u} (CommRingCat.of R)))
  let r : Spec.{u} (CommRingCat.of (IsLocalRing.ResidueField R)) ⟶ Spec.{u} (CommRingCat.of R) :=
    Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))
  obtain ⟨Y, g, y, hg, hy⟩ := exists_etale_neighborhood_in_sieve S hS (r default)
  have hgleft : g.left = Y.hom := by
    have h := g.w
    change g.left ≫ 𝟙 (Spec.{u} (CommRingCat.of R)) = Y.hom at h
    exact (Category.comp_id g.left).symm.trans h
  have hclosed : Y.hom y = r default := by
    rw [← hgleft]
    exact hy
  obtain ⟨s, hs⟩ :=
    Etale.exists_section_of_isSepClosed_residueField R Y.hom y hclosed
  have hsg : s ≫ g.left = 𝟙 (Spec.{u} (CommRingCat.of R)) :=
    (congrArg (fun f : Y.left ⟶ Spec.{u} (CommRingCat.of R) => s ≫ f) hgleft).trans hs
  let k : W ⟶ Y := MorphismProperty.Over.homMk s hs
  have hkg : k ≫ g = 𝟙 W := by
    apply MorphismProperty.Over.Hom.ext
    exact hsg
  apply Sieve.id_mem_iff_eq_top.mp
  rw [← hkg]
  exact S.downward_closed hg k

/-- Epimorphisms of coefficient sheaves over a strictly local spectrum are
surjective on the actual module of global sections. The coefficient ring
is arbitrary and is unrelated to the strictly local base ring. -/
theorem sheaf_epi_globalSections_surjective_of_henselianLocalRing
    (Λ : Type u) [CommRing Λ]
    {F G : Sheaf (Spec.{u} (CommRingCat.of R)).smallEtaleTopology (ModuleCat.{u} Λ)}
    (η : F ⟶ G) [Epi η] :
    Function.Surjective (η.hom.app
      (op (Scheme.Etale.mk (𝟙 (Spec.{u} (CommRingCat.of R)))))) := by
  have : (Spec.{u} (CommRingCat.of R)).smallEtaleTopology.HasSheafCompose
      (forget (ModuleCat.{u} Λ)) := by
    let : Limits.PreservesLimitsOfSize.{u, u + 1} (forget (ModuleCat.{u} Λ)) :=
      (ModuleCat.adj Λ).rightAdjoint_preservesLimits
    exact hasSheafCompose_of_preservesLimitsOfSize
      (F := forget (ModuleCat.{u} Λ)) (Spec.{u} (CommRingCat.of R)).smallEtaleTopology
  have : Sheaf.IsLocallySurjective η :=
    (Sheaf.isLocallySurjective_iff_epi'
      (J := (Spec.{u} (CommRingCat.of R)).smallEtaleTopology) (ModuleCat.{u} Λ) η).mpr
        inferInstance
  intro t
  have hS := sieve_eq_top_of_henselianLocalRing R
    (Presheaf.imageSieve η.hom t)
    (Presheaf.imageSieve_mem (Spec.{u} (CommRingCat.of R)).smallEtaleTopology η.hom t)
  have hid : Presheaf.imageSieve η.hom t
      (𝟙 (Scheme.Etale.mk (𝟙 (Spec.{u} (CommRingCat.of R))))) := by
    rw [hS]
    trivial
  obtain ⟨s, hs⟩ := hid
  refine ⟨s, ?_⟩
  have hmap : G.obj.map (𝟙 (op (Scheme.Etale.mk (𝟙 (Spec.{u} (CommRingCat.of R)))))) =
      𝟙 (G.obj.obj (op (Scheme.Etale.mk (𝟙 (Spec.{u} (CommRingCat.of R)))))) :=
    G.obj.map_id (op (Scheme.Etale.mk (𝟙 (Spec.{u} (CommRingCat.of R)))))
  exact hs.trans ((ConcreteCategory.congr_hom hmap t).trans (ModuleCat.id_apply _ t))

end EtaleCohomology
