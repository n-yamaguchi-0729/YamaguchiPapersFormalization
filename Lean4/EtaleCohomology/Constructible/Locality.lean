/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleCohomology.Constructible.Basic
import EtaleCohomology.Constructible.FiniteGluing
import EtaleCohomology.Constructible.Pullback
import EtaleCohomology.Constructible.Restriction
import EtaleCohomology.Sites.PullbackComposition
import EtaleCohomology.Sites.SheafFunctors
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Cover.Open
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.AlgebraicGeometry.Restrict

/-!
# Zariski locality and arbitrary pullback of constructible étale sheaves

On a qcqs scheme, affine-local constructibility is equivalent to a finite
adapted stratification. On any scheme it is Zariski local. Pullback along any
scheme morphism preserves constructibility: affine neighborhoods of source
points map into affine opens of the target, and their finite stratifications
glue by the preceding geometric refinement theorem.
-/

noncomputable section
universe u
open AlgebraicGeometry CategoryTheory

namespace EtaleCohomology

variable {X Y : Scheme.{u}} {R : Type u} [CommRing R]

/-- A constructible sheaf on a qcqs scheme admits one finite adapted stratification. -/
theorem IsEtaleConstructible.hasFiniteConstructibleStratification
    [CompactSpace X] [QuasiSeparatedSpace X]
    {G : Sheaf X.smallEtaleTopology (ModuleCat.{u} R)} (hG : IsEtaleConstructible R G) :
    HasFiniteConstructibleStratification R G := by
  apply HasFiniteConstructibleStratification.of_affine_neighborhoods
  intro x
  obtain ⟨U, hU, hx, _⟩ := exists_isAffineOpen_mem_and_subset (show x ∈ (⊤ : X.Opens) from trivial)
  exact ⟨⟨U, hU⟩, hx, hG ⟨U, hU⟩⟩

/-- Constructibility pulls back along every scheme morphism, with no
quasi-compactness, separation, or noetherianity condition on the morphism. -/
theorem IsEtaleConstructible.pullback (f : X ⟶ Y)
    {G : Sheaf Y.smallEtaleTopology (ModuleCat.{u} R)} (hG : IsEtaleConstructible R G) :
    IsEtaleConstructible R ((etalePullback f R).obj G) := by
  intro V
  apply HasFiniteConstructibleStratification.of_affine_neighborhoods
  intro x
  let fV : V.1.toScheme ⟶ Y := V.1.ι ≫ f
  obtain ⟨U, hU, hxU, _⟩ := exists_isAffineOpen_mem_and_subset
    (show fV x ∈ (⊤ : Y.Opens) from trivial)
  obtain ⟨W, hW, hxW, hWU⟩ := exists_isAffineOpen_mem_and_subset
    (show x ∈ fV ⁻¹ᵁ U from hxU)
  have hrange : Set.range (W.ι ≫ fV) ⊆ Set.range U.ι := by
    rintro y ⟨z, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact hWU z.2
  let g : W.toScheme ⟶ U.toScheme := IsOpenImmersion.lift U.ι (W.ι ≫ fV) hrange
  have hg : g ≫ U.ι = W.ι ≫ fV := IsOpenImmersion.lift_fac U.ι (W.ι ≫ fV) hrange
  refine ⟨⟨W, hW⟩, hxW, ?_⟩
  have h := (hG ⟨U, hU⟩).pullback g
  let e : (etalePullback g R).obj ((etalePullback U.ι R).obj G) ≅
      (etalePullback W.ι R).obj ((etalePullback V.1.ι R).obj ((etalePullback f R).obj G)) :=
    ((etalePullbackCompIso g U.ι R).app G).symm ≪≫
      eqToIso (congrArg (fun k : W.toScheme ⟶ Y => (etalePullback k R).obj G) hg) ≪≫
      (etalePullbackCompIso W.ι fV R).app G ≪≫
      (etalePullback W.ι R).mapIso ((etalePullbackCompIso V.1.ι f R).app G)
  exact h.of_iso e

/-- Constructibility can be verified on an open neighborhood of each point. -/
theorem IsEtaleConstructible.of_open_neighborhoods
    {G : Sheaf X.smallEtaleTopology (ModuleCat.{u} R)}
    (hG : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
      IsEtaleConstructible R ((etalePullback U.ι R).obj G)) :
    IsEtaleConstructible R G := by
  intro V
  apply HasFiniteConstructibleStratification.of_affine_neighborhoods
  intro x
  obtain ⟨U, hxU, hU⟩ := hG (V.1.ι x)
  obtain ⟨W, hW, hxW, hWU⟩ := exists_isAffineOpen_mem_and_subset
    (show x ∈ V.1.ι ⁻¹ᵁ U from hxU)
  have hrange : Set.range (W.ι ≫ V.1.ι) ⊆ Set.range U.ι := by
    rintro y ⟨z, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact hWU z.2
  let g : W.toScheme ⟶ U.toScheme := IsOpenImmersion.lift U.ι (W.ι ≫ V.1.ι) hrange
  have hg : g ≫ U.ι = W.ι ≫ V.1.ι := IsOpenImmersion.lift_fac U.ι (W.ι ≫ V.1.ι) hrange
  have : IsAffine W.toScheme := hW
  have h := (hU.pullback g).hasFiniteConstructibleStratification
  refine ⟨⟨W, hW⟩, hxW, ?_⟩
  exact h.of_iso (((etalePullbackCompIso g U.ι R).app G).symm ≪≫
    eqToIso (congrArg (fun k : W.toScheme ⟶ X => (etalePullback k R).obj G) hg) ≪≫
    (etalePullbackCompIso W.ι V.1.ι R).app G)

/-- Constructibility is local for an arbitrary family of open subsets covering the base. -/
theorem isEtaleConstructible_iff_open_cover {ι : Type u} (U : ι → X.Opens)
    (hcover : ∀ x : X, ∃ i : ι, x ∈ U i)
    (G : Sheaf X.smallEtaleTopology (ModuleCat.{u} R)) :
    IsEtaleConstructible R G ↔
      ∀ i : ι, IsEtaleConstructible R ((etalePullback (U i).ι R).obj G) := by
  constructor
  · intro hG i
    exact hG.restrict (U i)
  · intro hG
    apply IsEtaleConstructible.of_open_neighborhoods
    intro x
    obtain ⟨i, hi⟩ := hcover x
    exact ⟨U i, hi, hG i⟩

end EtaleCohomology
