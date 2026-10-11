/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleCohomology.Sites.ClosedAdjunction
import EtaleCohomology.Sites.ConstantPresentation
import SchemeTheory.Etale.FiniteRefinement
import Mathlib.Algebra.Category.ModuleCat.Adjunctions
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.Morphisms.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
import Mathlib.AlgebraicGeometry.Sites.Etale
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.CategoryTheory.Sites.LocallySurjective
import Mathlib.CategoryTheory.Sites.Whiskering

/-!
# Finite covers carrying actual local lifts of a closed-fiber section

The closed-immersion adjunction unit is an epimorphism. Its image sieve
therefore supplies an actual lift near every point. The disjoint union of
these neighborhoods is an actual surjective étale morphism, to which the
finite refinement theorem applies.

No connectedness or global restriction-surjectivity hypothesis is used.
The local lifts are retained with their equations against the original
unit and the original section. Gluing on the finite cover and descent of
the resulting section are not asserted here.
-/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits Opposite

namespace EtaleCohomology

/-- Every actual closed-fiber section has étale local lifts whose cover
admits a finite surjective refinement. The refined map need not be étale.
Only quasi-compactness and quasi-separatedness of the ambient scheme are
required for this step of proper-local restriction surjectivity. -/
theorem exists_finite_refinement_closed_unit_lifts
    {X Z : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    (i : Z ⟶ X) [IsClosedImmersion i]
    (Λ : Type u) [CommRing Λ] (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ))
    (t : ((etalePushforward i Λ).obj ((etalePullback i Λ).obj F)).obj.obj
      (op (Scheme.Etale.mk (𝟙 X)))) :
    ∃ (V : X → X.Etale) (g : ∀ x : X, V x ⟶ Scheme.Etale.mk (𝟙 X))
      (a : ∀ x : X, F.obj.obj (op (V x))) (Y : Scheme.{u}) (q : Y ⟶ X),
      (∀ x : X, (((etalePullbackPushforwardAdjunction i Λ).unit.app F).hom.app
        (op (V x))) (a x) =
          ((etalePushforward i Λ).obj ((etalePullback i Λ).obj F)).obj.map
            (g x).op t) ∧
      Surjective (Sigma.desc (fun x : X => (g x).left)) ∧
      IsFinite q ∧ Surjective q ∧
      q.ZariskiLocallyFactorsThrough (Sigma.desc (fun x : X => (g x).left)) := by
  classical
  let G : Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ) :=
    (etalePushforward i Λ).obj ((etalePullback i Λ).obj F)
  let η : F ⟶ G := (etalePullbackPushforwardAdjunction i Λ).unit.app F
  have : X.smallEtaleTopology.HasSheafCompose (forget (ModuleCat.{u} Λ)) := by
    let : PreservesLimitsOfSize.{u, u + 1} (forget (ModuleCat.{u} Λ)) :=
      (ModuleCat.adj Λ).rightAdjoint_preservesLimits
    exact hasSheafCompose_of_preservesLimitsOfSize
      (F := forget (ModuleCat.{u} Λ)) X.smallEtaleTopology
  have : Sheaf.IsLocallySurjective η :=
    (Sheaf.isLocallySurjective_iff_epi'
      (J := X.smallEtaleTopology) (ModuleCat.{u} Λ) η).mpr inferInstance
  have hLocal (x : X) :
      ∃ (V : X.Etale) (g : V ⟶ Scheme.Etale.mk (𝟙 X)) (v : V.left)
        (a : F.obj.obj (op V)),
        η.hom.app (op V) a = G.obj.map g.op t ∧ g.left v = x := by
    obtain ⟨V, g, v, hg, hv⟩ := exists_etale_neighborhood_in_sieve
      (Presheaf.imageSieve η.hom t)
      (Presheaf.imageSieve_mem X.smallEtaleTopology η.hom t) x
    obtain ⟨a, ha⟩ := hg
    exact ⟨V, g, v, a, ha, hv⟩
  choose V g v a ha hv using hLocal
  let p : (∐ fun x : X => (V x).left) ⟶ X :=
    Sigma.desc (fun x : X => (g x).left)
  have : Etale p := by
    have : IsZariskiLocalAtSource (show MorphismProperty Scheme.{u} from @Etale) :=
      HasRingHomProperty.instIsZariskiLocalAtSource
    exact IsZariskiLocalAtSource.sigmaDesc
      (fun x : X => inferInstanceAs (Etale (g x).left))
  have hp : Surjective p := by
    constructor
    intro x
    refine ⟨Sigma.ι (fun x : X => (V x).left) x (v x), ?_⟩
    exact (Scheme.Hom.comp_apply _ _ (v x)).symm.trans
      ((congrArg (fun k : (V x).left ⟶ X => k (v x))
        (Sigma.ι_comp_desc (fun x : X => (g x).left) x)).trans (hv x))
  obtain ⟨Y, q, hqFinite, hqSurjective, hqLocal⟩ := Etale.exists_finite_refinement p
  exact ⟨V, g, a, Y, q, ha, hp, hqFinite, hqSurjective, hqLocal⟩

end EtaleCohomology
