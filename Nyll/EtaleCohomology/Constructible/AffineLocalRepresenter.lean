/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleCohomology.Constructible.FiniteEtaleSheaf
import Nyll.EtaleCohomology.Constructible.FiniteLocallyConstantSet
import Nyll.EtaleCohomology.Constructible.LocalRepresenters
import Nyll.EtaleCohomology.Constructible.SigmaRepresenter
import Nyll.EtaleCohomology.Sites.EtaleRestriction
import Nyll.SchemeTheory.Pi1.FiniteEtale.Basic
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties
import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
import Mathlib.AlgebraicGeometry.Sites.Etale
import Mathlib.CategoryTheory.MorphismProperty.Comma
import Mathlib.RingTheory.RingHom.FaithfullyFlat

/-!
# A single affine cover with a finite étale representer

A finite locally constant set sheaf on a quasi-compact scheme becomes represented
by a finite étale scheme after ordinary restriction to one affine surjective
étale cover. We combine a finite affine family of local representers by its
disjoint union. Over an affine base, the same cover supplies a faithfully flat
étale map on global section rings. Neither construction assumes a ground field,
noetherianity, or quasi-separatedness.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Limits

universe u

namespace EtaleCohomology

variable {X : Scheme.{u}} {G : Sheaf X.smallEtaleTopology (Type u)}

/-- On a quasi-compact base, a finite locally constant set sheaf has a finite
étale representer after restriction to one affine surjective étale cover. -/
theorem IsEtaleFiniteLocallyConstantSet.exists_affine_localRepresenter
    [CompactSpace X] (hG : IsEtaleFiniteLocallyConstantSet G) :
    ∃ (V : Scheme.{u}) (f : V ⟶ X) (hf : Etale f),
      IsAffine V ∧ Surjective f ∧ ∃ W : FiniteEtale V,
        Nonempty (((etalePostcompose (hf := hf) f).op ⋙ G.obj).RepresentableBy
          ((finiteEtaleToEtale V).obj W)) := by
  obtain ⟨𝒱, hfinite, hRep⟩ := hG.exists_finite_affine_localRepresenters
  have : Finite 𝒱.I₀ := hfinite
  let U : 𝒱.I₀ → X.Etale := fun b =>
    MorphismProperty.Over.mk ⊤ (𝒱.cover.f b) (𝒱.map_prop b)
  let W : ∀ b : 𝒱.I₀, FiniteEtale (U b).left := fun b => Classical.choose (hRep b)
  have hW (b : 𝒱.I₀) :
      ((etalePostcompose (U b).hom).op ⋙ G.obj).RepresentableBy
        ((finiteEtaleToEtale (U b).left).obj (W b)) :=
    Classical.choice (Classical.choose_spec (hRep b))
  refine ⟨(etaleSigma U).left, (etaleSigma U).hom, (etaleSigma U).prop, ?_, ?_,
    finiteEtaleSigma (fun b => (U b).left) W,
    ⟨finiteEtaleSigmaRestrictionRepresentableBy U G W hW⟩⟩
  · change IsAffine (∐ fun b : 𝒱.I₀ => Spec (𝒱.X b))
    infer_instance
  · constructor
    intro x
    obtain ⟨y, hy⟩ := 𝒱.covers x
    refine ⟨Sigma.ι (fun b : 𝒱.I₀ => Spec (𝒱.X b)) (𝒱.idx x) y, ?_⟩
    change (Sigma.desc 𝒱.f) (Sigma.ι (fun b : 𝒱.I₀ => Spec (𝒱.X b)) (𝒱.idx x) y) = x
    rw [← Scheme.Hom.comp_apply, Sigma.ι_comp_desc]
    exact hy

/-- Over an affine base, the actual affine cover carrying the representer has
a faithfully flat étale map on global sections, suitable for algebra descent. -/
theorem IsEtaleFiniteLocallyConstantSet.exists_affine_localRepresenter_faithfullyFlat
    [IsAffine X] (hG : IsEtaleFiniteLocallyConstantSet G) :
    ∃ (V : Scheme.{u}) (f : V ⟶ X) (hf : Etale f),
      IsAffine V ∧ Surjective f ∧ f.appTop.hom.FaithfullyFlat ∧ f.appTop.hom.Etale ∧
        ∃ W : FiniteEtale V,
          Nonempty (((etalePostcompose (hf := hf) f).op ⋙ G.obj).RepresentableBy
            ((finiteEtaleToEtale V).obj W)) := by
  obtain ⟨V, f, hf, hV, hSurj, W, hW⟩ := hG.exists_affine_localRepresenter
  have : IsAffine V := hV
  have : Etale f := hf
  exact ⟨V, f, hf, hV, hSurj,
    (Flat.flat_and_surjective_iff_faithfullyFlat_of_isAffine f).mp
      ⟨inferInstance, hSurj⟩,
    HasRingHomProperty.appTop (P := @Etale) f hf, W, hW⟩

end EtaleCohomology
