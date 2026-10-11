/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleCohomology.Constructible.FiniteEtaleSheaf
import Nyll.EtaleCohomology.Constructible.FiniteLocallyConstantSet
import Nyll.EtaleCohomology.Sites.EtaleRestriction
import Nyll.EtaleCohomology.Sites.SetPullbackComposition
import Nyll.SchemeTheory.Etale.FiniteAffineCover
import Mathlib.CategoryTheory.Sites.Subcanonical
import Mathlib.CategoryTheory.Yoneda

/-!
# Local scheme representers of finite locally constant sheaves

An étale trivialization gives actual finite étale representers of the
restricted presheaf. Its representing equivalence is natural on the local
small site, so its universal section can be used to construct descent maps.
Global representability still requires effective descent.
-/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory

namespace EtaleCohomology

variable {X : Scheme.{u}} {G : Sheaf X.smallEtaleTopology (Type u)}

/-- A finite locally constant sheaf is represented on an étale cover by genuine
finite étale schemes, as a restriction of its original presheaf. -/
theorem IsEtaleFiniteLocallyConstantSet.exists_localRepresenters
    (hG : IsEtaleFiniteLocallyConstantSet G) :
    ∃ 𝒰 : X.Cover.{u} (Scheme.precoverage (show MorphismProperty Scheme.{u} from @Etale)),
      ∀ a : 𝒰.I₀, ∃ W : FiniteEtale (𝒰.X a),
        Nonempty (((etalePostcompose (𝒰.f a)).op ⋙ G.obj).RepresentableBy
          ((finiteEtaleToEtale (𝒰.X a)).obj W)) := by
  obtain ⟨𝒰, h𝒰⟩ := hG
  refine ⟨𝒰, fun a => ?_⟩
  obtain ⟨A, hA, ⟨eA⟩⟩ := h𝒰 a
  let W := finiteEtaleCopies (𝒰.X a) A
  let e : (finiteEtaleSheaf (𝒰.X a)).obj W ≅
      (etaleRestriction (𝒰.f a) (Type u)).obj G :=
    finiteEtaleCopiesSheafIso (𝒰.X a) A ≪≫ eA.symm ≪≫
      (etaleSetPullbackRestrictionIso (𝒰.f a)).app G
  exact ⟨W, ⟨Functor.representableByEquiv.symm
    ((sheafToPresheaf (𝒰.X a).smallEtaleTopology (Type u)).mapIso e)⟩⟩

/-- On a quasi-compact base the ordinary local representers can be chosen on
a finite affine étale cover. No common cardinality of the models is required. -/
theorem IsEtaleFiniteLocallyConstantSet.exists_finite_affine_localRepresenters
    [CompactSpace X] (hG : IsEtaleFiniteLocallyConstantSet G) :
    ∃ 𝒱 : Scheme.AffineCover.{u} (show MorphismProperty Scheme.{u} from @Etale) X,
      Finite 𝒱.I₀ ∧ ∀ b : 𝒱.I₀, ∃ W : FiniteEtale (𝒱.cover.X b),
        Nonempty (((etalePostcompose (hf := 𝒱.map_prop b) (𝒱.cover.f b)).op ⋙ G.obj).RepresentableBy
          ((finiteEtaleToEtale (𝒱.cover.X b)).obj W)) := by
  obtain ⟨𝒰, h𝒰⟩ := hG
  obtain ⟨𝒱, e, hfinite, _, _, _, _⟩ :=
    Scheme.Cover.exists_finite_affine_etale_refinement 𝒰
  refine ⟨𝒱, hfinite, fun b => ?_⟩
  have : Etale (𝒱.cover.f b) := 𝒱.map_prop b
  obtain ⟨A, hA, ⟨eA⟩⟩ := h𝒰 (e.s₀ b)
  let ecomp : etaleSetPullback (𝒱.cover.f b) ≅
      etaleSetPullback (e.h₀ b ≫ 𝒰.f (e.s₀ b)) :=
    eqToIso (congrArg (fun k => etaleSetPullback k) (e.w₀ b).symm)
  let eModel : (etaleSetPullback (𝒱.cover.f b)).obj G ≅
      (constantSheaf (𝒱.cover.X b).smallEtaleTopology (Type u)).obj A :=
    ecomp.app G ≪≫ (etaleSetPullbackCompIso (e.h₀ b) (𝒰.f (e.s₀ b))).app G ≪≫
      (etaleSetPullback (e.h₀ b)).mapIso eA ≪≫
        (etaleSetPullbackConstantIso (e.h₀ b)).app A
  let W := finiteEtaleCopies (𝒱.cover.X b) A
  let eW : (finiteEtaleSheaf (𝒱.cover.X b)).obj W ≅
      (etaleRestriction (𝒱.cover.f b) (Type u)).obj G :=
    finiteEtaleCopiesSheafIso (𝒱.cover.X b) A ≪≫ eModel.symm ≪≫
      (etaleSetPullbackRestrictionIso (𝒱.cover.f b)).app G
  exact ⟨W, ⟨Functor.representableByEquiv.symm
    ((sheafToPresheaf (𝒱.cover.X b).smallEtaleTopology (Type u)).mapIso eW)⟩⟩

end EtaleCohomology
