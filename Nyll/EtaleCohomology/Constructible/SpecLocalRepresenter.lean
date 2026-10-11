/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleCohomology.Constructible.AffineLocalRepresenter
import Nyll.EtaleCohomology.Sites.EtaleRestriction
import Nyll.EtaleCohomology.Sites.BaseChange
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.MorphismProperty.OverAdjunction
import Mathlib.CategoryTheory.Yoneda
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

import Nyll.EtaleCohomology.Constructible.FiniteEtaleSheaf
import Nyll.EtaleCohomology.Constructible.FiniteLocallyConstantSet
import Nyll.SchemeTheory.FiniteEtale.Basic
import Mathlib.AlgebraicGeometry.Morphisms.AffineAnd
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties
import Mathlib.CategoryTheory.MorphismProperty.Comma
import Mathlib.CategoryTheory.Opposites
import Mathlib.RingTheory.RingHom.FaithfullyFlat

/-!
# Literal spectrum coordinates for a finite étale local representer

We replace an affine étale cover and its finite étale representing scheme by
the spectra of their global section rings. The fully faithful spectrum functor
supplies ring maps with these precise spectra. Restriction of the original
sheaf remains represented: the map/pullback adjunction transports the
representing equivalence, and an actual cartesian square identifies the
resulting pullback with the new spectrum.

The base ring is arbitrary; no field or noetherian hypothesis is used.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Limits Opposite

universe u

namespace EtaleCohomology

private def restrictionRepresentableByBaseChange {X Y Z : Scheme.{u}}
    (f : Y ⟶ X) (e : Z ⟶ Y) (f' : Z ⟶ X)
    [Etale f] [Etale e] [Etale f'] (he : f' = e ≫ f)
    (G : Sheaf X.smallEtaleTopology (Type u)) (W : Y.Etale)
    (h : ((etalePostcompose f).op ⋙ G.obj).RepresentableBy W) :
    ((etalePostcompose f').op ⋙ G.obj).RepresentableBy ((etaleBaseChange e).obj W) := by
  let c : etalePostcompose f' ≅ etalePostcompose e ⋙ etalePostcompose f :=
    MorphismProperty.Over.mapComp (P := show MorphismProperty Scheme.{u} from @Etale) ⊤
      (show Etale e from inferInstance) (show Etale f from inferInstance) f' he
  let r := ((etalePostcomposeBaseChangeAdjunction e).representableBy W).ofIso
    (Functor.isoWhiskerLeft (etalePostcompose e).op h.toIso)
  exact r.ofIso (Functor.isoWhiskerRight (NatIso.op c) G.obj)

/-- A finite locally constant sheaf on `Spec R` is represented after restriction
along a faithfully flat étale ring map `R → B` by a literal finite étale map
`Spec C → Spec B`. Both the ring properties and the representing equivalence
are transported from the constructed affine local representer. -/
theorem IsEtaleFiniteLocallyConstantSet.exists_spec_localRepresenter_faithfullyFlat
    {R : CommRingCat.{u}} {G : Sheaf (Spec R).smallEtaleTopology (Type u)}
    (hG : IsEtaleFiniteLocallyConstantSet G) :
    ∃ (B C : CommRingCat.{u}) (f : R →+* B) (g : B →+* C)
      (hf : Etale (Spec.map (CommRingCat.ofHom f)))
      (hg : IsFiniteEtale (Spec.map (CommRingCat.ofHom g))),
      f.FaithfullyFlat ∧ f.Etale ∧ g.FiniteEtale ∧
        Nonempty (((etalePostcompose (hf := hf) (Spec.map (CommRingCat.ofHom f))).op ⋙
          G.obj).RepresentableBy
            (MorphismProperty.Over.mk ⊤ (Spec.map (CommRingCat.ofHom g)) hg.toEtale)) := by
  obtain ⟨V, fV, hfV, hV, hsurj, W, ⟨hW⟩⟩ := hG.exists_affine_localRepresenter
  let _ : IsAffine V := hV
  let _ : Etale fV := hfV
  let _ : Surjective fV := hsurj
  have : IsAffine W.left := inferInstance
  let B : CommRingCat.{u} := Γ(V, ⊤)
  let C : CommRingCat.{u} := Γ(W.left, ⊤)
  let eV : V ≅ Spec B := V.isoSpec
  let eW : W.left ≅ Spec C := W.left.isoSpec
  let f : R ⟶ B := Spec.preimage (eV.inv ≫ fV)
  let g : B ⟶ C := Spec.preimage (eW.inv ≫ W.hom ≫ eV.hom)
  have hfEq : Spec.map f = eV.inv ≫ fV := Spec.map_preimage _
  have hgEq : Spec.map g = eW.inv ≫ W.hom ≫ eV.hom := Spec.map_preimage _
  have hf : Etale (Spec.map f) := by rw [hfEq]; infer_instance
  have hg : IsFiniteEtale (Spec.map g) := by
    rw [hgEq]
    exact ⟨⟩
  have hfSurj : Surjective (Spec.map f) := by rw [hfEq]; infer_instance
  have hfFaithful : f.hom.FaithfullyFlat :=
    (flat_and_surjective_SpecMap_iff f).mp ⟨inferInstance, hfSurj⟩
  have hfRing : f.hom.Etale :=
    (HasRingHomProperty.Spec_iff (P := @Etale)).mp hf
  have hgRing : g.hom.FiniteEtale :=
    (HasAffineProperty.SpecMap_iff_of_affineAnd (P := @IsFiniteEtale)
      inferInstance RingHom.FiniteEtale.respectsIso g).mp hg
  let W' : (Spec B).Etale := MorphismProperty.Over.mk ⊤ (Spec.map g) hg.toEtale
  have hpb : IsPullback eW.inv (Spec.map g) W.hom eV.inv := by
    apply IsPullback.of_horiz_isIso
    refine ⟨?_⟩
    exact (Iso.eq_comp_inv eV).mpr (by
      exact (Category.assoc eW.inv W.hom eV.hom).trans hgEq.symm)
  let wIso : W' ≅ (etaleBaseChange eV.inv).obj ((finiteEtaleToEtale V).obj W) :=
    MorphismProperty.Over.isoMk hpb.isoPullback hpb.isoPullback_hom_snd
  let h' := (restrictionRepresentableByBaseChange fV eV.inv (Spec.map f) hfEq G
    ((finiteEtaleToEtale V).obj W) hW).ofIsoObj wIso
  exact ⟨B, C, f.hom, g.hom, hf, hg, hfFaithful, hfRing, hgRing, ⟨h'⟩⟩

end EtaleCohomology
