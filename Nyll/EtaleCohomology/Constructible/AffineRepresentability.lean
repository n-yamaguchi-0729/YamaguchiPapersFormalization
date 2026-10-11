/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleCohomology.Constructible.SpecLocalRepresenter
import Nyll.EtaleCohomology.Constructible.AffineRepresenterCoaction
import Nyll.EtaleCohomology.Constructible.RepresenterDescent
import Nyll.EtaleCohomology.Constructible.RepresenterIso
import Nyll.EtaleCohomology.Constructible.FiniteEtaleSheaf
import Nyll.EtaleCohomology.Constructible.FiniteLocallyConstantSet
import Nyll.EtaleCohomology.Constructible.RepresenterAction
import Nyll.EtaleCohomology.Sites.EtaleRestriction
import Nyll.SchemeTheory.Descent.AffineActionCoordinates
import Nyll.SchemeTheory.Descent.AffineAlgebraCoaction
import Nyll.SchemeTheory.Descent.AffineCocycle
import Nyll.SchemeTheory.Descent.AlgebraCoaction
import Nyll.SchemeTheory.Descent.EffectiveAffine
import Nyll.SchemeTheory.Descent.FaithfullyFlatAlgebra
import Nyll.SchemeTheory.FiniteEtale.Basic
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Sites.Etale
import Mathlib.CategoryTheory.MorphismProperty.Comma
import Mathlib.CategoryTheory.Yoneda
import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Finite étale representability on affine schemes

A finite locally constant sheaf has a finite étale local representer over a
faithfully flat affine étale cover. Its universal section constructs the full
algebra descent data. The invariant algebra gives a finite étale scheme with
the required cartesian comparison. Descending the universal section identifies
its represented sheaf with the original sheaf.

The base is any affine scheme: no ground field, noetherianity, or connectedness
is required.
-/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits Algebra.Descent
open scoped TensorProduct

namespace EtaleCohomology

/-- A finite locally constant sheaf on an arbitrary ring's spectrum is
represented by a finite étale scheme, constructed by effective descent. -/
theorem IsEtaleFiniteLocallyConstantSet.exists_spec_representer
    {R : CommRingCat.{u}} {G : Sheaf (Spec R).smallEtaleTopology (Type u)}
    (hG : IsEtaleFiniteLocallyConstantSet G) :
    ∃ Z : FiniteEtale (Spec R),
      Nonempty (G.obj.RepresentableBy ((finiteEtaleToEtale (Spec R)).obj Z)) := by
  obtain ⟨B, C, f, g, hf, hg, hff, _, hgRing, ⟨h⟩⟩ :=
    hG.exists_spec_localRepresenter_faithfullyFlat
  let : Algebra B C := g.toAlgebra
  let : Algebra R B := f.toAlgebra
  let : Algebra R C := Algebra.compHom C f
  have : IsScalarTower R B C := IsScalarTower.of_compHom R B C
  have : Etale (Spec.map (CommRingCat.ofHom f)) := hf
  have : IsFiniteEtale (Spec.map (CommRingCat.ofHom g)) := hg
  have : Surjective (Spec.map (CommRingCat.ofHom f)) :=
    ((flat_and_surjective_SpecMap_iff (CommRingCat.ofHom f)).mpr hff).2
  have : Algebra.FiniteEtale B C := (RingHom.finiteEtale_algebraMap_iff).mp hgRing
  let W : (Spec B).Etale := MorphismProperty.Over.mk ⊤
    (Spec.map (CommRingCat.ofHom g)) hg.toEtale
  let θ : C ⊗[R] B ≃ₐ[B] B ⊗[R] C := affineRepresenterAlgEquiv R B C G h
  have hd := affineRepresenterAlgEquiv_diagonal R B C G h
  have ht := affineRepresenterAlgEquiv_cocycle R B C G h
  let A := Algebra.FaithfullyFlatDescent.invariants f C (tensorCoaction R B C θ)
  let zmap : Spec (.of A) ⟶ Spec R := Spec.map (CommRingCat.ofHom (algebraMap R A))
  have hz : IsFiniteEtale zmap := tensorDescent_isFiniteEtale f C hff θ hd ht
  let Zfin : FiniteEtale (Spec R) := MorphismProperty.Over.mk ⊤ zmap hz
  let Z := (finiteEtaleToEtale (Spec R)).obj Zfin
  let q₀ : Spec C ⟶ Z.left := Spec.map (CommRingCat.ofHom A.val.toRingHom)
  have H : IsPullback W.hom q₀ (Spec.map (CommRingCat.ofHom f)) Z.hom :=
    tensorDescent_isPullback f C hff θ hd ht
  let q : (etalePostcompose (Spec.map (CommRingCat.ofHom f))).obj W ⟶ Z :=
    MorphismProperty.Over.homMk q₀ H.w.symm trivial
  have hi := Algebra.FaithfullyFlatDescent.invariantsSpec_action_invariant f C
    (tensorCoaction R B C θ)
  have hi' :
      pullbackActionCongr (Spec.map (CommRingCat.ofHom f)) W.hom
          (Spec.map (CommRingCat.ofHom (algebraMap R C))) (specMap_tower R B C)
          (representerAction (Spec.map (CommRingCat.ofHom f)) G W h) ≫ q₀ =
        pullback.snd (Spec.map (CommRingCat.ofHom f))
          (Spec.map (CommRingCat.ofHom (algebraMap R C))) ≫ q₀ := by
    exact (congrArg (fun a => a ≫ q₀)
      (affineRepresenterOverlapIso_action R B C G h).symm).trans
        ((congrArg (fun a => a ≫ q₀) (affineOverlapAction_eq_coaction R B C _
          (affineRepresenterOverlapIso_base R B C G h))).trans hi)
  have ha : representerAction (Spec.map (CommRingCat.ofHom f)) G W h ≫ q.left =
      pullback.snd (Spec.map (CommRingCat.ofHom f))
        (W.hom ≫ Spec.map (CommRingCat.ofHom f)) ≫ q.left :=
    (pullbackActionCongr_invariant_iff (Spec.map (CommRingCat.ofHom f)) W.hom
      (Spec.map (CommRingCat.ofHom (algebraMap R C))) (specMap_tower R B C)
      (representerAction (Spec.map (CommRingCat.ofHom f)) G W h) q₀).mp hi'
  exact ⟨Zfin, ⟨representableBy_of_cartesian_localRepresenter
    (Spec.map (CommRingCat.ofHom f)) G W h Z q H ha⟩⟩

/-- Every finite locally constant sheaf on an affine scheme is represented by
a finite étale scheme. The affine chart is removed using its actual isomorphism. -/
theorem IsEtaleFiniteLocallyConstantSet.exists_affine_representer
    {X : Scheme.{u}} [IsAffine X] {G : Sheaf X.smallEtaleTopology (Type u)}
    (hG : IsEtaleFiniteLocallyConstantSet G) :
    ∃ Z : FiniteEtale X, Nonempty (G.obj.RepresentableBy ((finiteEtaleToEtale X).obj Z)) := by
  let G' := (etaleRestriction X.isoSpec.inv (Type u)).obj G
  have hG' : IsEtaleFiniteLocallyConstantSet G' :=
    (hG.pullback X.isoSpec.inv).of_iso ((etaleSetPullbackRestrictionIso X.isoSpec.inv).app G)
  obtain ⟨W, ⟨hW⟩⟩ := hG'.exists_spec_representer
  exact ⟨(FiniteEtale.pullback X.isoSpec.hom).obj W,
    ⟨finiteEtaleRepresentableBy_of_isoRestriction X.isoSpec.symm G W hW⟩⟩

end EtaleCohomology
