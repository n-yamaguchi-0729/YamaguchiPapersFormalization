/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.FiniteEtale.CompatibleStalkCoverSpreading
import Nyll.EtaleFundamentalGroups.Purity.CodimensionOneGenericFiber
import Nyll.SchemeTheory.FiniteEtale.AffineEquivalence
import Nyll.SchemeTheory.Pi1.FiniteEtale.Basic
import Nyll.SchemeTheory.FiniteEtale.BaseChange.PullbackComposition
import Nyll.SchemeTheory.FiniteEtale.DVRUnramifiedExtension
import Nyll.SchemeTheory.FiniteEtale.TwoOpenGluing
import Nyll.SchemeTheory.RingTheory.Ramification.Unramified.DVRNormalization
import Nyll.SchemeTheory.RingTheory.RegularLocalDimensionOne
import Nyll.SchemeTheory.RingTheory.RegularLocalDomain
import Mathlib.Algebra.Algebra.Tower
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Restrict
import Mathlib.AlgebraicGeometry.Stalk
import Mathlib.CategoryTheory.MorphismProperty.OverAdjunction
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Topology.Closure

/-!
# Enlarging an existing extension across a codimension-one boundary

Let a finite etale cover of a dense open U already extend to N. At a
missing regular point with one-dimensional stalk, its original generic
field factors over U still supply the needed DVR model.

The canonical fraction-field maps to U and N agree after inclusion.
Consequently the given restriction isomorphism identifies the actual
generic fibre of the cover on N with the original fibre on U. We use
the integral closure of that original fibre to construct the stalk
model, its comparison on the actual overlap with N, and a compatible
open enlargement by spreading and gluing.

Thus iteration of the codimension-one step in Stacks Project, Lemma
58.31.2 (https://stacks.math.columbia.edu/tag/0H2W), need not assume a
ramification comparison for the newly chosen cover or recompute the
field factors of that cover. All unramifiedness hypotheses below concern
the original cover on U.
-/

noncomputable section

open CategoryTheory Limits TopologicalSpace

namespace AlgebraicGeometry.FiniteEtale

universe u

attribute [local instance] Ideal.Quotient.field
  finiteEtaleOverCategoryCoherence finiteEtaleHasPullbacksAlongCoherence
  finiteEtaleStableUnderBaseChangeAlongCoherence

/-- Any existing extension of the original cover can be enlarged across a
regular codimension-one boundary point, using the unramified field factors
of the original cover. The actual restriction isomorphism supplies the
generic-fibre comparison; no ramification-transfer premise is added. -/
theorem exists_open_enlargement_at_regular_dimension_one_boundary
    {X : Scheme.{u}} [IsLocallyNoetherian X]
    (U N : X.Opens) (hU : Dense (U : Set X)) (hUN : U ≤ N)
    (x : X) (hxN : x ∉ N) [IsRegularLocalRing (X.presheaf.stalk x)]
    (hdim : ringKrullDim (X.presheaf.stalk x) = (1 : WithBot ℕ∞))
    (Y : FiniteEtale U.toScheme) (W : FiniteEtale N.toScheme)
    (a : (pullback (X.homOfLE hUN)).obj W ≅ Y) :
    let R : CommRingCat.{u} := X.presheaf.stalk x
    let : IsDomain R := IsRegularLocalRing.isDomain R
    let : IsDiscreteValuationRing R :=
      SchemeTheory.isDiscreteValuationRing_of_isRegularLocalRing_dimension_one R hdim
    let K : Type u := FractionRing R
    let rU : Spec (.of K) ⟶ U.toScheme :=
      Scheme.denseOpenDVRFractionFieldMap U hU x (fun hx ↦ hxN (hUN hx)) hdim
    let A : CommAlgCat.FiniteEtale.{u} K :=
      (affineEquivalence (.of K)).functor.obj (Opposite.op ((pullback rU).obj Y))
    let : Algebra R A := Algebra.compHom A (algebraMap R K)
    (∀ m : MaximalSpectrum A, SchemeTheory.IsUnramifiedOverDVR R (A ⧸ m.asIdeal)) →
      ∃ (M : X.Opens) (hNM : N ≤ M), x ∈ M ∧
        ∃ Z : FiniteEtale M.toScheme,
          Nonempty ((pullback (X.homOfLE hNM)).obj Z ≅ W) := by
  intro R hdomain hdvr K rU A hRA hunramified
  let q := X.fromSpecStalk x
  let g : Spec (.of K) ⟶ Spec R :=
    Spec.map (CommRingCat.ofHom (algebraMap R K))
  let eN : Limits.pullback q N.ι ≅ Spec (.of K) :=
    Scheme.denseOpenDVRPullbackIso N (Dense.mono hUN hU) x hxN hdim
  let rN : Spec (.of K) ⟶ N.toScheme :=
    Scheme.denseOpenDVRFractionFieldMap N (Dense.mono hUN hU) x hxN hdim
  have hgenericMaps : rN = rU ≫ X.homOfLE hUN :=
    (Scheme.denseOpenDVRFractionFieldMap_homOfLE U N hU hUN x hxN hdim).symm
  let cGeneric : pullback rN ≅
      pullback (X.homOfLE hUN) ⋙ pullback rU :=
    MorphismProperty.Over.pullbackComp (P := @IsFiniteEtale) (Q := ⊤)
      rU (X.homOfLE hUN) rN hgenericMaps
  let aGeneric : (pullback rN).obj W ≅ (pullback rU).obj Y :=
    cGeneric.app W ≪≫ (pullback rU).mapIso a
  obtain ⟨L, ⟨aL⟩⟩ :=
    exists_dvr_extension_of_unramified_field_factors R K ((pullback rU).obj Y)
      hunramified
  have heN : Limits.pullback.fst q N.ι = eN.hom ≫ g :=
    (Scheme.denseOpenDVRPullbackIso_hom_SpecMap N (Dense.mono hUN hU) x hxN hdim).symm
  have hrN : Limits.pullback.snd q N.ι = eN.hom ≫ rN := by
    change Limits.pullback.snd q N.ι =
      eN.hom ≫ (eN.inv ≫ Limits.pullback.snd q N.ι)
    rw [← Category.assoc, eN.hom_inv_id, Category.id_comp]
  let cL : pullback (Limits.pullback.fst q N.ι) ≅
      pullback g ⋙ pullback eN.hom :=
    MorphismProperty.Over.pullbackComp (P := @IsFiniteEtale) (Q := ⊤)
      eN.hom g (Limits.pullback.fst q N.ι) heN
  let cW : pullback (Limits.pullback.snd q N.ι) ≅
      pullback rN ⋙ pullback eN.hom :=
    MorphismProperty.Over.pullbackComp (P := @IsFiniteEtale) (Q := ⊤)
      eN.hom rN (Limits.pullback.snd q N.ι) hrN
  let aOverlap : (pullback (Limits.pullback.fst q N.ι)).obj L ≅
      (pullback (Limits.pullback.snd q N.ι)).obj W :=
    cL.app L ≪≫ (pullback eN.hom).mapIso (aL ≪≫ aGeneric.symm) ≪≫
      (cW.app W).symm
  obtain ⟨V, hxV, B, ⟨b⟩⟩ :=
    exists_compatible_open_cover_fromSpecStalk X N x W L aOverlap
  obtain ⟨Z, hZN, _⟩ := exists_glued_over_sup X N V W B b.symm
  exact ⟨N ⊔ V, le_sup_left, (show V ≤ N ⊔ V from le_sup_right) hxV, Z, hZN⟩

end AlgebraicGeometry.FiniteEtale
