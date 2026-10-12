/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.FiniteEtale.CompatibleStalkCoverSpreading
import Nyll.SchemeTheory.FiniteEtale.AffineEquivalence
import Nyll.SchemeTheory.Pi1.FiniteEtale.Basic
import Nyll.SchemeTheory.FiniteEtale.BaseChange.PullbackComposition
import Nyll.SchemeTheory.FiniteEtale.DVRUnramifiedExtension
import Nyll.SchemeTheory.FiniteEtale.TwoOpenGluing
import Nyll.SchemeTheory.LocalGeometry.GenericComplementPuncture
import Nyll.SchemeTheory.LocalGeometry.PuncturedDVR
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
import Mathlib.Topology.Sober

/-!
# Extending a cover across a DVR boundary point

At a generic point of the complement of an open, the actual stalk overlap
is the punctured local spectrum. If this local ring is a DVR, its puncture
is the spectrum of its fraction field. The unramified field-factor
condition therefore produces a finite etale cover of the full stalk,
with an isomorphism on the actual overlap.

Compatible spreading and two-open gluing extend the original cover to a
larger open containing the boundary point. In particular the result keeps
the original cover and its structure map; it does not assume a local model
or an overlap comparison. This is the codimension-one enlargement step
in the proof of Stacks Project, Lemma 58.31.2:
https://stacks.math.columbia.edu/tag/0H2W

The theorem treats a DVR boundary point. Extending simultaneously across
all such points and applying purity to the remaining regular boundary are
separate steps.
-/

noncomputable section

open CategoryTheory Limits TopologicalSpace

namespace AlgebraicGeometry.FiniteEtale

universe u

attribute [local instance] Ideal.Quotient.field
  finiteEtaleOverCategoryCoherence finiteEtaleHasPullbacksAlongCoherence
  finiteEtaleStableUnderBaseChangeAlongCoherence

/-- Over a locally Noetherian scheme, a finite etale cover of an open
extends across a generic boundary point whose stalk is regular and has
dimension one, provided that every actual generic field factor is
unramified over that stalk.

The fraction-field map to the original open is constructed from the
canonical stalk-overlap and puncture isomorphisms. The hypothesis is the
ramification-index and separable-residue-field condition on its coordinate
algebra, rather than an assumed cover extension. The domain and DVR
structures and retrocompactness of the open are derived from the original
regularity, dimension, and locally Noetherian hypotheses. -/
theorem exists_open_extension_at_regular_dimension_one_generic_boundary
    {X : Scheme.{u}} [IsLocallyNoetherian X] (U : X.Opens)
    (x : genericPoints {z : X // z ∉ U})
    [IsRegularLocalRing (X.presheaf.stalk x.1.1)]
    (hdim : ringKrullDim (X.presheaf.stalk x.1.1) = (1 : WithBot ℕ∞))
    (Y : FiniteEtale U.toScheme) :
    let R : CommRingCat.{u} := X.presheaf.stalk x.1.1
    let : IsDomain R := IsRegularLocalRing.isDomain R
    let : IsDiscreteValuationRing R :=
      SchemeTheory.isDiscreteValuationRing_of_isRegularLocalRing_dimension_one R hdim
    let K : Type u := FractionRing R
    let e : Limits.pullback (X.fromSpecStalk x.1.1) U.ι ≅ Spec (.of K) :=
      Scheme.genericComplementPuncturedSpectrumPullbackIso U x ≪≫
        Scheme.puncturedSpectrumIsoSpecFractionField R K
    let r : Spec (.of K) ⟶ U.toScheme :=
      e.inv ≫ Limits.pullback.snd (X.fromSpecStalk x.1.1) U.ι
    let A : CommAlgCat.FiniteEtale.{u} K :=
      (affineEquivalence (.of K)).functor.obj (Opposite.op ((pullback r).obj Y))
    let : Algebra R A := Algebra.compHom A (algebraMap R K)
    (∀ m : MaximalSpectrum A, SchemeTheory.IsUnramifiedOverDVR R (A ⧸ m.asIdeal)) →
      ∃ (N : X.Opens) (hUN : U ≤ N), x.1.1 ∈ N ∧
        ∃ Z : FiniteEtale N.toScheme,
          Nonempty ((pullback (X.homOfLE hUN)).obj Z ≅ Y) := by
  intro R hdomain hdvr K e r A hRA hunramified
  let q := X.fromSpecStalk x.1.1
  let g : Spec (.of K) ⟶ Spec R :=
    Spec.map (CommRingCat.ofHom (algebraMap R K))
  have hg : (Scheme.puncturedSpectrumIsoSpecFractionField R K).hom ≫ g =
      Scheme.puncturedSpectrumInclusion R :=
    Scheme.puncturedSpectrumIsoSpecFractionField_hom_SpecMap R K
  have he : Limits.pullback.fst q U.ι = e.hom ≫ g := by
    change Limits.pullback.fst (X.fromSpecStalk x.1.1) U.ι =
      ((Scheme.genericComplementPuncturedSpectrumPullbackIso U x).hom ≫
        (Scheme.puncturedSpectrumIsoSpecFractionField R K).hom) ≫ g
    rw [Category.assoc, hg,
      Scheme.genericComplementPuncturedSpectrumPullbackIso_hom_inclusion U x]
  have hr : Limits.pullback.snd q U.ι = e.hom ≫ r := by
    dsimp only [r]
    rw [← Category.assoc, e.hom_inv_id, Category.id_comp]
  obtain ⟨W, ⟨a⟩⟩ :=
    exists_dvr_extension_of_unramified_field_factors R K ((pullback r).obj Y) hunramified
  let cW : pullback (Limits.pullback.fst q U.ι) ≅ pullback g ⋙ pullback e.hom :=
    MorphismProperty.Over.pullbackComp (P := @IsFiniteEtale) (Q := ⊤)
      e.hom g (Limits.pullback.fst q U.ι) he
  let cY : pullback (Limits.pullback.snd q U.ι) ≅ pullback r ⋙ pullback e.hom :=
    MorphismProperty.Over.pullbackComp (P := @IsFiniteEtale) (Q := ⊤)
      e.hom r (Limits.pullback.snd q U.ι) hr
  let aOverlap : (pullback (Limits.pullback.fst q U.ι)).obj W ≅
      (pullback (Limits.pullback.snd q U.ι)).obj Y :=
    cW.app W ≪≫ (pullback e.hom).mapIso a ≪≫ (cY.app Y).symm
  obtain ⟨M, hxM, B, ⟨b⟩⟩ :=
    exists_compatible_open_cover_fromSpecStalk X U x.1.1 Y W aOverlap
  obtain ⟨Z, hZU, _⟩ := exists_glued_over_sup X U M Y B b.symm
  exact ⟨U ⊔ M, le_sup_left, (show M ≤ U ⊔ M from le_sup_right) hxM, Z, hZU⟩

end AlgebraicGeometry.FiniteEtale
