/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Purity.PuncturedHypersurfaceGerms
import Nyll.EtaleFundamentalGroups.Purity.PuncturedHypersurfaceNeighborhoodDiagram
import Nyll.EtaleFundamentalGroups.Purity.PuncturedSpectrumQuotient
import Nyll.EtaleFundamentalGroups.FiniteEtale.InverseLimitModels
import Nyll.EtaleFundamentalGroups.FiniteEtale.InverseLimitStages
import Nyll.SchemeTheory.Pi1.FiniteEtale.Basic
import Nyll.SchemeTheory.FiniteEtale.DensePullback
import Nyll.SchemeTheory.FiniteEtale.BaseChange.PullbackComposition
import Nyll.SchemeTheory.LocalGeometry.PuncturedSpectrum
import Nyll.SchemeTheory.RingTheory.RegularLocalDomain
import Mathlib.CategoryTheory.Functor.Category
import Mathlib.CategoryTheory.Functor.FullyFaithful
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
import Mathlib.CategoryTheory.MorphismProperty.OverAdjunction
import Mathlib.CategoryTheory.Whiskering

/-!
# Restriction of neighbourhood germs to the actual quotient puncture

The target in Stacks Project, Lemma 58.22.1 is the punctured spectrum of
`R / (f)`. The previously constructed neighbourhood cone uses the pullback
of `Spec (R / (f))` to the puncture of `Spec R`. The cartesian square of the
actual quotient morphism gives an isomorphism between these schemes,
compatible with both projections.

Base change through that isomorphism gives the restriction functor with
the original target. Its restriction to each stage is naturally the usual
pullback along the actual map from the quotient puncture. Faithfulness is
inherited from the proved geometric shrinking argument, without a new
faithfulness or comparison hypothesis.

Source: https://stacks.math.columbia.edu/tag/0BLN
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicCurves.Foundations.CommutativeAlgebra.Proofs.IsRegularLocalRing_isDomain
open W2RLR.No4PatchingCore (isLocalRing_quotient_span_singleton)

namespace AlgebraicGeometry.FiniteEtale.PuncturedHypersurface

universe u

attribute [local instance] finiteEtaleOverCategoryCoherence
  finiteEtaleHasPullbacksAlongCoherence finiteEtaleStableUnderBaseChangeAlongCoherence

variable (R : Type u) [CommRing R] [IsLocalRing R] (f : R)
  (hf : f ∈ IsLocalRing.maximalIdeal R)

/-- The punctured spectrum of the actual quotient is the hypersurface
pullback used in the neighbourhood cone. -/
def quotientPunctureIso :
    let : IsLocalRing (R ⧸ Ideal.span {f}) :=
      isLocalRing_quotient_span_singleton (R := R) (x := f) hf
    Scheme.puncturedSpectrum (R ⧸ Ideal.span {f}) ≅ puncture R f := by
  intro hLocal
  exact (Scheme.puncturedSpectrumQuotientMorphism_isPullback R (Ideal.span {f})
    ((IsLocalRing.maximalIdeal R).span_singleton_le_iff_mem.mpr hf)).isoPullback

/-- The comparison is over the original punctured local spectrum. -/
theorem quotientPunctureIso_hom_fst :
    let : IsLocalRing (R ⧸ Ideal.span {f}) :=
      isLocalRing_quotient_span_singleton (R := R) (x := f) hf
    (quotientPunctureIso R f hf).hom ≫
        pullback.fst (Scheme.puncturedSpectrumOpen R).ι (hypersurfaceMap R f) =
      Scheme.puncturedSpectrumQuotientMorphism R (Ideal.span {f})
        ((IsLocalRing.maximalIdeal R).span_singleton_le_iff_mem.mpr hf) := by
  intro hLocal
  exact (Scheme.puncturedSpectrumQuotientMorphism_isPullback R (Ideal.span {f})
    ((IsLocalRing.maximalIdeal R).span_singleton_le_iff_mem.mpr hf)).isoPullback_hom_fst

/-- The comparison also preserves the inclusion into the quotient spectrum. -/
theorem quotientPunctureIso_hom_snd :
    let : IsLocalRing (R ⧸ Ideal.span {f}) :=
      isLocalRing_quotient_span_singleton (R := R) (x := f) hf
    (quotientPunctureIso R f hf).hom ≫
        pullback.snd (Scheme.puncturedSpectrumOpen R).ι (hypersurfaceMap R f) =
      Scheme.puncturedSpectrumInclusion (R ⧸ Ideal.span {f}) := by
  intro hLocal
  exact (Scheme.puncturedSpectrumQuotientMorphism_isPullback R (Ideal.span {f})
    ((IsLocalRing.maximalIdeal R).span_singleton_le_iff_mem.mpr hf)).isoPullback_hom_snd

/-- Restriction of neighbourhood germs to the literal punctured spectrum
of the quotient by the original equation. -/
def restrictionToQuotientPuncture :
    let : IsLocalRing (R ⧸ Ideal.span {f}) :=
      isLocalRing_quotient_span_singleton (R := R) (x := f) hf
    (InverseLimitModel.cartesian (diagram R f)).Localization ⥤
      FiniteEtale (Scheme.puncturedSpectrum (R ⧸ Ideal.span {f})) := by
  intro hLocal
  exact InverseLimitModel.localizedBaseChange (diagram R f) (cone R f) ⋙
    FiniteEtale.pullback (quotientPunctureIso R f hf).hom

/-- On each actual neighbourhood, the germ restriction agrees naturally
with pullback along the map from the original quotient puncture. -/
def stageRestrictionToQuotientPunctureIso
    (i : (OrderDual (Neighborhood R f))ᵒᵖ) :
    let : IsLocalRing (R ⧸ Ideal.span {f}) :=
      isLocalRing_quotient_span_singleton (R := R) (x := f) hf
    InverseLimitModel.localizedStageInclusion (diagram R f) i ⋙
        restrictionToQuotientPuncture R f hf ≅
      FiniteEtale.pullback
        ((quotientPunctureIso R f hf).hom ≫ projection R f i.unop) := by
  intro hLocal
  let F : FiniteEtale ((diagram R f).obj i) ⥤
      (InverseLimitModel.cartesian (diagram R f)).Localization :=
    InverseLimitModel.localizedStageInclusion (diagram R f) i
  let G : (InverseLimitModel.cartesian (diagram R f)).Localization ⥤
      FiniteEtale (puncture R f) :=
    InverseLimitModel.localizedBaseChange (diagram R f) (cone R f)
  let q : Scheme.puncturedSpectrum (R ⧸ Ideal.span {f}) ⟶ puncture R f :=
    (quotientPunctureIso R f hf).hom
  have hlocal :
      (InverseLimitModel.cartesian (diagram R f)).Q ⋙ G =
        InverseLimitModel.baseChange (diagram R f) (cone R f) :=
    InverseLimitModel.q_comp_localizedBaseChange (diagram R f) (cone R f)
  have hstageBase :
      InverseLimitModel.stageInclusion (diagram R f) i ⋙
          InverseLimitModel.baseChange (diagram R f) (cone R f) =
        FiniteEtale.pullback (projection R f i.unop) :=
    InverseLimitModel.stageInclusion_comp_baseChange (diagram R f) (cone R f) i
  have hstage : F ⋙ G = FiniteEtale.pullback (projection R f i.unop) :=
    (Functor.assoc (InverseLimitModel.stageInclusion (diagram R f) i)
      (InverseLimitModel.cartesian (diagram R f)).Q G).trans
        ((congrArg (fun H : InverseLimitModel (diagram R f) ⥤ FiniteEtale (puncture R f) ↦
          InverseLimitModel.stageInclusion (diagram R f) i ⋙ H) hlocal).trans hstageBase)
  let ePullback : FiniteEtale.pullback (q ≫ projection R f i.unop) ≅
      FiniteEtale.pullback (projection R f i.unop) ⋙ FiniteEtale.pullback q :=
    MorphismProperty.Over.pullbackComp (P := @IsFiniteEtale) (Q := ⊤)
      q (projection R f i.unop) (q ≫ projection R f i.unop) rfl
  exact (Functor.associator F G (FiniteEtale.pullback q)).symm ≪≫
    Functor.isoWhiskerRight (eqToIso hstage) (FiniteEtale.pullback q) ≪≫
    ePullback.symm

/-- The restriction from all neighbourhood germs to the punctured spectrum
of `R / (f)` is faithful under the original local Noetherian hypotheses of
Stacks 58.22.1. The concrete target comparison is constructed above. -/
theorem restrictionToQuotientPuncture_faithful [IsNoetherianRing R] :
    let : IsLocalRing (R ⧸ Ideal.span {f}) :=
      isLocalRing_quotient_span_singleton (R := R) (x := f) hf
    (restrictionToQuotientPuncture R f hf).Faithful := by
  intro hLocal
  let F : (InverseLimitModel.cartesian (diagram R f)).Localization ⥤
      FiniteEtale (puncture R f) :=
    InverseLimitModel.localizedBaseChange (diagram R f) (cone R f)
  let G : FiniteEtale (puncture R f) ⥤
      FiniteEtale (Scheme.puncturedSpectrum (R ⧸ Ideal.span {f})) :=
    FiniteEtale.pullback (quotientPunctureIso R f hf).hom
  change (F ⋙ G).Faithful
  have hF : F.Faithful := restriction_faithful R f hf
  have hG : G.Faithful :=
    pullback_faithful_of_isDominant (quotientPunctureIso R f hf).hom
  exact Functor.Faithful.comp F G

end AlgebraicGeometry.FiniteEtale.PuncturedHypersurface
