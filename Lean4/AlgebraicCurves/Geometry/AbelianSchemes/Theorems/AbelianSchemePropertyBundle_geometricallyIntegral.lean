/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_GoodReductionJacobian_AbelianSchemePropertyBundle_geometricallyIntegral.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import AlgebraicCurves.Geometry.AbelianSchemes.AbelianSchemePropertyBundle
import AlgebraicCurves.Geometry.Schemes.isIntegral_of_isLocallyNoetherian_of_connectedSpace_of_forall_isDomain_stalk
import AlgebraicCurves.Geometry.Schemes.Smooth_isRegularLocalRing_stalk
import SchemeTheory.RingTheory.RegularLocalDomain
import AlgebraicCurves.Geometry.Curves.geometricallyIntegral_of_isAlgClosed
import AlgebraicCurves.Geometry.Curves.GeometricallyIrreducible_geometricallyConnected
import AlgebraicCurves.Geometry.Curves.GeometricallyConnected_descendsAlong_surjective

/-!
# Abelian Scheme Property Bundle geometrically Integral
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.AbelianSchemes.Theorems.Proofs
namespace AbelianSchemePropertyBundle_geometricallyIntegral

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

namespace S17A0

theorem isIntegral_of_smooth_of_connectedSpace {K : Type u} [Field K] {X : Scheme.{u}}
    (t : X ⟶ Spec (CommRingCat.of K)) [Smooth t] [ConnectedSpace X] : IsIntegral X := by
  have : LocallyOfFiniteType t := inferInstance
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian t
  exact
    AlgebraicGeometry.isIntegral_of_isLocallyNoetherian_of_connectedSpace_of_forall_isDomain_stalk
    X fun x => by
      have := AlgebraicGeometry.Smooth.isRegularLocalRing_stalk (f := t) x
      exact IsRegularLocalRing.isDomain _

scoped instance subsingleton_spec_field (K : Type u) [Field K] :
    Subsingleton ↥(Spec (CommRingCat.of K)) :=
  inferInstanceAs (Subsingleton (PrimeSpectrum K))

scoped instance nonempty_spec_field (K : Type u) [Field K] :
    Nonempty ↥(Spec (CommRingCat.of K)) :=
  inferInstanceAs (Nonempty (PrimeSpectrum K))

section Stacks04KV

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of k))
  (e : Spec (CommRingCat.of k) ⟶ A) (he : e ≫ f = 𝟙 _)

/-- The morphism of spectra induced by the algebra map from the base field to its extension. -/
noncomputable abbrev bc (k K : Type u) [Field k] [Field K] [Algebra k K] :
    Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of k) :=
  Spec.map (CommRingCat.ofHom (algebraMap k K))

/-- The section after base change to `K`, obtained by lifting the original section
through the pullback. -/
noncomputable def pt' : Spec (CommRingCat.of K) ⟶ pullback f (bc k K) :=
  pullback.lift (bc k K ≫ e) (𝟙 _) (by rw [Category.assoc, he, Category.comp_id, Category.id_comp])

@[scoped simp] theorem pt'_fst : pt' f e he ≫ pullback.fst f (bc k K) = bc k K ≫ e :=
  pullback.lift_fst _ _ _
include he in
theorem subsingleton_pullback_section :
    Subsingleton ↥(pullback e (pullback.fst f (bc k K))) := by
  let i₁ : pullback e (pullback.fst f (bc k K)) ≅ pullback (e ≫ f) (bc k K) :=
    pullbackRightPullbackFstIso f (bc k K) e
  let i₂ : pullback (e ≫ f) (bc k K) ≅ pullback (𝟙 _) (bc k K) := pullback.congrHom he rfl
  have : IsIso (pullback.snd (𝟙 (Spec (CommRingCat.of k))) (bc k K)) := inferInstance
  let j : pullback e (pullback.fst f (bc k K)) ⟶ Spec (CommRingCat.of K) :=
    i₁.hom ≫ i₂.hom ≫ pullback.snd (𝟙 _) (bc k K)
  have : IsIso j := by unfold j; infer_instance
  exact (Scheme.Hom.homeomorph j).subsingleton

theorem eq_pt'_of_fst_eq (v : ↥(pullback f (bc k K)))
    (hv : pullback.fst f (bc k K) v = e (IsLocalRing.closedPoint k)) :
    v = pt' f e he (IsLocalRing.closedPoint K) := by
  have hrange : Set.range (pullback.snd e (pullback.fst f (bc k K))) =
      pullback.fst f (bc k K) ⁻¹' Set.range e := Scheme.Pullback.range_snd _ _
  have hv' : v ∈ Set.range (pullback.snd e (pullback.fst f (bc k K))) := by
    rw [hrange]; exact ⟨_, hv.symm⟩
  have hp' : pt' f e he (IsLocalRing.closedPoint K) ∈
      Set.range (pullback.snd e (pullback.fst f (bc k K))) := by
    rw [hrange]
    refine ⟨(bc k K) (IsLocalRing.closedPoint K), ?_⟩
    exact (congrArg
      (fun φ : Spec (CommRingCat.of K) ⟶ A => φ (IsLocalRing.closedPoint K))
      (pt'_fst f e he (K := K))).symm
  obtain ⟨z, rfl⟩ := hv'
  obtain ⟨z', hz'⟩ := hp'
  have := subsingleton_pullback_section f e he (K := K)
  rw [← hz', Subsingleton.elim z z']
include he in
theorem connectedSpace_pullback [Algebra.IsAlgebraic k K] [ConnectedSpace A] :
    ConnectedSpace ↥(pullback f (bc k K)) := by
  have : UniversallyOpen (bc k K) := inferInstance
  have hopen : IsOpenMap (pullback.fst f (bc k K)) := (pullback.fst f (bc k K)).isOpenMap
  have : IsIntegralHom (bc k K) := by
    rw [IsIntegralHom.SpecMap_iff, CommRingCat.hom_ofHom, algebraMap_isIntegral_iff]
    exact Algebra.isAlgebraic_iff_isIntegral.mp inferInstance
  have hbc : MorphismProperty.IsStableUnderBaseChange
      (@UniversallyClosed : MorphismProperty Scheme.{u}) :=
    universallyClosed_isStableUnderBaseChange
  have : UniversallyClosed (pullback.fst f (bc k K)) :=
    hbc.of_isPullback (IsPullback.of_hasPullback f (bc k K)).flip inferInstance
  have hclosed : IsClosedMap (pullback.fst f (bc k K)) := (pullback.fst f (bc k K)).isClosedMap
  obtain ⟨x₁, hx₁def⟩ : ∃ x : ↥(pullback f (bc k K)), x = pt' f e he (IsLocalRing.closedPoint K) :=
    ⟨_, rfl⟩
  have key : ∀ s : Set ↥(pullback f (bc k K)), IsClopen s → x₁ ∈ s → s = Set.univ := by
    intro s hs hxs
    have himg : IsClopen (pullback.fst f (bc k K) '' sᶜ) :=
      ⟨hclosed _ hs.compl.isClosed, hopen _ hs.compl.isOpen⟩
    rcases isClopen_iff.mp himg with h0 | h1
    · exact Set.compl_empty_iff.mp (Set.image_eq_empty.mp h0)
    · exfalso
      have hmem : e (IsLocalRing.closedPoint k) ∈ pullback.fst f (bc k K) '' sᶜ :=
        h1 ▸ Set.mem_univ _
      obtain ⟨v, hvs, hv⟩ := hmem
      have hv' : v = x₁ := hx₁def ▸ eq_pt'_of_fst_eq f e he v hv
      rw [hv'] at hvs
      exact hvs hxs
  rw [connectedSpace_iff_clopen]
  refine ⟨⟨x₁⟩, fun s hs => ?_⟩
  by_cases hxs : x₁ ∈ s
  · exact Or.inr (key s hs hxs)
  · exact Or.inl (Set.compl_univ_iff.mp (key sᶜ hs.compl hxs))

end Stacks04KV

end S17A0

open S17A0 in
theorem _root_.GoodReductionJacobian.AbelianSchemePropertyBundle.geometricallyIntegral
    {k : Type u} [Field k] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of k)}
    (hA : AbelianSchemePropertyBundle k f) : GeometricallyIntegral f := by
  have : Smooth f := hA.smooth
  obtain ⟨L⟩ := hA.hasGroupLaw
  let e : Spec (CommRingCat.of k) ⟶ A := (L.one (𝟙 _)).1
  have he : e ≫ f = 𝟙 _ := (L.one (𝟙 _)).2
  have : ConnectedSpace ↥A := by
    rw [connectedSpace_iff_univ]
    convert hA.connectedFibres (IsLocalRing.closedPoint k) using 1
    exact (Set.eq_univ_of_forall fun a =>
      Set.mem_preimage.mpr (Set.mem_singleton_iff.mpr (Subsingleton.elim _ _))).symm
  let K := AlgebraicClosure k
  have : ConnectedSpace ↥(pullback f (bc k K)) := connectedSpace_pullback f e he
  have hbcSmooth : MorphismProperty.IsStableUnderBaseChange
      (@Smooth : MorphismProperty Scheme.{u}) := smooth_isStableUnderBaseChange
  have : Smooth (pullback.snd f (bc k K)) :=
    hbcSmooth.of_isPullback (IsPullback.of_hasPullback f (bc k K)) hA.smooth
  have : IsIntegral (pullback f (bc k K)) :=
    isIntegral_of_smooth_of_connectedSpace (pullback.snd f (bc k K))
  have : LocallyOfFiniteType (pullback.snd f (bc k K)) := inferInstance
  have : GeometricallyIntegral (pullback.snd f (bc k K)) :=
    AlgebraicGeometry.geometricallyIntegral_of_isAlgClosed _
  have : GeometricallyConnected (pullback.snd f (bc k K)) :=
    AlgebraicGeometry.GeometricallyIrreducible.geometricallyConnected _
  have : MorphismProperty.DescendsAlong (@GeometricallyConnected : MorphismProperty Scheme.{u})
      @Surjective :=
    AlgebraicGeometry.GeometricallyConnected.descendsAlong_surjective
  have hsurj : Surjective (bc k K) := ⟨Function.surjective_to_subsingleton _⟩
  have : GeometricallyConnected f :=
    MorphismProperty.of_pullback_snd_of_descendsAlong (P := @GeometricallyConnected)
      (Q := @Surjective) hsurj ‹_›
  refine ⟨fun K' _ y Z fst snd h => ?_⟩
  have : Smooth (pullback.snd f y) :=
    hbcSmooth.of_isPullback (IsPullback.of_hasPullback f y) hA.smooth
  have : ConnectedSpace ↥(pullback f y) :=
    GeometricallyConnected.connectedSpace_of_subsingleton (pullback.snd f y)
  have : IsIntegral (pullback f y) := isIntegral_of_smooth_of_connectedSpace (pullback.snd f y)
  exact IsIntegral.of_isIso h.isoPullback.inv
end AbelianSchemePropertyBundle_geometricallyIntegral
end AlgebraicCurves.Geometry.AbelianSchemes.Theorems.Proofs
end ProofImplementation
