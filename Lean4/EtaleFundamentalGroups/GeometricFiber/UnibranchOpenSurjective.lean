/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.GeometricFiber.OpenImmersionSurjective
import EtaleFundamentalGroups.Purity.LocallyConnectedRestriction
import EtaleFundamentalGroups.StrictHenselian.GeometricStalkUnibranchCriterion
import EtaleFundamentalGroups.StrictHenselian.GeometricStalkFlat
import SchemeTheory.LocalGeometry.PuncturedSpectrum
import Mathlib.AlgebraicGeometry.Stalk
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.RingTheory.RingHom.FaithfullyFlat
import Mathlib.Topology.Sober

/-!
# Nonempty opens of irreducible geometrically unibranch schemes

The local hypothesis uses the original definition through normalization of
each stalk's reduction. Its actual geometric stalk has irreducible spectrum.
Outside the nonempty open, the generic point lifts to a nonclosed prime of
the ordinary stalk; faithful flatness lifts that point to the strict stalk.
Thus the punctured strict stalk is nonempty and irreducible, hence connected.

The original finite-component local-connectedness criterion gives fully
faithful finite étale restriction, and the actual fiber comparison gives
surjectivity of the canonical fundamental group map. The scheme is arbitrary:
normality, reducedness, Noetherianity, and quasi-compactness are not assumed.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CategoryTheory.PreGaloisCategory TopologicalSpace
open EtaleFundamentalGroups.StrictHenselian

universe u

namespace AlgebraicGeometry.FiniteEtale

private theorem puncturedGeometricStalk_nonempty_of_nonempty_open_complement
    {X : Scheme.{u}} [IrreducibleSpace X]
    (U : X.Opens) (hU : (U : Set X).Nonempty) (x : X) (hx : x ∉ U)
    {Ω : Type u} [Field Ω]
    (φ : X.presheaf.stalk x →+* Ω) [IsLocalHom φ] :
    Nonempty (Scheme.puncturedSpectrum
      (geometricStalk (Spec.map (CommRingCat.ofHom φ)))) := by
  have hηU : genericPoint X ∈ U :=
    ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr
      (by simpa only [Set.univ_inter] using hU)
  have hηx : genericPoint X ≠ x := by
    intro heq
    exact hx (heq ▸ hηU)
  have hηrange : genericPoint X ∈ Set.range (X.fromSpecStalk x) := by
    rw [Scheme.range_fromSpecStalk]
    exact genericPoint_specializes x
  obtain ⟨p, hp⟩ := hηrange
  have hpne : p ≠ IsLocalRing.closedPoint (X.presheaf.stalk x) := by
    intro heq
    apply hηx
    rw [heq, Scheme.fromSpecStalk_closedPoint] at hp
    exact hp.symm
  have hsurj : Function.Surjective (PrimeSpectrum.comap (geometricStalkStructureMap φ)) :=
    (RingHom.FaithfullyFlat.iff_flat_and_comap_surjective.mp
      (geometricStalkStructureMap_faithfullyFlat φ)).2
  obtain ⟨q, hq⟩ := hsurj p
  refine ⟨⟨q, ?_⟩⟩
  change q ≠ IsLocalRing.closedPoint (geometricStalk (Spec.map (CommRingCat.ofHom φ)))
  intro heq
  apply hpne
  rw [← hq, heq]
  exact IsLocalRing.comap_closedPoint (geometricStalkStructureMap φ)

/-- Restriction to any nonempty open of an irreducible geometrically
unibranch scheme is fully faithful on the actual finite étale categories. -/
def nonemptyOpenPullbackFullyFaithful_of_geometricallyUnibranch
    {X : Scheme.{u}} [IrreducibleSpace X]
    (hX : ∀ x : X, IsLocalRing.IsGeometricallyUnibranch (X.presheaf.stalk x))
    (U : X.Opens) (hU : (U : Set X).Nonempty) :
    (FiniteEtale.pullback U.ι).FullyFaithful := by
  have hfin : ∀ A : X.Opens, IsCompact (A : Set X) →
      (irreducibleComponents A.toScheme).Finite := by
    intro A _
    apply (Set.finite_singleton (Set.univ : Set A.toScheme)).subset
    intro Z hZ
    have : Nonempty A.toScheme := by
      obtain ⟨z, _⟩ := hZ.1.nonempty
      exact ⟨z⟩
    have : IrreducibleSpace A.toScheme := A.ι.isOpenEmbedding.irreducibleSpace
    rw [irreducibleComponents_eq_singleton] at hZ
    exact hZ
  let Ω : X → Type u := fun x => AlgebraicClosure (IsLocalRing.ResidueField (X.presheaf.stalk x))
  let φ : ∀ x : X, X.presheaf.stalk x →+* Ω x := fun x =>
    (algebraMap (IsLocalRing.ResidueField (X.presheaf.stalk x)) (Ω x)).comp
      (IsLocalRing.residue (X.presheaf.stalk x))
  have (x : X) : IsLocalHom (φ x) := inferInstance
  have hconn : ∀ x : X, x ∉ U → ConnectedSpace (Scheme.puncturedSpectrum
      (geometricStalk (Spec.map (CommRingCat.ofHom (φ x))))) := by
    intro x hx
    let H := geometricStalk (Spec.map (CommRingCat.ofHom (φ x)))
    have : IrreducibleSpace (PrimeSpectrum H) :=
      geometricStalk_irreducibleSpace_of_geometricallyUnibranch (φ x) (hX x)
    have : IrreducibleSpace (Spec (CommRingCat.of H)) :=
      inferInstanceAs (IrreducibleSpace (PrimeSpectrum H))
    have : Nonempty (Scheme.puncturedSpectrum H) :=
      puncturedGeometricStalk_nonempty_of_nonempty_open_complement U hU x hx (φ x)
    have : IrreducibleSpace (Scheme.puncturedSpectrum H) :=
      (Scheme.puncturedSpectrumOpen H).ι.isOpenEmbedding.irreducibleSpace
    exact inferInstance
  exact denseOpenPullbackFullyFaithful_of_finite_components hfin U
    (U.isOpen.dense hU) Ω φ hconn

/-- The original open-immersion conclusion of Stacks 58.10.7: every nonempty
open of an arbitrary irreducible geometrically unibranch scheme surjects onto
its actual étale fundamental group. -/
theorem fundamentalGroupHom_surjective_nonemptyOpen_of_geometricallyUnibranch
    {X : Scheme.{u}} [IrreducibleSpace X]
    (hX : ∀ x : X, IsLocalRing.IsGeometricallyUnibranch (X.presheaf.stalk x))
    (U : X.Opens) (hU : (U : Set X).Nonempty)
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (ξ : Spec (.of Ω) ⟶ U.toScheme) :
    Function.Surjective (fundamentalGroupHom U.ι ξ) := by
  have : Nonempty U.toScheme := by
    obtain ⟨x, hx⟩ := hU
    exact ⟨⟨x, hx⟩⟩
  have : IrreducibleSpace U.toScheme := U.ι.isOpenEmbedding.irreducibleSpace
  have : PreservesLimitsOfShape (Discrete PEmpty.{1}) (pullback U.ι) :=
    pullback_preservesLimitsOfShape_pempty U.ι
  change Function.Surjective (autHomOfCompIso (pullback U.ι) (pullbackFiberIso U.ι ξ))
  apply ((autHomOfCompIso_surjective_tfae
    (fiber (ξ ≫ U.ι)) (fiber ξ) (pullback U.ι) (pullbackFiberIso U.ι ξ)).out 2 1).mp
  exact ⟨nonemptyOpenPullbackFullyFaithful_of_geometricallyUnibranch hX U hU⟩

end AlgebraicGeometry.FiniteEtale
