/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Normalization.UnramifiedNormalization
import Nyll.EtaleFundamentalGroups.Normalization.GlobalLocalUnramifiedCriterion
import Nyll.EtaleFundamentalGroups.Normalization.UnramifiedFiberDegree
import Nyll.EtaleFundamentalGroups.Normalization.GlobalFiberDegreeCriterion
import Nyll.EtaleFundamentalGroups.Normalization.AffineInertiaCriterion
import Nyll.EtaleFundamentalGroups.StrictHenselian.OrdinaryHenselization
import Mathlib.Tactic.TFAE

/-!
# The original eight normalization criteria and the Galois inertia criterion

Stacks Project Tag 0BTF is assembled from the actual global, local-ring,
ordinary-henselian, strict-henselian, and scheme-fiber suppliers. Both
henselizations are the constructed pointed étale colimits; no finite set of
neighborhoods or an assumed local comparison replaces their original maps.

Reference: https://stacks.math.columbia.edu/tag/0BTF
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace EtaleFundamentalGroups

universe u

private local instance fieldSpecQuasiCompact
    {K : Type u} [Field K] {S : Scheme.{u}} (f : Spec (.of K) ⟶ S) :
    QuasiCompact f where
  isCompact_preimage U _ _ := (Set.toFinite (f ⁻¹' U)).isCompact

/-- The definition in Stacks Project Section 58.11: the base is unramified
in the field extension if its actual normalization morphism is unramified. -/
def IsUnramifiedIn (X : Scheme.{u}) [IsIntegral X]
    (L : Type u) [Field L] [Algebra X.functionField L] : Prop :=
  FormallyUnramified (X.genericExtensionMorphism L).fromNormalization ∧
    LocallyOfFiniteType (X.genericExtensionMorphism L).fromNormalization

/-- Original Tag 0BTF, conditions `(1)` through `(8)`, for every finite
extension of the function field of an integral normal scheme. -/
theorem unramified_normalization_criteria_tfae
    (X : Scheme.{u}) [IsIntegral X] [IsNormalIntegral X]
    (L : Type u) [Field L] [Algebra X.functionField L]
    [FiniteDimensional X.functionField L] :
    let f := (X.genericExtensionMorphism L).fromNormalization
    List.TFAE [
      IsUnramifiedIn X L,
      FormallyUnramified f ∧ LocallyOfFiniteType f,
      Etale f,
      IsFinite f ∧ Etale f,
      ∀ x : X, FormallyUnramified (pullback.snd f (X.fromSpecStalk x)) ∧
        LocallyOfFiniteType (pullback.snd f (X.fromSpecStalk x)),
      ∀ x : X,
        FormallyUnramified (pullback.snd f
          (Spec.map (CommRingCat.ofHom
            (StrictHenselian.ordinaryHenselizationMap (X.presheaf.stalk x))) ≫
              X.fromSpecStalk x)) ∧
        LocallyOfFiniteType (pullback.snd f
          (Spec.map (CommRingCat.ofHom
            (StrictHenselian.ordinaryHenselizationMap (X.presheaf.stalk x))) ≫
              X.fromSpecStalk x)),
      ∀ x : X,
        FormallyUnramified (pullback.snd f
          (Spec.map (CommRingCat.ofHom (StrictHenselian.geometricStalkStructureMap
            ((algebraMap (IsLocalRing.ResidueField (X.presheaf.stalk x))
              (SeparableClosure (IsLocalRing.ResidueField (X.presheaf.stalk x)))).comp
                (IsLocalRing.residue (X.presheaf.stalk x))))) ≫ X.fromSpecStalk x)) ∧
        LocallyOfFiniteType (pullback.snd f
          (Spec.map (CommRingCat.ofHom (StrictHenselian.geometricStalkStructureMap
            ((algebraMap (IsLocalRing.ResidueField (X.presheaf.stalk x))
              (SeparableClosure (IsLocalRing.ResidueField (X.presheaf.stalk x)))).comp
                (IsLocalRing.residue (X.presheaf.stalk x))))) ≫ X.fromSpecStalk x)),
      ∀ x : X, Etale (f.fiberToSpecResidueField x) ∧
        Module.finrank X.functionField L ≤
          (f.fiberToSpecResidueField x).finrank (IsLocalRing.closedPoint (X.residueField x))] := by
  intro f
  tfae_have 1 ↔ 2 := Iff.rfl
  tfae_have 2 ↔ 3 := (unramified_normalization_iff_etale_iff_finiteEtale X L).1
  tfae_have 3 ↔ 4 := (unramified_normalization_iff_etale_iff_finiteEtale X L).2
  tfae_have 2 → 5 := fun h x => unramified_normalization_stalk_of_unramified X L h x
  tfae_have 5 → 4 := finiteEtale_normalization_of_stalk_unramified X L
  tfae_have 5 ↔ 6 := by
    constructor
    · intro h x
      exact (unramified_normalization_stalk_iff_geometricStalk X L x
        (IsLocalRing.residue (X.presheaf.stalk x))).mp (h x)
    · intro h x
      exact (unramified_normalization_stalk_iff_geometricStalk X L x
        (IsLocalRing.residue (X.presheaf.stalk x))).mpr (h x)
  tfae_have 5 ↔ 7 := by
    have hpointLocal (x : X) : IsLocalHom
        ((algebraMap (IsLocalRing.ResidueField (X.presheaf.stalk x))
          (SeparableClosure (IsLocalRing.ResidueField (X.presheaf.stalk x)))).comp
            (IsLocalRing.residue (X.presheaf.stalk x))) := by
      let k := IsLocalRing.ResidueField (X.presheaf.stalk x)
      have hfieldLocal : IsLocalHom (algebraMap k (SeparableClosure k)) := ⟨by
          intro z hz
          apply isUnit_iff_ne_zero.mpr
          intro hzero
          apply hz.ne_zero
          rw [hzero, map_zero]⟩
      exact RingHom.isLocalHom_comp (algebraMap k (SeparableClosure k))
        (IsLocalRing.residue (X.presheaf.stalk x))
    constructor
    · intro h x
      let φ := (algebraMap (IsLocalRing.ResidueField (X.presheaf.stalk x))
        (SeparableClosure (IsLocalRing.ResidueField (X.presheaf.stalk x)))).comp
          (IsLocalRing.residue (X.presheaf.stalk x))
      have : IsLocalHom φ := hpointLocal x
      exact (unramified_normalization_stalk_iff_geometricStalk X L x φ).mp (h x)
    · intro h x
      let φ := (algebraMap (IsLocalRing.ResidueField (X.presheaf.stalk x))
        (SeparableClosure (IsLocalRing.ResidueField (X.presheaf.stalk x)))).comp
          (IsLocalRing.residue (X.presheaf.stalk x))
      have : IsLocalHom φ := hpointLocal x
      exact (unramified_normalization_stalk_iff_geometricStalk X L x φ).mpr (h x)
  tfae_have 2 → 8 := by
    intro h x
    obtain ⟨_, he, hdegree⟩ := unramified_normalization_fiber_finiteEtale_degree X L h x
    exact ⟨he, hdegree.symm.le⟩
  tfae_have 8 → 4 := finiteEtale_normalization_of_fiber_etale_degree X L
  tfae_finish

/-- Original Tag 0BTF with condition `(9)` added for a finite Galois
extension. The inertia statement uses the literal normalization point and
its original ambient-field automorphism's actual residue-field map. -/
theorem unramified_normalization_galois_criteria_tfae
    (X : Scheme.{u}) [IsIntegral X] [IsNormalIntegral X]
    (L : Type u) [Field L] [Algebra X.functionField L]
    [FiniteDimensional X.functionField L] [IsGalois X.functionField L] :
    let f := (X.genericExtensionMorphism L).fromNormalization
    List.TFAE [
      IsUnramifiedIn X L,
      FormallyUnramified f ∧ LocallyOfFiniteType f,
      Etale f,
      IsFinite f ∧ Etale f,
      ∀ x : X, FormallyUnramified (pullback.snd f (X.fromSpecStalk x)) ∧
        LocallyOfFiniteType (pullback.snd f (X.fromSpecStalk x)),
      ∀ x : X,
        FormallyUnramified (pullback.snd f
          (Spec.map (CommRingCat.ofHom
            (StrictHenselian.ordinaryHenselizationMap (X.presheaf.stalk x))) ≫
              X.fromSpecStalk x)) ∧
        LocallyOfFiniteType (pullback.snd f
          (Spec.map (CommRingCat.ofHom
            (StrictHenselian.ordinaryHenselizationMap (X.presheaf.stalk x))) ≫
              X.fromSpecStalk x)),
      ∀ x : X,
        FormallyUnramified (pullback.snd f
          (Spec.map (CommRingCat.ofHom (StrictHenselian.geometricStalkStructureMap
            ((algebraMap (IsLocalRing.ResidueField (X.presheaf.stalk x))
              (SeparableClosure (IsLocalRing.ResidueField (X.presheaf.stalk x)))).comp
                (IsLocalRing.residue (X.presheaf.stalk x))))) ≫ X.fromSpecStalk x)) ∧
        LocallyOfFiniteType (pullback.snd f
          (Spec.map (CommRingCat.ofHom (StrictHenselian.geometricStalkStructureMap
            ((algebraMap (IsLocalRing.ResidueField (X.presheaf.stalk x))
              (SeparableClosure (IsLocalRing.ResidueField (X.presheaf.stalk x)))).comp
                (IsLocalRing.residue (X.presheaf.stalk x))))) ≫ X.fromSpecStalk x)),
      ∀ x : X, Etale (f.fiberToSpecResidueField x) ∧
        Module.finrank X.functionField L ≤
          (f.fiberToSpecResidueField x).finrank (IsLocalRing.closedPoint (X.residueField x)),
      ∀ (σ : L ≃ₐ[X.functionField] L)
        (y : (X.genericExtensionMorphism L).normalization)
        (hy : Inertia.normalizationEndomorphism (X.genericExtensionMorphism L)
          (Spec.map (CommRingCat.ofHom σ.toRingHom))
          (genericExtensionMorphism_specMap_algEquiv X L σ) y = y),
        (Inertia.normalizationEndomorphism (X.genericExtensionMorphism L)
          (Spec.map (CommRingCat.ofHom σ.toRingHom))
          (genericExtensionMorphism_specMap_algEquiv X L σ)).residueFieldMap y =
            ((X.genericExtensionMorphism L).normalization.residueFieldCongr hy).hom → σ = 1] := by
  intro f
  have h := unramified_normalization_criteria_tfae X L
  tfae_have 1 ↔ 2 := h.out 1 2
  tfae_have 2 ↔ 3 := h.out 2 3
  tfae_have 3 ↔ 4 := h.out 3 4
  tfae_have 4 ↔ 5 := h.out 4 5
  tfae_have 5 ↔ 6 := h.out 5 6
  tfae_have 6 ↔ 7 := h.out 6 7
  tfae_have 7 ↔ 8 := h.out 7 8
  tfae_have 3 ↔ 9 := etale_genericNormalization_iff_trivial_point_residue_inertia X L
  tfae_finish

end EtaleFundamentalGroups
