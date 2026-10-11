/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Normalization.GenericExtensionFiber
import EtaleFundamentalGroups.Normalization.UnramifiedNormalization
import SchemeTheory.Morphisms.FiberRank
import Mathlib.AlgebraicGeometry.Fiber
import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
import Mathlib.RingTheory.Spectrum.Prime.FreeLocus

/-!
# Degrees of the fibers of an unramified normalization

The actual generic-fiber square identifies the rank of a finite etale
normalization with the degree of the original field extension. Local
constancy then gives the same degree on every scheme-theoretic fiber.
This proves the implication from unramifiedness to condition (8) of
Stacks Project, Tag 0BTF, with equality rather than only a lower bound.
No separability, Galois, or Noetherian hypothesis is added.

Reference: https://stacks.math.columbia.edu/tag/0BTF
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

namespace EtaleFundamentalGroups

universe u

private local instance fieldSpecQuasiCompact
    {K : Type u} [Field K] {S : Scheme.{u}} (f : Spec (.of K) ⟶ S) :
    QuasiCompact f where
  isCompact_preimage U _ _ := (Set.toFinite (f ⁻¹' U)).isCompact

private theorem finiteFieldExtension_spec_finrank
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] (p : PrimeSpectrum K) :
    (Spec.map (CommRingCat.ofHom (algebraMap K L))).finrank p =
      Module.finrank K L := by
  calc
    (Spec.map (CommRingCat.ofHom (algebraMap K L))).finrank p =
        Module.rankAtStalk L p := Scheme.Hom.finrank_SpecMap_algebraMap K L p
    _ = Module.finrank K L := by
      simp only [Module.rankAtStalk_eq_finrank_of_free, Pi.natCast_apply, Nat.cast_id]

/-- The degree of the actual finite etale normalization is the original
field-extension degree at every point of the integral base. -/
theorem finiteEtale_genericExtensionNormalization_finrank
    (X : Scheme.{u}) [IsIntegral X]
    (L : Type u) [Field L] [Algebra X.functionField L]
    [FiniteDimensional X.functionField L]
    [IsFinite (X.genericExtensionMorphism L).fromNormalization]
    [Etale (X.genericExtensionMorphism L).fromNormalization] (x : X) :
    (X.genericExtensionMorphism L).fromNormalization.finrank x =
      Module.finrank X.functionField L := by
  let f : (X.genericExtensionMorphism L).normalization ⟶ X :=
    (X.genericExtensionMorphism L).fromNormalization
  calc
    f.finrank x =
        (Spec.map (CommRingCat.ofHom (algebraMap X.functionField L))).finrank
          (IsLocalRing.closedPoint X.functionField) :=
      Scheme.Hom.finrank_eq_genericStalkPullback f
        (X.genericExtensionMorphism L).toNormalization
        (Spec.map (CommRingCat.ofHom (algebraMap X.functionField L)))
        (isPullback_genericExtensionNormalization X L) x
    _ = Module.finrank X.functionField L :=
      finiteFieldExtension_spec_finrank X.functionField L
        (IsLocalRing.closedPoint X.functionField)

/-- The scheme-theoretic fibers of an unramified normalization are finite
etale of degree exactly `[L : K]`. This supplies `(2) -> (8)` in Tag 0BTF
for an arbitrary finite extension of the function field. -/
theorem unramified_normalization_fiber_finiteEtale_degree
    (X : Scheme.{u}) [IsIntegral X] [IsNormalIntegral X]
    (L : Type u) [Field L] [Algebra X.functionField L]
    [FiniteDimensional X.functionField L]
    (h : FormallyUnramified (X.genericExtensionMorphism L).fromNormalization ∧
      LocallyOfFiniteType (X.genericExtensionMorphism L).fromNormalization)
    (x : X) :
    IsFinite ((X.genericExtensionMorphism L).fromNormalization.fiberToSpecResidueField x) ∧
      Etale ((X.genericExtensionMorphism L).fromNormalization.fiberToSpecResidueField x) ∧
      ((X.genericExtensionMorphism L).fromNormalization.fiberToSpecResidueField x).finrank
          (IsLocalRing.closedPoint (X.residueField x)) =
        Module.finrank X.functionField L := by
  let f : (X.genericExtensionMorphism L).normalization ⟶ X :=
    (X.genericExtensionMorphism L).fromNormalization
  have he : Etale f :=
    (unramified_normalization_iff_etale_iff_finiteEtale X L).1.mp h
  have hf : IsFinite f :=
    ((unramified_normalization_iff_etale_iff_finiteEtale X L).2.mp he).1
  refine ⟨inferInstanceAs (IsFinite (pullback.snd f (X.fromSpecResidueField x))),
    inferInstanceAs (Etale (pullback.snd f (X.fromSpecResidueField x))), ?_⟩
  exact (Scheme.Hom.finrank_fiberToSpecResidueField f x).trans
    (finiteEtale_genericExtensionNormalization_finrank X L x)

end EtaleFundamentalGroups
