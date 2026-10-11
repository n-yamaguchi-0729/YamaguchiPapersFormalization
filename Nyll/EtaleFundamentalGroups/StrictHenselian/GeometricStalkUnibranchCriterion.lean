/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.StrictHenselian.GeometricStalkUnibranchIrreducible
import Nyll.SchemeTheory.RingTheory.GeometricallyUnibranch
import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# Geometric unibranchness implies irreducibility of the actual strict stalk

The original definition is phrased using the normalization of the reduction.
Its canonical normalization map supplies the integral normal extension used
in the proved étale-neighborhood and geometric-stalk irreducibility results.
In particular the base ring need not be reduced or Noetherian.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory IsLocalRing

namespace EtaleFundamentalGroups.StrictHenselian

universe u

variable {R Ω : Type u} [CommRing R] [IsLocalRing R]
  [Field Ω] (φ : R →+* Ω) [IsLocalHom φ]

/-- Geometric unibranchness in the original normalization definition makes
the nilradical of the actual geometric stalk prime. -/
theorem geometricStalk_nilradical_isPrime_of_geometricallyUnibranch
    (hR : IsLocalRing.IsGeometricallyUnibranch R) :
    (nilradical (geometricStalk (Spec.map (CommRingCat.ofHom φ)))).IsPrime := by
  obtain ⟨hD, hN, hpure⟩ := hR
  let Q := R ⧸ nilradical R
  let N := reducedNormalization R
  have : IsDomain Q := hD
  have : IsLocalRing N := hN
  have : IsDomain N := inferInstance
  have : IsIntegrallyClosed N :=
    integralClosure.isIntegrallyClosedOfFiniteExtension (FractionRing Q)
      (R := Q) (L := FractionRing Q)
  let : Algebra R N := (reducedNormalizationMap R).toAlgebra
  have : Algebra.IsIntegral R N := ⟨reducedNormalizationMap_isIntegral R⟩
  have : IsLocalHom (algebraMap R N) := reducedNormalizationMap_isLocalHom R
  have hres : ResidueField.map (reducedNormalizationMap R) =
      algebraMap (ResidueField R) (ResidueField N) := by
    apply RingHom.ext
    intro z
    obtain ⟨r, rfl⟩ := residue_surjective z
    rfl
  change (ResidueField.map (reducedNormalizationMap R)).IsPurelyInseparable at hpure
  rw [hres, RingHom.isPurelyInseparable_algebraMap_iff] at hpure
  have : IsPurelyInseparable (ResidueField R) (ResidueField N) := hpure
  have hinj : Function.Injective (algebraMap Q N) := by
    intro a b hab
    apply IsFractionRing.injective Q (FractionRing Q)
    exact congrArg (fun n : N => (n : FractionRing Q)) hab
  have hker : RingHom.ker (algebraMap R N) ≤ nilradical R := by
    change RingHom.ker ((algebraMap Q N).comp (Ideal.Quotient.mk (nilradical R))) ≤
      nilradical R
    rw [RingHom.ker_comp_of_injective (Ideal.Quotient.mk (nilradical R)) hinj,
      Ideal.mk_ker]
  exact geometricStalk_nilradical_isPrime_of_integral_normal_extension φ N hker

/-- The spectrum of the actual strict stalk of a geometrically unibranch
local ring is irreducible. The field-valued point may have any overfield. -/
theorem geometricStalk_irreducibleSpace_of_geometricallyUnibranch
    (hR : IsLocalRing.IsGeometricallyUnibranch R) :
    IrreducibleSpace (PrimeSpectrum (geometricStalk (Spec.map (CommRingCat.ofHom φ)))) :=
  PrimeSpectrum.irreducibleSpace_iff_isPrime_nilradical.mpr
    (geometricStalk_nilradical_isPrime_of_geometricallyUnibranch φ hR)

end EtaleFundamentalGroups.StrictHenselian
