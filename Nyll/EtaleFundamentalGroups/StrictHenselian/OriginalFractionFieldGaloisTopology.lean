/-
Copyright (c) 2024 Nailin Guan. All rights reserved.
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan, Yuyang Zhao, Jujian Zhang,
Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.StrictHenselian.OriginalFractionFieldGalois
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Topology.Algebra.ContinuousMonoidHom

/-!
# The original fraction-field Galois comparison preserves the Krull topology

A finite intermediate field over the displayed fraction field is finite
over the canonical fraction field because their coefficient map is
surjective. The original scalar comparison therefore carries every basic
Krull neighborhood continuously. Compactness gives continuity of its inverse.

The finite-basis argument adapts `InfiniteGalois.restrictNormalHom_continuous`
from Mathlib/FieldTheory/Galois/Profinite.lean at revision 065356127b1dc0016f66b7283ce0ce2c4055aa55.
-/

noncomputable section

open scoped Topology

namespace EtaleFundamentalGroups.StrictHenselian

universe u v w

private theorem extendScalarsHomOfSurjective_continuous
    (F : Type u) (K : Type v) (L : Type w) [Field F] [Field K] [Field L]
    [Algebra F K] [Algebra K L] [Algebra F L] [IsScalarTower F K L]
    (h : Function.Surjective (algebraMap F K)) :
    Continuous (AlgEquiv.extendScalarsHomOfSurjective (A := L) h :
      Gal(L/F) ≃* Gal(L/K)) := by
  have : FiniteDimensional F K := Module.Finite.of_surjective (Algebra.linearMap F K) h
  let e : Gal(L/F) ≃* Gal(L/K) := AlgEquiv.extendScalarsHomOfSurjective h
  apply continuous_of_continuousAt_one e.toMonoidHom (continuousAt_def.mpr ?_)
  intro N hN
  rw [map_one, krullTopology_mem_nhds_one_iff] at hN
  obtain ⟨E, hE, hN⟩ := hN
  have : FiniteDimensional K E := hE
  have : FiniteDimensional F (E.restrictScalars F) := Module.Finite.trans (R := F) K E
  apply mem_nhds_iff.mpr
  refine ⟨(E.restrictScalars F).fixingSubgroup, ?_,
    (E.restrictScalars F).fixingSubgroup_isOpen, (E.restrictScalars F).fixingSubgroup.one_mem⟩
  intro σ hσ
  apply hN
  apply (IntermediateField.mem_fixingSubgroup_iff E (e σ)).mpr
  intro x hx
  exact (IntermediateField.mem_fixingSubgroup_iff (E.restrictScalars F) σ).mp hσ x hx

/-- The canonical-to-original fraction-field Galois comparison is continuous
for the original Krull topologies. -/
theorem originalFractionFieldGaloisEquiv_continuous
    (A : Type u) (K : Type v) (L : Type w)
    [CommRing A] [IsDomain A] [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K] [Algebra A L] [FaithfulSMul A L]
    [Algebra K L] [IsScalarTower A K L] :
    let : Algebra (FractionRing A) K := FractionRing.liftAlgebra A K
    let : Algebra (FractionRing A) L := FractionRing.liftAlgebra A L
    Continuous (originalFractionFieldGaloisEquiv A K L) := by
  intro actualFractionAlgebra actualAmbientAlgebra
  have : IsScalarTower (FractionRing A) K L := inferInstance
  exact extendScalarsHomOfSurjective_continuous (FractionRing A) K L
    (fractionFieldBaseMap_surjective A K)

/-- The same literal original automorphism comparison is a homeomorphism
when the ambient field is the original separable closure. -/
theorem originalFractionFieldGaloisEquiv_isHomeomorph
    (A : Type u) (K : Type v) (L : Type w)
    [CommRing A] [IsDomain A] [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K] [Algebra A L] [FaithfulSMul A L]
    [Algebra K L] [IsScalarTower A K L] [IsGalois K L] [IsSepClosed L] :
    let : Algebra (FractionRing A) K := FractionRing.liftAlgebra A K
    let : Algebra (FractionRing A) L := FractionRing.liftAlgebra A L
    IsHomeomorph (originalFractionFieldGaloisEquiv A K L) := by
  intro actualFractionAlgebra actualAmbientAlgebra
  have : IsSepClosure (FractionRing A) L := originalFractionField_isSepClosure A K L
  rw [isHomeomorph_iff_continuous_bijective]
  exact ⟨originalFractionFieldGaloisEquiv_continuous A K L,
    (originalFractionFieldGaloisEquiv A K L).bijective⟩

end EtaleFundamentalGroups.StrictHenselian
