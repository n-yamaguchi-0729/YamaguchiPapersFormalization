/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Purity.PuncturedHypersurfaceNeighborhoodFaithful
import Nyll.SchemeTheory.LocalGeometry.PuncturedSpectrum
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
import Mathlib.RingTheory.Spectrum.Prime.RingHom
import Mathlib.Topology.Connected.Basic

/-!
# Faithful restriction to a punctured hypersurface

If every minimal prime not containing the equation has quotient dimension
at least two, every connected component of the punctured spectrum meets the
hypersurface. Consequently finite étale restriction to its actual pullback
is faithful. This proves the dimension case of Stacks 58.19.2 (`0BLG`);
its component-intersection case is the general connected-component theorem.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits IsLocalRing

namespace AlgebraicGeometry.FiniteEtale

/-- The dimension condition on minimal primes forces the hypersurface to
meet each connected component of the puncture. -/
theorem exists_hypersurface_point_in_connectedComponent_of_minimalPrime_dimension
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (f : R) (hf : f ∈ maximalIdeal R)
    (hdim : ∀ P ∈ minimalPrimes R, f ∉ P →
      (2 : WithBot ℕ∞) ≤ ringKrullDim (R ⧸ P))
    (x : Scheme.puncturedSpectrum R) :
    ∃ y : Scheme.puncturedSpectrum R,
      f ∈ y.1.asIdeal ∧ y ∈ connectedComponent x :=
  exists_hypersurface_point_in_neighborhood_connectedComponent R f hf
    (Scheme.puncturedSpectrumOpen R) (fun _ hp _ ↦ hp)
    (fun P hP _ hfP ↦ hdim P hP hfP) x

/-- Finite étale restriction to the punctured hypersurface is faithful under
the minimal-prime dimension condition of Stacks 58.19.2 (`0BLG`). The source
of the restriction is the literal scheme pullback defining that hypersurface. -/
theorem pullback_faithful_punctured_hypersurface_of_minimalPrime_dimension
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (f : R) (hf : f ∈ maximalIdeal R)
    (hdim : ∀ P ∈ minimalPrimes R, f ∉ P →
      (2 : WithBot ℕ∞) ≤ ringKrullDim (R ⧸ P)) :
    (FiniteEtale.pullback (pullback.fst (Scheme.puncturedSpectrumInclusion R)
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {f})))))).Faithful :=
  pullback_faithful_punctured_hypersurface_neighborhood_of_minimalPrime_dimension R f hf
    (Scheme.puncturedSpectrumOpen R) (fun _ hp _ ↦ hp)
    (fun P hP _ hfP ↦ hdim P hP hfP)

end AlgebraicGeometry.FiniteEtale
