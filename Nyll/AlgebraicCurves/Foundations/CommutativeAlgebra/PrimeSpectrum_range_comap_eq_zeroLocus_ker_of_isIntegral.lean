/-
Copyright (c) 2026 Naganori Yamaguchi (local additions and compilation).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

This library builds on Anthropic's Fermat's Last Theorem in Lean 4;
no direct Anthropic source-file match is established for this module.
Upstream NOTICE (Copyright 2026 Anthropic, PBC): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md
Repository maintainer: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
-/

import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# Prime Spectrum range comap eq zero Locus ker of is Integral
-/

section ProofImplementation

namespace AlgebraicCurves.Foundations.CommutativeAlgebra.Proofs
namespace PrimeSpectrum_range_comap_eq_zeroLocus_ker_of_isIntegral

universe u v

open PrimeSpectrum

theorem _root_.PrimeSpectrum.range_comap_eq_zeroLocus_ker_of_isIntegral
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] (f : R →+* S) (hf : f.IsIntegral) :
    Set.range (PrimeSpectrum.comap f) = PrimeSpectrum.zeroLocus (RingHom.ker f) := by
  rw [← (PrimeSpectrum.isClosedMap_comap_of_isIntegral f hf).isClosed_range.closure_eq,
    PrimeSpectrum.closure_range_comap]

end PrimeSpectrum_range_comap_eq_zeroLocus_ker_of_isIntegral
end AlgebraicCurves.Foundations.CommutativeAlgebra.Proofs
end ProofImplementation
