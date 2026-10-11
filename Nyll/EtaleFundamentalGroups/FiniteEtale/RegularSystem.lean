/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.RingTheory.LocalRing.Etale
import Mathlib.RingTheory.Regular.Flat
import Nyll.SchemeTheory.LocalGeometry.RegularLocal.SystemDomain

/-!
# Regular systems under a finite étale local extension

A finite étale local algebra is faithfully flat over its local base.  Hence a
regular system remains regular after applying the algebra map.  Formal
unramifiedness identifies the extension of the source maximal ideal with the
target maximal ideal, so the mapped system still generates the maximal ideal.

For a module-finite extension of a Noetherian base, the target is Noetherian.
The regular-system geometry developed in `Kummer.RegularSystemDomain` then
supplies the domain, regular-local, prime-parameter, and quotient conclusions.
-/

noncomputable section

namespace EtaleFundamentalGroups

open IsLocalRing
open RingTheory.Sequence

universe u v

/-- A regular system of parameters remains a regular system of parameters
under an étale local extension.

The regularity is faithfully-flat descent along the local flat map.  The
maximal-ideal equality is the cotangent-space consequence of formal
unramifiedness, rather than an extra assumption on the residue extension. -/
theorem regularSystem_map_of_etale_local
    {A : Type u} {C : Type v}
    [CommRing A] [CommRing C] [Algebra A C]
    [IsLocalRing A] [IsLocalRing C]
    [Algebra.Etale A C]
    [IsLocalHom (algebraMap A C)]
    {ps : List A}
    (hreg : IsRegular A ps)
    (hgen : Ideal.ofList ps = maximalIdeal A) :
    IsRegular C (ps.map (algebraMap A C)) ∧
      Ideal.ofList (ps.map (algebraMap A C)) = maximalIdeal C := by
  let : Module.FaithfullyFlat A C :=
    Module.FaithfullyFlat.of_flat_of_isLocalHom
  have hregC : IsRegular C (ps.map (algebraMap A C)) :=
    hreg.of_faithfullyFlat
  have hgenC : Ideal.ofList (ps.map (algebraMap A C)) = maximalIdeal C := by
    calc
      Ideal.ofList (ps.map (algebraMap A C)) =
          (Ideal.ofList ps).map (algebraMap A C) := by
        rw [Ideal.map_ofList]
      _ = (maximalIdeal A).map (algebraMap A C) := by rw [hgen]
      _ = maximalIdeal C :=
        Algebra.FormallyUnramified.map_maximalIdeal
  exact ⟨hregC, hgenC⟩

/-- Full local geometry of the mapped parameter system in a finite étale
local extension of a Noetherian local ring.

No domain, regular-local, or primality hypothesis is imposed on the target.
They are all produced from the mapped regular system.  In particular, every
mapped parameter cuts out a regular local domain. -/
theorem finiteEtale_regularSystem_geometry
    {A : Type u} {C : Type v}
    [CommRing A] [CommRing C] [Algebra A C]
    [IsLocalRing A] [IsLocalRing C] [IsNoetherianRing A]
    [Module.Finite A C] [Algebra.Etale A C]
    [IsLocalHom (algebraMap A C)]
    {ps : List A}
    (hreg : IsRegular A ps)
    (hgen : Ideal.ofList ps = maximalIdeal A) :
    IsNoetherianRing C ∧
      IsDomain C ∧
      IsRegular C (ps.map (algebraMap A C)) ∧
      Ideal.ofList (ps.map (algebraMap A C)) = maximalIdeal C ∧
      IsRegularLocalRing C ∧
      (∀ p ∈ ps.map (algebraMap A C), Prime p) ∧
      (∀ p ∈ ps.map (algebraMap A C),
        IsDomain (C ⧸ Ideal.span {p}) ∧
          IsRegularLocalRing (C ⧸ Ideal.span {p})) := by
  let : IsNoetherianRing C := IsNoetherianRing.of_finite A C
  obtain ⟨hregC, hgenC⟩ :=
    regularSystem_map_of_etale_local
      (A := A) (C := C) (ps := ps) hreg hgen
  have hdomainC : IsDomain C :=
    Kummer.isDomain_of_regularSystem
      (ps.map (algebraMap A C)) hregC hgenC
  have hregularC : IsRegularLocalRing C :=
    Kummer.isRegularLocalRing_of_regularSystem
      (ps.map (algebraMap A C)) hregC hgenC
  refine ⟨inferInstance, hdomainC, hregC, hgenC, hregularC, ?_, ?_⟩
  · intro p hp
    exact Kummer.prime_of_mem_regularSystem hregC hgenC hp
  · intro p hp
    exact Kummer.quotient_geometry_of_mem_regularSystem hregC hgenC hp

end EtaleFundamentalGroups

end
