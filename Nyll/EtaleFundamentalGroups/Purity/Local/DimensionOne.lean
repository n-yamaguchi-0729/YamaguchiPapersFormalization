/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Smooth.Fiber

/-!
# Dimension-one local purity over a DVR

At every height-one point of the regular base used in the absolute Abhyankar
argument, the local ring is a DVR.  A finite torsion-free algebra over that DVR
is finite free, hence flat.  If the algebra is local, unramifiedness at its
closed point therefore makes the morphism etale at that point.  The etale locus
is open and stable under generalization, while every prime of a local ring lies
below its closed point, so the whole finite algebra is etale.

This is the dimension-one input to the higher-dimensional local-purity step;
it does not assume flatness or etaleness separately.
-/

noncomputable section

namespace EtaleFundamentalGroups

open IsLocalRing

universe u v

/-- Dimension-one purity over a Dedekind domain: a finite torsion-free algebra
that is unramified at every maximal ideal is finite etale.

Torsion-freeness produces flatness over the Dedekind base.  At each prime of
the target, choose a maximal ideal above it.  Unramifiedness at that maximal
ideal and flatness give etaleness there, and stability under generalization
then gives etaleness at the original prime. -/
theorem etale_of_dedekind_of_finite_torsionFree_of_isUnramifiedAt_all_maximalIdeals
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    [IsDedekindDomain R] [Algebra R S]
    [Module.Finite R S] [Module.IsTorsionFree R S]
    (hunramified : ∀ (P : Ideal S), [P.IsMaximal] → Algebra.IsUnramifiedAt R P) :
    Algebra.Etale R S := by
  let : Module.FinitePresentation R S :=
    Module.finitePresentation_of_finite R S
  let : Algebra.FinitePresentation R S :=
    Algebra.FinitePresentation.of_finitePresentation R S
  rw [← Algebra.etaleLocus_eq_univ_iff_etale]
  apply Set.eq_univ_iff_forall.mpr
  intro p
  obtain ⟨P, hP, hpP⟩ := Ideal.exists_le_maximal p.asIdeal p.isPrime.ne_top
  let : P.IsPrime := hP.isPrime
  let : Algebra.IsUnramifiedAt R P := hunramified P
  let : Algebra.IsEtaleAt R P :=
    Algebra.IsEtaleAt.of_isUnramifiedAt_of_flat (R := R) (S := S) P
  let q : PrimeSpectrum S := ⟨P, inferInstance⟩
  have hq : q ∈ Algebra.etaleLocus R S := by
    change Algebra.IsEtaleAt R P
    infer_instance
  exact Algebra.isOpen_etaleLocus.stableUnderGeneralization
    ((PrimeSpectrum.le_iff_specializes p q).mp hpP) hq

/-- Dimension-one purity over a DVR: a finite torsion-free algebra that is
unramified at every maximal ideal is finite etale.

This formulation directly consumes the all-maximal-ideals output of the DVR
Abhyankar theorem.  Finite torsion-freeness over the PID underlying the DVR
produces flatness; openness and generalization-stability of the etale locus
then propagate etaleness from the maximal points to every prime. -/
theorem etale_of_dvr_of_finite_torsionFree_of_isUnramifiedAt_all_maximalIdeals
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    [IsDomain R] [IsDiscreteValuationRing R] [Algebra R S]
    [Module.Finite R S] [Module.IsTorsionFree R S]
    (hunramified : ∀ (P : Ideal S), [P.IsMaximal] → Algebra.IsUnramifiedAt R P) :
    Algebra.Etale R S := by
  let : IsDedekindDomain R := inferInstance
  exact
    etale_of_dedekind_of_finite_torsionFree_of_isUnramifiedAt_all_maximalIdeals
      hunramified

/-- Dimension-one local purity: a finite torsion-free local algebra over a DVR
that is unramified at its closed point is finite etale.

The torsion-free hypothesis is supplied by the normalization sitting inside
its fraction field.  Flatness is produced in the proof from finite
torsion-freeness over the PID underlying the DVR. -/
theorem etale_of_dvr_of_finite_torsionFree_of_isUnramifiedAt_maximalIdeal
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    [IsDomain R] [IsDiscreteValuationRing R] [Algebra R S]
    [IsLocalRing S] [Module.Finite R S] [Module.IsTorsionFree R S]
    [Algebra.IsUnramifiedAt R (maximalIdeal S)] :
    Algebra.Etale R S := by
  apply etale_of_dvr_of_finite_torsionFree_of_isUnramifiedAt_all_maximalIdeals
  intro P _
  have hP : P = maximalIdeal S :=
    IsLocalRing.eq_maximalIdeal (show P.IsMaximal from inferInstance)
  subst P
  infer_instance

end EtaleFundamentalGroups
