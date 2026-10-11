/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.RingTheory.Etale.Locus
import Mathlib.RingTheory.Ideal.Height
import Mathlib.RingTheory.IntegralClosure.GoingDown

/-!
# The codimension-one support input to special local purity

This file isolates the part of special local purity currently supported by
the commutative-algebra API.  In a faithfully integral extension of domains
over an integrally closed base, going-down and incomparability identify the
height of a prime with the height of its contraction.  Consequently, if the
extension is unramified (respectively etale) over every height-one base
prime, the support of relative differentials (respectively the union with
the first cotangent homology support) contains no height-one prime.

The missing step to full purity is precisely the codimension-at-least-two
support-vanishing theorem; it is not assumed here.
-/

noncomputable section

namespace EtaleFundamentalGroups.SpecialLocalPurity

universe u v

/--
Prime height is preserved by a faithfully integral extension of domains over
an integrally closed base.  The two inequalities come from incomparability
and going-down, respectively.
-/
theorem height_eq_height_under_of_faithfully_integral_over_integrallyClosed
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    [IsDomain R] [IsIntegrallyClosed R] [IsDomain S]
    [Algebra R S] [Algebra.IsIntegral R S] [FaithfulSMul R S]
    (P : Ideal S) [P.IsPrime] :
    P.height = (P.under R).height := by
  let Q : PrimeSpectrum S := ⟨P, inferInstance⟩
  let p : PrimeSpectrum R := PrimeSpectrum.comap (algebraMap R S) Q
  change Q.asIdeal.height = p.asIdeal.height
  rw [PrimeSpectrum.height_eq_orderHeight, PrimeSpectrum.height_eq_orderHeight]
  apply le_antisymm
  · apply Order.height_le
    intro l hlast
    let l' : LTSeries (PrimeSpectrum R) :=
      l.map (PrimeSpectrum.comap (algebraMap R S)) (by
        intro x y hxy
        exact Ideal.IsIntegral.under_lt_under hxy)
    have hlast' : l'.last = p := by
      change PrimeSpectrum.comap (algebraMap R S) l.last = p
      rw [hlast]
    rw [← show l'.length = l.length by rfl]
    simpa [hlast'] using (Order.length_le_height_last (p := l'))
  · apply Order.height_le
    intro l hlast
    have hlastIdeal : l.last.asIdeal = P.under R := by
      simpa [p, Q, Ideal.under_def] using congrArg PrimeSpectrum.asIdeal hlast
    let : P.LiesOver l.last.asIdeal := ⟨hlastIdeal⟩
    obtain ⟨L, hlen, hlastL, -⟩ :=
      Ideal.exists_ltSeries_of_hasGoingDown l P
    rw [← hlen]
    simpa [Q, hlastL] using (Order.length_le_height_last (p := L))

private theorem contracted_height_eq_one
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    [IsDomain R] [IsIntegrallyClosed R] [IsDomain S]
    [Algebra R S] [Algebra.IsIntegral R S] [FaithfulSMul R S]
    (P : Ideal S) [P.IsPrime] (hP : P.height = 1) :
    (P.under R).height = 1 := by
  rw [← height_eq_height_under_of_faithfully_integral_over_integrallyClosed P]
  exact hP

/--
If a finite torsion-free extension is unramified above every height-one base
prime, the support of its relative Kähler differentials has no height-one
prime.
-/
theorem kaehlerDifferential_support_subset_height_ne_one_of_unramifiedAt_heightOne
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    [IsDomain R] [IsIntegrallyClosed R] [IsDomain S]
    [Algebra R S] [Module.Finite R S] [Module.IsTorsionFree R S]
    (hunramified :
      ∀ (p : Ideal R) [p.IsPrime], p.height = 1 →
        ∀ (P : Ideal S) [P.IsPrime] [P.LiesOver p],
          Algebra.IsUnramifiedAt R P) :
    Module.support S Ω[S⁄R] ⊆ {P | P.asIdeal.height ≠ 1} := by
  let : Algebra.IsIntegral R S := Algebra.IsIntegral.of_finite R S
  intro P hsupport hheight
  let : P.asIdeal.IsPrime := P.isPrime
  let p : Ideal R := P.asIdeal.under R
  let : p.IsPrime := inferInstance
  let : P.asIdeal.LiesOver p := inferInstance
  have hpHeight : p.height = 1 :=
    contracted_height_eq_one P.asIdeal hheight
  have hUnramified : Algebra.IsUnramifiedAt R P.asIdeal :=
    hunramified p hpHeight P.asIdeal
  have hLocus : P ∈ Algebra.unramifiedLocus R S := hUnramified
  rw [Algebra.unramifiedLocus_eq_compl_support] at hLocus
  exact hLocus hsupport

/--
If a finite torsion-free extension is etale above every height-one base
prime, neither relative differentials nor first cotangent homology is
supported at a height-one prime.  Thus the non-etale cotangent support has
codimension at least two in the precise height-one sense available here.
-/
theorem nonEtaleCotangentSupport_subset_height_ne_one_of_isEtaleAt_heightOne
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    [IsDomain R] [IsIntegrallyClosed R] [IsDomain S]
    [Algebra R S] [Module.Finite R S] [Module.IsTorsionFree R S]
    (hetale :
      ∀ (p : Ideal R) [p.IsPrime], p.height = 1 →
        ∀ (P : Ideal S) [P.IsPrime] [P.LiesOver p],
          Algebra.IsEtaleAt R P) :
    Module.support S Ω[S⁄R] ∪ Module.support S (Algebra.H1Cotangent R S) ⊆
      {P | P.asIdeal.height ≠ 1} := by
  let : Algebra.IsIntegral R S := Algebra.IsIntegral.of_finite R S
  intro P hsupport hheight
  let : P.asIdeal.IsPrime := P.isPrime
  let p : Ideal R := P.asIdeal.under R
  let : p.IsPrime := inferInstance
  let : P.asIdeal.LiesOver p := inferInstance
  have hpHeight : p.height = 1 :=
    contracted_height_eq_one P.asIdeal hheight
  have hEtale : Algebra.IsEtaleAt R P.asIdeal :=
    hetale p hpHeight P.asIdeal
  have hLocus : P ∈ Algebra.etaleLocus R S := hEtale
  rw [Algebra.etaleLocus_eq_compl_support] at hLocus
  exact hsupport.elim hLocus.1 hLocus.2

end EtaleFundamentalGroups.SpecialLocalPurity

end
