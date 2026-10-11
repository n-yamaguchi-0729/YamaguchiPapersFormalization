/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Divisors.ReducedIrreducibleComponentGeometry
import Nyll.SchemeTheory.Divisors.RegularCartier
import Nyll.SchemeTheory.LocalGeometry.RegularLocal.SystemDomain
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.Algebra.Module.SpanRank
import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Mathlib.RingTheory.RegularLocalRing.Defs

/-!
# Discrete valuation stalks at Cartier component generic points

On a locally Noetherian scheme, the generic point of an effective Cartier
divisor has codimension one. If the ambient scheme is regular along the
divisor, its stalk there is a discrete valuation ring, even when the whole
scheme is neither integral nor globally regular.

The domain assertion is proved locally. Regularity and dimension one make
the maximal ideal principal. A Cartier equation remains a non-zero-divisor
in the stalk, so a generator of that maximal ideal is both prime and a
non-zero-divisor. Krull intersection then proves that the stalk is a domain.
Only after this argument is the DVR cotangent-space criterion applied.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory IsLocalRing

universe u

namespace EtaleFundamentalGroups

private theorem isDomain_of_regularLocal_dimension_one_of_regularElement
    {R : Type u} [CommRing R] [IsRegularLocalRing R]
    (hdim : ringKrullDim R = ((1 : ℕ∞) : WithBot ℕ∞))
    (a : R) (ha : IsSMulRegular R a)
    (hamem : a ∈ maximalIdeal R) : IsDomain R := by
  have hspanCast :
      (((maximalIdeal R).spanFinrank : ℕ∞) : WithBot ℕ∞) =
        ((1 : ℕ∞) : WithBot ℕ∞) :=
    (IsRegularLocalRing.spanFinrank_maximalIdeal (R := R)).trans hdim
  have hspan : (maximalIdeal R).spanFinrank = 1 :=
    ENat.natCast_inj.mp (WithBot.coe_eq_coe.mp hspanCast)
  have hprincipal : (maximalIdeal R).IsPrincipal :=
    ((Submodule.spanFinrank_eq_one_iff (maximalIdeal R)).mp hspan).1
  obtain ⟨π, hπspan⟩ := hprincipal
  have hπdvd : π ∣ a := by
    rw [hπspan, Ideal.mem_span_singleton] at hamem
    exact hamem
  obtain ⟨b, hab⟩ := hπdvd
  have haRegular : IsRegular a :=
    (Commute.isRegular_iff (Commute.all a)).mpr ha
  have hπRegular : IsRegular π := by
    rw [hab] at haRegular
    exact haRegular.of_mul_left
  have hπne : π ≠ 0 := hπRegular.left.ne_zero
  have hπprimeIdeal : (Ideal.span {π}).IsPrime := by
    change Ideal.IsPrime (R ∙ π : Ideal R)
    rw [← hπspan]
    infer_instance
  have hπprime : Prime π := (Ideal.span_singleton_prime hπne).mp hπprimeIdeal
  exact Kummer.isDomain_of_prime_isSMulRegular hπprime hπRegular.left

/-- The local ring at a Cartier component generic point is a domain when
the ambient scheme is regular along the divisor. No global integrality of
`X` is assumed. -/
theorem isDomain_stalk_componentGenericPoint
    {X : Scheme.{u}} [IsLocallyNoetherian X]
    (D : X.EffectiveCartierDivisor) (hreg : D.1.IsAmbientRegularAlongSupport)
    (Z : Set D.1.subscheme) (hZ : Z ∈ irreducibleComponents D.1.subscheme) :
    IsDomain (X.presheaf.stalk (D.1.componentGenericPoint Z hZ)) := by
  let x : X := D.1.componentGenericPoint Z hZ
  let R := X.presheaf.stalk x
  let : IsRegularLocalRing R := hreg.isRegularAt_componentGenericPoint Z hZ
  have hdim : ringKrullDim R = ((1 : ℕ∞) : WithBot ℕ∞) := by
    rw [show ringKrullDim R = (Order.coheight x : WithBot ℕ∞) from
      ringKrullDim_stalk_eq_coheight x]
    exact congrArg (fun n : ℕ∞ ↦ (n : WithBot ℕ∞))
      (D.2.coheight_componentGenericPoint_eq_one Z hZ)
  obtain ⟨a, hareg, hIa⟩ := D.2.exists_regular_stalkIdeal_generator x
  have hxSupport : x ∈ D.1.support := D.1.componentGenericPoint_mem_support Z hZ
  have hstalk : D.1.stalkIdeal x ≤ maximalIdeal R := by
    refine iSup_le fun U ↦ iSup_le fun hxU ↦ ?_
    rw [Ideal.map_le_iff_le_comap]
    intro f hf
    change X.presheaf.germ U.1 x hxU f ∈ maximalIdeal R
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro haUnit
    have hxZero : x ∈ X.zeroLocus (D.1.ideal U : Set Γ(X, U.1)) :=
      (D.1.mem_support_iff_of_mem hxU).mp hxSupport
    have hnotBasic : x ∉ X.basicOpen f :=
      (X.mem_zeroLocus_iff (D.1.ideal U : Set Γ(X, U.1)) x).mp hxZero f hf
    exact hnotBasic ((X.mem_basicOpen f x hxU).mpr haUnit)
  have hamem : a ∈ maximalIdeal R := hstalk (by
    rw [hIa]
    exact Ideal.mem_span_singleton_self a)
  exact isDomain_of_regularLocal_dimension_one_of_regularElement hdim a hareg.left hamem

/-- The local ring at a generic point of an effective Cartier component is
a DVR under regularity along the divisor. Both its domain structure and its
one-dimensional regularity are obtained from the stated geometric data. -/
theorem isDiscreteValuationRing_stalk_componentGenericPoint
    {X : Scheme.{u}} [IsLocallyNoetherian X]
    (D : X.EffectiveCartierDivisor) (hreg : D.1.IsAmbientRegularAlongSupport)
    (Z : Set D.1.subscheme) (hZ : Z ∈ irreducibleComponents D.1.subscheme) :
    letI : IsDomain (X.presheaf.stalk (D.1.componentGenericPoint Z hZ)) :=
      isDomain_stalk_componentGenericPoint D hreg Z hZ
    IsDiscreteValuationRing (X.presheaf.stalk (D.1.componentGenericPoint Z hZ)) := by
  let x : X := D.1.componentGenericPoint Z hZ
  let : IsDomain (X.presheaf.stalk x) := isDomain_stalk_componentGenericPoint D hreg Z hZ
  let hregular : IsRegularLocalRing (X.presheaf.stalk x) :=
    hreg.isRegularAt_componentGenericPoint Z hZ
  apply IsLocalRing.finrank_CotangentSpace_eq_one_iff.mp
  have hdim :
      ((Module.finrank
          (ResidueField (X.presheaf.stalk x))
          (CotangentSpace (X.presheaf.stalk x)) : ℕ∞) : WithBot ℕ∞) =
        ((1 : ℕ∞) : WithBot ℕ∞) := by
    calc
      ((Module.finrank
          (ResidueField (X.presheaf.stalk x))
          (CotangentSpace (X.presheaf.stalk x)) : ℕ∞) : WithBot ℕ∞) =
          ringKrullDim (X.presheaf.stalk x) :=
        (IsRegularLocalRing.iff_finrank_cotangentSpace (X.presheaf.stalk x)).mp hregular
      _ = (Order.coheight x : WithBot ℕ∞) := ringKrullDim_stalk_eq_coheight x
      _ = ((1 : ℕ∞) : WithBot ℕ∞) :=
        congrArg (fun n : ℕ∞ ↦ (n : WithBot ℕ∞))
          (D.2.coheight_componentGenericPoint_eq_one Z hZ)
  exact ENat.natCast_inj.mp (WithBot.coe_eq_coe.mp hdim)

end EtaleFundamentalGroups
