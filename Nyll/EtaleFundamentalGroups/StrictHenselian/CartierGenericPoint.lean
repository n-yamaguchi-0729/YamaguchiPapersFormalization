/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.StrictHenselian.GeometricStalkDVR
import Nyll.EtaleFundamentalGroups.StrictHenselian.GeometricStalkNormalDomain
import Nyll.EtaleFundamentalGroups.StrictHenselian.GeometricStalkFlat
import Nyll.EtaleFundamentalGroups.LocalGeometry.HeightOne.CartierComponentStalkDVR
import Nyll.SchemeTheory.Divisors.LocalComplement
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Nyll.SchemeTheory.Divisors.RegularCartier


/-!
# The strict-Henselian generic point of a Cartier boundary

The fraction field of the actual geometric etale stalk maps to the complement
of an effective Cartier divisor. Its structure map is injective, whereas the
stalk ideal of a Cartier divisor contains a regular element. Normality of the
base local ring supplies the domain property of the geometric stalk. This proves that
the generic point misses the divisor, and constructs the required factorization
through the open complement. At a regular boundary component the DVR input is
obtained from the component's actual local ring.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

namespace EtaleFundamentalGroups.StrictHenselian

universe u

private theorem fieldFromStalk_mem_complement
    {X : Scheme.{u}} (D : X.EffectiveCartierDivisor) (x : X)
    {F : Type u} [Field F] (a : X.presheaf.stalk x →+* F)
    (ha : Function.Injective a) (y : Spec (.of F)) :
    X.fromSpecStalk x (Spec.map (CommRingCat.ofHom a) y) ∈ D.1.supportComplement := by
  intro hy
  have hle := (D.1.mem_support_fromSpecStalk_iff_stalkIdeal_le x
    (Spec.map (CommRingCat.ofHom a) y)).mp hy
  obtain ⟨t, ht, hIt⟩ := D.2.exists_regular_stalkIdeal_generator x
  have htI : t ∈ D.1.stalkIdeal x := by
    rw [hIt]
    exact Ideal.mem_span_singleton_self t
  have hat : a t ∈ y.asIdeal := hle htI
  have hybot : y.asIdeal = ⊥ :=
    congrArg PrimeSpectrum.asIdeal (Subsingleton.elim y (⊥ : PrimeSpectrum F))
  rw [hybot, Ideal.mem_bot] at hat
  exact ht.left.ne_zero (ha (hat.trans (map_zero a).symm))

/-- The generic point of the actual geometric etale stalk factors through the
Cartier complement over any normal domain stalk. The displayed source is the
fraction field of that geometric stalk. -/
def geometricStalkFractionFieldToComplement
    {X : Scheme.{u}} (D : X.EffectiveCartierDivisor) (x : X)
    [IsDomain (X.presheaf.stalk x)] [IsIntegrallyClosed (X.presheaf.stalk x)]
    {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (φ : X.presheaf.stalk x →+* Ω) [IsLocalHom φ] :
    Spec (.of (FractionRing (geometricStalk (Spec.map (CommRingCat.ofHom φ))))) ⟶
      D.1.supportComplement := by
  let S := geometricStalk (Spec.map (CommRingCat.ofHom φ))
  let a : X.presheaf.stalk x →+* FractionRing S :=
    (algebraMap S (FractionRing S)).comp (geometricStalkStructureMap φ)
  have ha : Function.Injective a :=
    (IsFractionRing.injective S (FractionRing S)).comp
      (geometricStalkStructureMap_injective φ)
  apply IsOpenImmersion.lift D.1.supportComplement.ι
    (Spec.map (CommRingCat.ofHom a) ≫ X.fromSpecStalk x)
  rw [Scheme.Opens.range_ι]
  rintro _ ⟨y, rfl⟩
  exact fieldFromStalk_mem_complement D x a ha y

/-- The constructed morphism has the original local structure morphism as its
composite with the open inclusion. -/
@[reassoc]
theorem geometricStalkFractionFieldToComplement_comp_ι
    {X : Scheme.{u}} (D : X.EffectiveCartierDivisor) (x : X)
    [IsDomain (X.presheaf.stalk x)] [IsIntegrallyClosed (X.presheaf.stalk x)]
    {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (φ : X.presheaf.stalk x →+* Ω) [IsLocalHom φ] :
    geometricStalkFractionFieldToComplement D x φ ≫ D.1.supportComplement.ι =
      Spec.map (CommRingCat.ofHom
        ((algebraMap (geometricStalk (Spec.map (CommRingCat.ofHom φ)))
          (FractionRing (geometricStalk (Spec.map (CommRingCat.ofHom φ))))).comp
            (geometricStalkStructureMap φ))) ≫ X.fromSpecStalk x := by
  exact IsOpenImmersion.lift_fac _ _ _

/-- At a regular Cartier component, the residue map into its algebraic closure
constructs the strict-Henselian generic point used for divisorial inertia.
The DVR properties are derived from regularity along the boundary. -/
def cartierComponentStrictHenselianGenericMorphism
    {X : Scheme.{u}} [IsLocallyNoetherian X]
    (D : X.EffectiveCartierDivisor) (hreg : D.IsAmbientRegularAlongSupport)
    (Z : Set D.1.subscheme) (hZ : Z ∈ irreducibleComponents D.1.subscheme) :
    let x := D.1.componentGenericPoint Z hZ
    let φ := (algebraMap (IsLocalRing.ResidueField (X.presheaf.stalk x))
      (AlgebraicClosure (IsLocalRing.ResidueField (X.presheaf.stalk x)))).comp
      (IsLocalRing.residue (X.presheaf.stalk x))
    Spec (.of (FractionRing (geometricStalk (Spec.map (CommRingCat.ofHom φ))))) ⟶
      D.1.supportComplement := by
  intro x φ
  letI : IsDomain (X.presheaf.stalk x) := isDomain_stalk_componentGenericPoint D hreg Z hZ
  letI : IsDiscreteValuationRing (X.presheaf.stalk x) :=
    isDiscreteValuationRing_stalk_componentGenericPoint D hreg Z hZ
  letI : IsLocalHom φ := RingHom.isLocalHom_comp
    (algebraMap (IsLocalRing.ResidueField (X.presheaf.stalk x))
      (AlgebraicClosure (IsLocalRing.ResidueField (X.presheaf.stalk x))))
    (IsLocalRing.residue (X.presheaf.stalk x))
  exact geometricStalkFractionFieldToComplement D x φ

end EtaleFundamentalGroups.StrictHenselian
