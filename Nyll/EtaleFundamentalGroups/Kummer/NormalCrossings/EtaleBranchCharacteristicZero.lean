/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.FiniteEtale.Boundary.ArithmeticAllBranchCharacteristicZero
import Nyll.SchemeTheory.Divisors.LocalComplement
import Nyll.SchemeTheory.Divisors.SurjectiveArithmeticBoundary
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem

/-!
# Characteristic-zero branches on etale normal-crossings charts

Height-one primes contract to height-one primes along an etale stalk map.
Consequently, characteristic zero along every branch of a horizontal
boundary passes to the strict chart witnessing normal crossings.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

private theorem Ideal.height_comap_eq_one_of_flat_of_quasiFinite
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (q : Ideal S) [q.IsPrime]
    (hflat : f.Flat) (hqf : f.QuasiFinite)
    [IsNoetherianRing R] [IsNoetherianRing S] (hq : q.height = 1) :
    (q.comap f).height = 1 := by
  let : Algebra R S := f.toAlgebra
  let : Module.Flat R S := hflat
  let : Algebra.QuasiFinite R S := hqf
  let p : Ideal R := q.comap f
  let : p.IsPrime := Ideal.IsPrime.comap f
  let : q.LiesOver p := ⟨rfl⟩
  have hheight :=
    Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown p q
  have hp_le_q : p.height ≤ q.height := by
    rw [hheight]
    exact le_add_right (le_refl _)
  have hp_le_one : p.height ≤ 1 := by
    simpa only [hq] using hp_le_q
  rcases Order.le_one_iff.mp hp_le_one with hp | hp
  · have hpmin : p ∈ minimalPrimes R :=
      Ideal.height_eq_zero_iff.mp hp
    rw [minimalPrimes_eq_minimals] at hpmin
    have hqmin : q ∈ minimalPrimes S := by
      rw [minimalPrimes_eq_minimals]
      refine ⟨inferInstance, ?_⟩
      intro Q hQ hQq
      let : Q.IsPrime := hQ
      have hunder_le : Q.under R ≤ p :=
        Ideal.comap_mono hQq
      have hunder_eq : Q.under R = p :=
        le_antisymm hunder_le (hpmin.2 inferInstance hunder_le)
      have hQeq : Q = q :=
        Algebra.QuasiFinite.eq_of_le_of_under_eq
          (R := R) Q q hQq hunder_eq
      exact hQeq.ge
    have hqzero : q.height = 0 :=
      Ideal.height_eq_zero_iff.mpr hqmin
    exact (one_ne_zero (hq.symm.trans hqzero)).elim
  · exact hp

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X Y : Scheme.{u}}

/-- Characteristic zero along every height-one boundary branch passes through
an etale chart.  The proof contracts a chart prime through the stalk map;
support functoriality supplies containment of the original stalk ideal, so no
affineness hypothesis or global stalk-ideal comparison is required. -/
theorem HasCharacteristicZeroBranchesAt.comap_of_etale
    [IsLocallyNoetherian X]
    {I : X.IdealSheafData} (f : Y ⟶ X) [Etale f] (y : Y)
    (hI : I.HasCharacteristicZeroBranchesAt (f y)) :
    (I.comap f).HasCharacteristicZeroBranchesAt y := by
  let : IsLocallyNoetherian Y :=
    LocallyOfFiniteType.isLocallyNoetherian f
  intro q hqPrime hqheight hIq
  let : q.IsPrime := hqPrime
  let φ : X.presheaf.stalk (f y) →+* Y.presheaf.stalk y :=
    (f.stalkMap y).hom
  let p : Ideal (X.presheaf.stalk (f y)) := q.comap φ
  let : p.IsPrime := Ideal.IsPrime.comap φ
  have hφqf : φ.QuasiFinite := by
    let : Algebra (X.presheaf.stalk (f y)) (Y.presheaf.stalk y) :=
      φ.toAlgebra
    let : Algebra.EssFiniteType
        (X.presheaf.stalk (f y)) (Y.presheaf.stalk y) :=
      LocallyOfFiniteType.stalkMap f y
    let : Algebra.FormallyUnramified
        (X.presheaf.stalk (f y)) (Y.presheaf.stalk y) :=
      FormallyUnramified.stalkMap f y
    change Algebra.QuasiFinite
      (X.presheaf.stalk (f y)) (Y.presheaf.stalk y)
    exact inferInstance
  have hpheight : p.height = 1 :=
    Ideal.height_comap_eq_one_of_flat_of_quasiFinite
      φ q (Flat.stalkMap f y) hφqf hqheight
  let qSpec : Spec (Y.presheaf.stalk y) := ⟨q, hqPrime⟩
  let pSpec : Spec (X.presheaf.stalk (f y)) := ⟨p, inferInstance⟩
  have hpoint :
      X.fromSpecStalk (f y) pSpec = f (Y.fromSpecStalk y qSpec) := by
    change
      (Spec.map (f.stalkMap y) ≫ X.fromSpecStalk (f y)) qSpec =
        (Y.fromSpecStalk y ≫ f) qSpec
    exact congrArg (fun g ↦ g qSpec)
      (Scheme.SpecMap_stalkMap_fromSpecStalk f)
  have hySupport :
      Y.fromSpecStalk y qSpec ∈ (I.comap f).support :=
    ((I.comap f).mem_support_fromSpecStalk_iff_stalkIdeal_le y qSpec).2 hIq
  have hpSupport : X.fromSpecStalk (f y) pSpec ∈ I.support := by
    rw [hpoint]
    rw [support_comap] at hySupport
    exact hySupport
  have hIp : I.stalkIdeal (f y) ≤ p :=
    (I.mem_support_fromSpecStalk_iff_stalkIdeal_le (f y) pSpec).1 hpSupport
  let : CharZero (X.presheaf.stalk (f y) ⧸ p) :=
    hI p inferInstance hpheight hIp
  exact charZero_of_injective_ringHom
    (Ideal.quotientMap_injective (I := q) (f := φ))

end AlgebraicGeometry.Scheme.IdealSheafData

namespace AlgebraicGeometry.Scheme.EffectiveCartierDivisor

variable {X S : Scheme.{u}}

/-- A horizontal normal-crossings boundary has an etale strict chart whose
height-one boundary branches all have characteristic zero. -/
theorem IsHorizontalOver.exists_etaleStrictChart_hasCharacteristicZeroBranchesAt
    [IsLocallyNoetherian X] [IsIntegral S]
    (D : EffectiveCartierDivisor X) (structural : X ⟶ S)
    (hHorizontal : D.IsHorizontalOver structural)
    [CharZero (S.residueField (genericPoint S))]
    {x : X} (hNC : D.1.IsNormalCrossingsAt x) :
    ∃ (U : Scheme.{u}) (f : U ⟶ X) (u : U),
      Etale f ∧ f u = x ∧ (D.1.comap f).IsStrictNormalCrossings ∧
        (D.1.comap f).HasCharacteristicZeroBranchesAt u := by
  obtain ⟨U, f, u, hf, hfu, hstrict⟩ := hNC
  let : Etale f := hf
  refine ⟨U, f, u, hf, hfu, hstrict, ?_⟩
  apply IdealSheafData.HasCharacteristicZeroBranchesAt.comap_of_etale f u
  simpa only [hfu] using
    hHorizontal.hasCharacteristicZeroBranchesAt D structural (f u)

section IntegerBase

local instance : IsDomain (ULift.{u} ℤ) :=
  (ULift.ringEquiv : ULift.{u} ℤ ≃+* ℤ).toMulEquiv.isDomain ℤ

/-- Integer-base specialization of the horizontal etale-chart theorem. -/
theorem IsHorizontalOver.exists_etaleStrictChart_hasCharacteristicZeroBranchesAt_overIntegers
    [IsLocallyNoetherian X]
    (D : EffectiveCartierDivisor X)
    (hHorizontal : D.IsHorizontalOver (specULiftZIsTerminal.from X))
    {x : X} (hNC : D.1.IsNormalCrossingsAt x) :
    ∃ (U : Scheme.{u}) (f : U ⟶ X) (u : U),
      Etale f ∧ f u = x ∧ (D.1.comap f).IsStrictNormalCrossings ∧
        (D.1.comap f).HasCharacteristicZeroBranchesAt u := by
  let B := Spec (CommRingCat.of (ULift.{u} ℤ))
  let e : B.residueField (genericPoint B) ≃+* ℚ :=
    specULiftZGenericResidueFieldEquivQ
  let : CharZero (B.residueField (genericPoint B)) :=
    e.toRingHom.charZero
  exact hHorizontal.exists_etaleStrictChart_hasCharacteristicZeroBranchesAt
    D (specULiftZIsTerminal.from X) hNC

/-- Componentwise surjectivity over the integer base supplies the same
characteristic-zero etale strict chart. -/
theorem HasSurjectiveComponentsOverIntegers.exists_etaleStrictChart_hasCharacteristicZeroBranchesAt
    [IsLocallyNoetherian X]
    (D : EffectiveCartierDivisor X)
    (hD : D.HasSurjectiveComponentsOverIntegers)
    {x : X} (hNC : D.1.IsNormalCrossingsAt x) :
    ∃ (U : Scheme.{u}) (f : U ⟶ X) (u : U),
      Etale f ∧ f u = x ∧ (D.1.comap f).IsStrictNormalCrossings ∧
        (D.1.comap f).HasCharacteristicZeroBranchesAt u :=
  IsHorizontalOver.exists_etaleStrictChart_hasCharacteristicZeroBranchesAt_overIntegers
    D hD.isHorizontalOverIntegers hNC

end IntegerBase

end AlgebraicGeometry.Scheme.EffectiveCartierDivisor

end
