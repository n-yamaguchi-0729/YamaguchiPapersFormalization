/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Kummer.NormalCrossings.EtaleBranchCharacteristicZero
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra

/-!
# Locally horizontal component branches on etale charts

Only the boundary components through the chosen point need to dominate the
base in order to obtain characteristic zero along all branches at that point.
The canonical height-one prime of any specified incident component lifts to
the strict etale chart, with its contraction recorded explicitly.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

private theorem Ideal.isPrime_transport_stalk
    {T : Scheme.{u}} {x x' : T} (h : x = x')
    (p : Ideal (T.presheaf.stalk x)) (hp : p.IsPrime) :
    (h ▸ p).IsPrime := by
  subst x'
  exact hp

private theorem Ideal.height_transport_stalk
    {T : Scheme.{u}} {x x' : T} (h : x = x')
    (p : Ideal (T.presheaf.stalk x)) :
    (h ▸ p).height = p.height := by
  subst x'
  rfl

private theorem AlgebraicGeometry.Scheme.IdealSheafData.stalkIdeal_le_transport
    {T : Scheme.{u}} (I : T.IdealSheafData) {x x' : T} (h : x = x')
    {p : Ideal (T.presheaf.stalk x)} (hp : I.stalkIdeal x ≤ p) :
    I.stalkIdeal x' ≤ h ▸ p := by
  subst x'
  exact hp

private theorem Ideal.height_eq_height_comap_of_flat_of_quasiFinite
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (q : Ideal S) [q.IsPrime]
    (hflat : f.Flat) (hqf : f.QuasiFinite)
    [IsNoetherianRing R] [IsNoetherianRing S] :
    q.height = (q.comap f).height := by
  let : Algebra R S := f.toAlgebra
  let : Module.Flat R S := hflat
  let : Algebra.QuasiFinite R S := hqf
  let p : Ideal R := q.comap f
  let : p.IsPrime := Ideal.IsPrime.comap f
  let : q.LiesOver p := ⟨rfl⟩
  let π : S →+* S ⧸ p.map (algebraMap R S) :=
    Ideal.Quotient.mk (p.map (algebraMap R S))
  let qbar : Ideal (S ⧸ p.map (algebraMap R S)) := q.map π
  have hpmap_le_q : p.map (algebraMap R S) ≤ q := by
    rw [Ideal.map_le_iff_le_comap]
    exact le_rfl
  let : qbar.IsPrime := by
    apply Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective
    change RingHom.ker π ≤ q
    dsimp only [π]
    rw [Ideal.mk_ker]
    exact hpmap_le_q
  have hqbar_min : qbar ∈ minimalPrimes (S ⧸ p.map (algebraMap R S)) := by
    rw [minimalPrimes_eq_minimals]
    refine ⟨inferInstance, ?_⟩
    intro J hJ hJq
    let : J.IsPrime := hJ
    let Q : Ideal S := J.comap π
    let : Q.IsPrime := Ideal.IsPrime.comap π
    have hqbar_comap : qbar.comap π = q := by
      rw [Ideal.comap_map_of_surjective π Ideal.Quotient.mk_surjective]
      exact sup_eq_left.mpr <| by
        change RingHom.ker π ≤ q
        dsimp only [π]
        rw [Ideal.mk_ker]
        exact hpmap_le_q
    have hQq : Q ≤ q := by
      change J.comap π ≤ q
      rw [← hqbar_comap]
      exact Ideal.comap_mono hJq
    have hp_le_underQ : p ≤ Q.under R := by
      intro x hx
      change f x ∈ Q
      change π (f x) ∈ J
      have hxf : f x ∈ p.map (algebraMap R S) :=
        Ideal.mem_map_of_mem (algebraMap R S) hx
      have hzero : π (f x) = 0 := by
        dsimp only [π]
        rw [Ideal.Quotient.eq_zero_iff_mem]
        exact hxf
      rw [hzero]
      exact J.zero_mem
    have hunderQ_le : Q.under R ≤ p := by
      exact (Ideal.comap_mono hQq).trans_eq rfl
    have hunderQ : Q.under R = p := le_antisymm hunderQ_le hp_le_underQ
    have hQeq : Q = q :=
      Algebra.QuasiFinite.eq_of_le_of_under_eq
        (R := R) Q q hQq hunderQ
    have hEq : qbar = J := by
      calc
        qbar = q.map π := rfl
        _ = Q.map π := congrArg (fun K : Ideal S ↦ K.map π) hQeq.symm
        _ = J := Ideal.map_comap_of_surjective π
          Ideal.Quotient.mk_surjective J
    exact hEq.le
  have hqbar_height : qbar.height = 0 :=
    Ideal.height_eq_zero_iff.mpr hqbar_min
  calc
    q.height = p.height + qbar.height :=
      Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown p q
    _ = p.height := by rw [hqbar_height, add_zero]
    _ = (q.comap f).height := rfl

namespace AlgebraicGeometry.Scheme.EffectiveCartierDivisor

variable {X S : Scheme.{u}}

/-- Exactly the components through `z` dominate the base. -/
def ComponentsThroughPointAreHorizontal
    (D : EffectiveCartierDivisor X) (structural : X ⟶ S)
    (z : D.1.subscheme) : Prop :=
  ∀ (Z : Set D.1.subscheme)
    (hZ : Z ∈ irreducibleComponents D.1.subscheme),
    z ∈ Z → DenseRange (D.1.componentToBase structural Z hZ)

/-- Local componentwise horizontality at a divisor point forces
characteristic zero along every height-one branch through that point. -/
theorem ComponentsThroughPointAreHorizontal.hasCharacteristicZeroBranchesAt
    [IsLocallyNoetherian X] [IsIntegral S]
    (D : EffectiveCartierDivisor X) (structural : X ⟶ S)
    {z : D.1.subscheme}
    (hD : D.ComponentsThroughPointAreHorizontal structural z)
    [CharZero (S.residueField (genericPoint S))] :
    D.1.HasCharacteristicZeroBranchesAt (D.1.subschemeι z) := by
  let I : X.IdealSheafData := D.1
  dsimp only [Scheme.IdealSheafData.HasCharacteristicZeroBranchesAt]
  intro q hqPrime hqHeight hIq
  let : q.IsPrime := hqPrime
  let qSpec : Spec (X.presheaf.stalk (I.subschemeι z)) := ⟨q, hqPrime⟩
  obtain ⟨Z, hZ, hgeneric⟩ :=
    D.2.exists_componentGenericPoint_eq_fromSpecStalk
      (I.subschemeι z) qSpec hqHeight hIq
  have hfromSpec :
      X.fromSpecStalk (I.subschemeι z) qSpec ⤳ I.subschemeι z := by
    have hmem : X.fromSpecStalk (I.subschemeι z) qSpec ∈
        Set.range (X.fromSpecStalk (I.subschemeι z)) := ⟨qSpec, rfl⟩
    rw [Scheme.range_fromSpecStalk] at hmem
    exact hmem
  have hgenericSpecializes :
      I.componentGenericPoint Z hZ ⤳ I.subschemeι z := by
    rw [hgeneric]
    exact hfromSpec
  have hzZ : z ∈ Z := by
    apply (genericPoints.isGenericPoint_ofComponent
      (⟨Z, hZ⟩ : irreducibleComponents I.subscheme)).specializes_iff_mem.mp
    apply I.subschemeι.isClosedEmbedding.isInducing.specializes_iff.mp
    rw [← I.componentGenericPoint_eq Z hZ]
    exact hgenericSpecializes
  let eta := I.componentGenericPoint Z hZ
  have hetaBase : structural eta = genericPoint S := by
    exact I.componentToBase_genericPoint structural Z hZ (hD Z hZ hzZ)
  let eBase : S.residueField (genericPoint S) ≃+*
      S.residueField (structural eta) :=
    (S.residueFieldCongr hetaBase.symm).commRingCatIsoToRingEquiv
  let phi : S.residueField (genericPoint S) →+* X.residueField eta :=
    (structural.residueFieldMap eta).hom.comp eBase.toRingHom
  let : CharZero (X.residueField eta) :=
    charZero_of_injective_ringHom phi.injective
  let ePoint : X.residueField eta ≃+*
      X.residueField (X.fromSpecStalk (I.subschemeι z) qSpec) :=
    (X.residueFieldCongr hgeneric).commRingCatIsoToRingEquiv
  let e : X.residueField eta ≃+* q.ResidueField :=
    ePoint.trans (X.residueFieldFromSpecStalkEquiv (I.subschemeι z) qSpec)
  let : CharZero q.ResidueField := e.symm.toRingHom.charZero
  exact (algebraMap (X.presheaf.stalk (I.subschemeι z) ⧸ q)
    q.ResidueField).charZero

end AlgebraicGeometry.Scheme.EffectiveCartierDivisor

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X Y : Scheme.{u}}

/-- A height-one branch prime lifts through an etale stalk map.  The lifted
prime still contains the pulled-back boundary stalk ideal. -/
theorem exists_etaleHeightOnePrime_liesOver
    [IsLocallyNoetherian X]
    (I : X.IdealSheafData) (f : Y ⟶ X) [Etale f] (y : Y)
    (p : Ideal (X.presheaf.stalk (f y))) [p.IsPrime]
    (hpheight : p.height = 1) (hIp : I.stalkIdeal (f y) ≤ p) :
    ∃ (q : Ideal (Y.presheaf.stalk y)) (_hqPrime : q.IsPrime),
      q.height = 1 ∧ (I.comap f).stalkIdeal y ≤ q ∧
        q.comap (f.stalkMap y).hom = p := by
  let : IsLocallyNoetherian Y :=
    LocallyOfFiniteType.isLocallyNoetherian f
  let φ : X.presheaf.stalk (f y) →+* Y.presheaf.stalk y :=
    (f.stalkMap y).hom
  let : Algebra (X.presheaf.stalk (f y)) (Y.presheaf.stalk y) :=
    φ.toAlgebra
  let : IsLocalHom φ := by
    dsimp only [φ]
    infer_instance
  let : Module.Flat (X.presheaf.stalk (f y)) (Y.presheaf.stalk y) :=
    Flat.stalkMap f y
  let : Module.FaithfullyFlat
      (X.presheaf.stalk (f y)) (Y.presheaf.stalk y) :=
    Module.FaithfullyFlat.of_flat_of_isLocalHom
  obtain ⟨q, hqPrime, hqOver⟩ :=
    Ideal.exists_isPrime_liesOver_of_faithfullyFlat
      (B := Y.presheaf.stalk y) p
  let : q.IsPrime := hqPrime
  have hqcomap : q.comap φ = p := hqOver.over.symm
  have hφqf : φ.QuasiFinite := by
    let : Algebra.EssFiniteType
        (X.presheaf.stalk (f y)) (Y.presheaf.stalk y) :=
      LocallyOfFiniteType.stalkMap f y
    let : Algebra.FormallyUnramified
        (X.presheaf.stalk (f y)) (Y.presheaf.stalk y) :=
      FormallyUnramified.stalkMap f y
    change Algebra.QuasiFinite
      (X.presheaf.stalk (f y)) (Y.presheaf.stalk y)
    exact inferInstance
  have hqheight : q.height = 1 := by
    rw [Ideal.height_eq_height_comap_of_flat_of_quasiFinite
      φ q (Flat.stalkMap f y) hφqf, hqcomap, hpheight]
  let qSpec : Spec (Y.presheaf.stalk y) := ⟨q, hqPrime⟩
  let pSpec : Spec (X.presheaf.stalk (f y)) := ⟨p, inferInstance⟩
  have hpoint :
      X.fromSpecStalk (f y) pSpec = f (Y.fromSpecStalk y qSpec) := by
    have hSpecMap : Spec.map (f.stalkMap y) qSpec = pSpec := by
      apply PrimeSpectrum.ext
      exact hqcomap
    rw [← hSpecMap]
    change
      (Spec.map (f.stalkMap y) ≫ X.fromSpecStalk (f y)) qSpec =
        (Y.fromSpecStalk y ≫ f) qSpec
    exact congrArg (fun g ↦ g qSpec)
      (Scheme.SpecMap_stalkMap_fromSpecStalk f)
  have hpSupport : X.fromSpecStalk (f y) pSpec ∈ I.support :=
    (I.mem_support_fromSpecStalk_iff_stalkIdeal_le (f y) pSpec).2 hIp
  have hqSupport :
      Y.fromSpecStalk y qSpec ∈ (I.comap f).support := by
    rw [support_comap]
    change f (Y.fromSpecStalk y qSpec) ∈ I.support
    rw [← hpoint]
    exact hpSupport
  have hIq : (I.comap f).stalkIdeal y ≤ q :=
    ((I.comap f).mem_support_fromSpecStalk_iff_stalkIdeal_le y qSpec).1
      hqSupport
  exact ⟨q, hqPrime, hqheight, hIq, hqcomap⟩

end AlgebraicGeometry.Scheme.IdealSheafData

namespace AlgebraicGeometry.Scheme.EffectiveCartierDivisor

variable {X Y S : Scheme.{u}}

/-- The canonical branch prime of a specified divisor component has a
height-one lift on every pointed etale neighbourhood.  The final equality
is literal lying-over after transporting the original branch ideal along
the equality of centre points. -/
theorem exists_etaleHeightOnePrime_over_componentBranchPrimeAt
    [IsLocallyNoetherian X]
    (D : EffectiveCartierDivisor X)
    (Z : Set D.1.subscheme)
    (hZ : Z ∈ irreducibleComponents D.1.subscheme)
    (z : D.1.subscheme) (hz : z ∈ Z)
    (f : Y ⟶ X) [Etale f] (y : Y)
    (hfy : f y = D.1.subschemeι z) :
    let p : Ideal (X.presheaf.stalk (f y)) :=
      hfy.symm ▸ (D.1.componentBranchPrimeAt Z hZ z hz).asIdeal
    ∃ (q : Ideal (Y.presheaf.stalk y)) (_hqPrime : q.IsPrime),
      q.height = 1 ∧ (D.1.comap f).stalkIdeal y ≤ q ∧
        q.comap (f.stalkMap y).hom = p := by
  dsimp only
  let e : D.1.subschemeι z = f y := hfy.symm
  let p : Ideal (X.presheaf.stalk (f y)) :=
    e ▸ (D.1.componentBranchPrimeAt Z hZ z hz).asIdeal
  have hbranchPrime :
      (D.1.componentBranchPrimeAt Z hZ z hz).asIdeal.IsPrime :=
    (D.1.componentBranchPrimeAt Z hZ z hz).isPrime
  have hpPrime : p.IsPrime := Ideal.isPrime_transport_stalk e
    (D.1.componentBranchPrimeAt Z hZ z hz).asIdeal hbranchPrime
  let : p.IsPrime := hpPrime
  have hpheight : p.height = 1 := by
    rw [Ideal.height_transport_stalk e]
    exact D.2.componentBranchPrimeAt_height_eq_one Z hZ z hz
  have hIp : D.1.stalkIdeal (f y) ≤ p := by
    exact D.1.stalkIdeal_le_transport e
      (D.1.stalkIdeal_le_componentBranchPrimeAt Z hZ z hz)
  exact @Scheme.IdealSheafData.exists_etaleHeightOnePrime_liesOver
    X Y inferInstance D.1 f inferInstance y p hpPrime hpheight hIp

/-- A normal-crossings point with only its incident components horizontal
admits a strict etale chart carrying both characteristic-zero branches and
a height-one prime lying over the canonical branch of a specified incident
component. -/
theorem ComponentsThroughPointAreHorizontal.exists_etaleStrictChart_componentBranch
    [IsLocallyNoetherian X] [IsIntegral S]
    (D : EffectiveCartierDivisor X) (structural : X ⟶ S)
    (Z : Set D.1.subscheme)
    (hZ : Z ∈ irreducibleComponents D.1.subscheme)
    (z : D.1.subscheme) (hz : z ∈ Z)
    (hD : D.ComponentsThroughPointAreHorizontal structural z)
    [CharZero (S.residueField (genericPoint S))]
    (hNC : D.1.IsNormalCrossingsAt (D.1.subschemeι z)) :
    ∃ (U : Scheme.{u}) (f : U ⟶ X) (u : U)
      (hfu : f u = D.1.subschemeι z),
      Etale f ∧ (D.1.comap f).IsStrictNormalCrossings ∧
        (D.1.comap f).HasCharacteristicZeroBranchesAt u ∧
          let p : Ideal (X.presheaf.stalk (f u)) :=
            hfu.symm ▸ (D.1.componentBranchPrimeAt Z hZ z hz).asIdeal
          ∃ (q : Ideal (U.presheaf.stalk u)) (_hqPrime : q.IsPrime),
            q.height = 1 ∧ (D.1.comap f).stalkIdeal u ≤ q ∧
              q.comap (f.stalkMap u).hom = p := by
  obtain ⟨U, f, u, hf, hfu, hstrict⟩ := hNC
  let : Etale f := hf
  refine ⟨U, f, u, hfu, hf, hstrict, ?_, ?_⟩
  · apply Scheme.IdealSheafData.HasCharacteristicZeroBranchesAt.comap_of_etale
      f u
    simpa only [hfu] using
      hD.hasCharacteristicZeroBranchesAt D structural
  · exact D.exists_etaleHeightOnePrime_over_componentBranchPrimeAt
      Z hZ z hz f u hfu

end AlgebraicGeometry.Scheme.EffectiveCartierDivisor

end
