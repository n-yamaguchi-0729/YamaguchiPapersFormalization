/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.FiniteEtale.BaseChange.GenericTensorComponent
import EtaleFundamentalGroups.Normalization.Localization.IntegralClosureAtPrimeEquiv

/-!
# Away components at height-one primes

This file closes the height-one branch disjoint from a boundary equation.
For a prime `q` disjoint from the powers of `f`, the element `f` is a unit in
`D_q`.  A chosen fraction field of `D[1/f]` maps canonically to a chosen
fraction field of `D`; the latter is also the fraction field of `D_q` under
the canonical localization map.  These maps let the finite-etale away
component theorem feed directly into the localized-normalization target used
by purity, while retaining the specified maximal tensor component.
-/

noncomputable section

open scoped TensorProduct

namespace EtaleFundamentalGroups

universe uD uC uF uE uK

/-- The existence of a fraction field for `D[1/f]` forces `f` to be
nonzero.  This is the source of the nonvanishing needed by the canonical
map to a fraction field of `D`. -/
theorem awayElement_ne_zero_of_isFractionRing
    {D : Type uD} {F : Type uF}
    [CommRing D] (f : D)
    [Field F] [Algebra (Localization.Away f) F]
    [IsFractionRing (Localization.Away f) F] :
    f ≠ 0 := by
  let S := Localization.Away f
  let : Nontrivial S := (algebraMap S F).domain_nontrivial
  intro hzero
  subst f
  have hu : IsUnit
      (algebraMap D (Localization.Away (0 : D)) (0 : D)) :=
    IsLocalization.map_units (Localization.Away (0 : D))
      (⟨0, Submonoid.mem_powers 0⟩ : Submonoid.powers (0 : D))
  have : IsUnit (0 : Localization.Away (0 : D)) := by
    simpa only [map_zero] using hu
  exact not_isUnit_zero this

/-- The canonical localization lift from `D[1/f]` to a chosen fraction
field of `D`. -/
noncomputable def awayToFractionFieldRingHom
    {D : Type uD} {F : Type uF} {K : Type uK}
    [CommRing D] [IsDomain D]
    (f : D)
    [Field F] [Algebra (Localization.Away f) F]
    [IsFractionRing (Localization.Away f) F]
    [Field K] [Algebra D K] [IsFractionRing D K] :
    Localization.Away f →+* K := by
  have hf : f ≠ 0 := awayElement_ne_zero_of_isFractionRing (F := F) f
  have hfK : IsUnit (algebraMap D K f) := by
    rw [isUnit_iff_ne_zero]
    simpa using (IsFractionRing.injective D K).ne hf
  exact IsLocalization.Away.lift f hfK

@[simp]
theorem awayToFractionFieldRingHom_algebraMap
    {D : Type uD} {F : Type uF} {K : Type uK}
    [CommRing D] [IsDomain D]
    (f : D)
    [Field F] [Algebra (Localization.Away f) F]
    [IsFractionRing (Localization.Away f) F]
    [Field K] [Algebra D K] [IsFractionRing D K]
    (x : D) :
    awayToFractionFieldRingHom (F := F) (K := K) f
        (algebraMap D (Localization.Away f) x) =
      algebraMap D K x := by
  unfold awayToFractionFieldRingHom
  apply IsLocalization.Away.lift_eq

/-- The canonical lift from `D[1/f]` to `Frac(D)` is injective. -/
theorem awayToFractionFieldRingHom_injective
    {D : Type uD} {F : Type uF} {K : Type uK}
    [CommRing D] [IsDomain D]
    (f : D)
    [Field F] [Algebra (Localization.Away f) F]
    [IsFractionRing (Localization.Away f) F]
    [Field K] [Algebra D K] [IsFractionRing D K] :
    Function.Injective
      (awayToFractionFieldRingHom (F := F) (K := K) f) := by
  let S := Localization.Away f
  let mapSK : S →+* K :=
    awayToFractionFieldRingHom (F := F) (K := K) f
  rw [IsLocalization.injective_iff_map_algebraMap_eq
    (Submonoid.powers f) mapSK]
  intro x y
  constructor
  · intro hxy
    exact congrArg mapSK hxy
  · intro hxy
    have hxy' : algebraMap D K x = algebraMap D K y := by
      calc
        algebraMap D K x = mapSK (algebraMap D S x) := by
          symm
          exact awayToFractionFieldRingHom_algebraMap
            (F := F) (K := K) f x
        _ = mapSK (algebraMap D S y) := hxy
        _ = algebraMap D K y :=
          awayToFractionFieldRingHom_algebraMap
            (F := F) (K := K) f y
    exact congrArg (algebraMap D S)
      ((IsFractionRing.injective D K) hxy')

/-- The canonical map from a chosen fraction field of `D[1/f]` to a chosen
fraction field of `D`.

The map on `D[1/f]` is the localization lift of `D -> K`; its injectivity and
the extension to `F` are produced internally. -/
@[reducible]
noncomputable def awayFractionFieldToFractionFieldAlgebra
    {D : Type uD} {F : Type uF} {K : Type uK}
    [CommRing D] [IsDomain D]
    (f : D)
    [Field F] [Algebra (Localization.Away f) F]
    [IsFractionRing (Localization.Away f) F]
    [Field K] [Algebra D K] [IsFractionRing D K] :
    Algebra F K :=
  (IsFractionRing.lift
    (awayToFractionFieldRingHom_injective (F := F) (K := K) f)).toAlgebra

@[simp]
theorem awayFractionFieldToFractionFieldAlgebra_algebraMap
    {D : Type uD} {F : Type uF} {K : Type uK}
    [CommRing D] [IsDomain D]
    (f : D)
    [Field F] [Algebra (Localization.Away f) F]
    [IsFractionRing (Localization.Away f) F]
    [Field K] [Algebra D K] [IsFractionRing D K]
    (x : Localization.Away f) :
    letI : Algebra F K :=
      awayFractionFieldToFractionFieldAlgebra f
    algebraMap F K (algebraMap (Localization.Away f) F x) =
      awayToFractionFieldRingHom (F := F) (K := K) f x := by
  let : Algebra F K := awayFractionFieldToFractionFieldAlgebra f
  exact IsFractionRing.lift_algebraMap
    (awayToFractionFieldRingHom_injective (F := F) (K := K) f) x

/-- The canonical fraction-field lift from `D[1/f]` is compatible with the
original maps from `D`. -/
theorem awayFractionFieldToFractionField_isScalarTower
    {D : Type uD} {F : Type uF} {K : Type uK}
    [CommRing D] [IsDomain D]
    (f : D)
    [Field F] [Algebra (Localization.Away f) F]
    [IsFractionRing (Localization.Away f) F]
    [Field K] [Algebra D K] [IsFractionRing D K] :
    letI : Algebra D F :=
      ((algebraMap (Localization.Away f) F).comp
        (algebraMap D (Localization.Away f))).toAlgebra
    letI : Algebra F K :=
      awayFractionFieldToFractionFieldAlgebra f
    IsScalarTower D F K := by
  let S := Localization.Away f
  let : Algebra D F :=
    ((algebraMap S F).comp (algebraMap D S)).toAlgebra
  let : Algebra F K := awayFractionFieldToFractionFieldAlgebra f
  apply IsScalarTower.of_algebraMap_eq
  intro x
  change algebraMap D K x =
    algebraMap F K (algebraMap S F (algebraMap D S x))
  rw [awayFractionFieldToFractionFieldAlgebra_algebraMap,
    awayToFractionFieldRingHom_algebraMap]

/-- If a prime is disjoint from every power of `f`, then `f` is a unit in
the localization at that prime. -/
theorem isUnit_localizationAtPrime_of_disjoint_powers
    {D : Type uD} [CommRing D]
    (f : D) (q : Ideal D) [q.IsPrime]
    (hdisj : Disjoint
      ((Submonoid.powers f : Submonoid D) : Set D) (q : Set D)) :
    IsUnit (algebraMap D (Localization.AtPrime q) f) := by
  have hfq : f ∉ q := by
    rw [← Ideal.disjoint_powers_iff_notMem_of_isPrime]
    exact hdisj
  exact IsLocalization.map_units (Localization.AtPrime q)
    (⟨f, hfq⟩ : q.primeCompl)

/-- The purity input at a height-one prime disjoint from the boundary.

The only geometric input is the finite-etale algebra on `D[1/f]`, together
with its generic fraction fields.  From disjointness the proof constructs the
unit in `D_q`, the map `Frac(D[1/f]) -> Frac(D_q)`, and all localization
scalar towers.  It then applies the fixed-component away theorem and
transports the resulting local normalization through the canonical
normalization-localization equivalence.  The maximal ideal `m`, and hence the
selected global tensor component, is preserved literally. -/
theorem localization_integralClosure_genericTensorFieldComponent_etale_of_away
    {D : Type uD} {C : Type uC} {F : Type uF}
    {E : Type uE} {K : Type uK}
    [CommRing D] [IsDomain D] [IsIntegrallyClosed D]
    [CommRing C] [IsDomain C] [Algebra D C] [FaithfulSMul D C]
    (f : D)
    [Algebra (Localization.Away f)
      (Localization.Away (algebraMap D C f))]
    [Module.Finite (Localization.Away f)
      (Localization.Away (algebraMap D C f))]
    [Algebra.Etale (Localization.Away f)
      (Localization.Away (algebraMap D C f))]
    [Field F] [Algebra (Localization.Away f) F]
    [IsFractionRing (Localization.Away f) F]
    [Field E] [Algebra (Localization.Away (algebraMap D C f)) E]
    [IsFractionRing (Localization.Away (algebraMap D C f)) E]
    [Algebra (Localization.Away f) E]
    [IsScalarTower (Localization.Away f)
      (Localization.Away (algebraMap D C f)) E]
    [Algebra F E] [IsScalarTower (Localization.Away f) F E]
    [Field K] [Algebra D K] [IsFractionRing D K]
    (q : Ideal D) [q.IsPrime]
    (hdisj : Disjoint
      ((Submonoid.powers f : Submonoid D) : Set D) (q : Set D)) :
    letI : Algebra D F :=
      ((algebraMap (Localization.Away f) F).comp
        (algebraMap D (Localization.Away f))).toAlgebra
    letI : IsScalarTower D (Localization.Away f) F :=
      IsScalarTower.of_algebraMap_eq' rfl
    letI : Algebra F K :=
      awayFractionFieldToFractionFieldAlgebra f
    letI : IsScalarTower D F K :=
      awayFractionFieldToFractionField_isScalarTower f
    ∀ (m : Ideal (K ⊗[F] E)), [m.IsMaximal] →
      let M := GenericTensorFieldComponent m
      letI : IsScalarTower F K M := genericTensorFieldComponent_isScalarTower m
      letI : IsScalarTower D K M := by
        apply IsScalarTower.of_algebraMap_eq
        intro x
        rw [IsScalarTower.algebraMap_apply D F M,
          IsScalarTower.algebraMap_apply F K M,
          IsScalarTower.algebraMap_apply D F K]
      let canonicalBM : Algebra (Localization.AtPrime q) M :=
        localizationAtPrimeToExtensionAlgebra (K := K) (L := M) q
      letI : Algebra (Localization.AtPrime q) M := canonicalBM
      letI : SMul (Localization.AtPrime q) M := canonicalBM.toSMul
      letI := localizationAtPrimeToExtension_isScalarTower
        (K := K) (L := M) q
      letI := integralClosureLocalizationAlgebra (L := M) q
      Algebra.Etale (Localization.AtPrime q)
        (Localization (Algebra.algebraMapSubmonoid
          (integralClosure D M) q.primeCompl)) := by
  let S := Localization.Away f
  let B := Localization.AtPrime q
  let : Algebra F K := awayFractionFieldToFractionFieldAlgebra f
  intro m _
  let M := GenericTensorFieldComponent m
  let : Algebra D F :=
    ((algebraMap S F).comp (algebraMap D S)).toAlgebra
  let : IsScalarTower D S F := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower D F K :=
    awayFractionFieldToFractionField_isScalarTower f
  let : IsScalarTower F K M := genericTensorFieldComponent_isScalarTower m
  let : IsScalarTower D K M := by
    apply IsScalarTower.of_algebraMap_eq
    intro x
    rw [IsScalarTower.algebraMap_apply D F M,
      IsScalarTower.algebraMap_apply F K M,
      IsScalarTower.algebraMap_apply D F K]
  let : Algebra B K :=
    localizationAtPrimeToFractionFieldAlgebra (K := K) q
  let : IsScalarTower D B K :=
    localizationAtPrimeToFractionField_isScalarTower (K := K) q
  let : IsFractionRing B K :=
    localizationAtPrimeToFractionField_isFractionRing (K := K) q
  let : IsIntegrallyClosed B :=
    isIntegrallyClosed_of_isLocalization B q.primeCompl
      q.primeCompl_le_nonZeroDivisors
  have hf : IsUnit (algebraMap D B f) :=
    isUnit_localizationAtPrime_of_disjoint_powers f q hdisj
  have hlocalOld :=
    integralClosure_genericTensorFieldComponent_etale_of_away_isUnit
      (R := D) (C := C) (B := Localization.AtPrime q)
      (F := F) (E := E) (K := K)
      f hf m
  let quotientPrimeComponentAlgebra : Algebra (Localization.AtPrime q)
      (GenericTensorFieldComponent m) :=
    Ideal.instAlgebraQuotient (Localization.AtPrime q) m
  let canonicalPrimeComponentAlgebra : Algebra (Localization.AtPrime q)
      (GenericTensorFieldComponent m) :=
    localizationAtPrimeToExtensionAlgebra
      (K := K) (L := GenericTensorFieldComponent m) q
  have hAlgebra : quotientPrimeComponentAlgebra =
      canonicalPrimeComponentAlgebra := by
    apply Algebra.algebra_ext
    intro z
    rfl
  have hlocalCanonical :
      @Algebra.Etale (Localization.AtPrime q)
        (@integralClosure (Localization.AtPrime q)
          (GenericTensorFieldComponent m) _ _
          canonicalPrimeComponentAlgebra)
        _ _
        (@integralClosure (Localization.AtPrime q)
          (GenericTensorFieldComponent m) _ _
          canonicalPrimeComponentAlgebra).algebra := by
    exact hAlgebra ▸ hlocalOld
  let : Algebra (Localization.AtPrime q)
      (GenericTensorFieldComponent m) := canonicalPrimeComponentAlgebra
  let : SMul (Localization.AtPrime q) (GenericTensorFieldComponent m) :=
    canonicalPrimeComponentAlgebra.toSMul
  let : IsScalarTower (Localization.AtPrime q) K
      (GenericTensorFieldComponent m) :=
    localizationAtPrimeToFractionFieldToExtension_isScalarTower
      (K := K) (L := GenericTensorFieldComponent m) q
  let : IsScalarTower D (Localization.AtPrime q)
      (GenericTensorFieldComponent m) :=
    localizationAtPrimeToExtension_isScalarTower
      (K := K) (L := GenericTensorFieldComponent m) q
  let := integralClosureLocalizationAlgebra
    (L := GenericTensorFieldComponent m) q
  exact localization_integralClosure_etale_of_local_integralClosure_etale
    (A := D) (K := K) (L := GenericTensorFieldComponent m) q
    hlocalCanonical

end EtaleFundamentalGroups

end
