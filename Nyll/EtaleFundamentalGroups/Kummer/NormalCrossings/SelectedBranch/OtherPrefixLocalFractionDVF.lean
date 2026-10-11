/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.RingTheory.Localization.Fraction.RingExtension
import Nyll.EtaleFundamentalGroups.LocalGeometry.HeightOne.StandardDVF
import Nyll.EtaleFundamentalGroups.Kummer.NormalCrossings.SelectedBranch.OtherPrefixLocalDVR
import Mathlib.RingTheory.Localization.FractionRing

/-!
# Fraction fields of the selected-prefix local DVRs

The selected other-root prefix supplies a prime `Q` in the tensor product,
its contraction `P` to the prefix, and DVR structures on the two local rings
`E_P` and `T_Q`.  This file fixes the literal fraction fields of those DVRs
and the canonical fraction-field tower.  The local map then gives an
extension of the two standard discrete valuations.

The exact ramification index retained here is deliberately the
ideal-theoretic equality `Q.ramificationIdx E = N` produced before
localization.  We do **not** assert `Module.Finite E_P T_Q`: a localization
at one prime of a finite algebra need not be finite over the corresponding
base localization without an additional chosen-factor argument.  For the
same reason, finite dimensionality of the literal fraction-field extension
and the corresponding `DVF.ramificationIndex` equality belong to the later
generic-component bridge, not to this raw local-DVR leaf.
-/

noncomputable section

open scoped TensorProduct

namespace EtaleFundamentalGroups.Kummer

open ValuationTheory.DiscreteValuationField

universe uV uC uE

/-- Choose the tensor prime above the prescribed normalization prime and
package the literal fraction-field tower of its two local DVRs.

Besides the two DVR instances, the conclusion installs the canonical maps

`E_P → T_Q → Frac(T_Q)` and `E_P → Frac(E_P) → Frac(T_Q)`.

The equality of these two routes is what supplies the standard-valuations
`HasExtension` instance.  No finiteness assertion for `T_Q / E_P` is made.
-/
theorem
    exists_tensorProduct_prime_over_right_with_localFractionDVFs_ramificationIdx_eq_of_etale
    {V : Type uV} {C : Type uC} {E : Type uE}
    [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    [CommRing C] [IsDedekindDomain C]
    [Algebra V C] [FaithfulSMul V C] [Module.Flat V C]
    [CommRing E] [Algebra V E]
    [Algebra.Etale V E] [Module.FaithfullyFlat V E]
    (q : Ideal C) [q.IsPrime] [q.LiesOver (IsLocalRing.maximalIdeal V)]
    (N : ℕ) (hqRam : q.ramificationIdx V = N) :
    let T := E ⊗[V] C
    letI : Algebra E T := Algebra.TensorProduct.leftAlgebra
    ∃ Q : Ideal T, ∃ hQPrime : Q.IsPrime,
      letI : Q.IsPrime := hQPrime
      let P := Q.under E
      letI : P.IsPrime := inferInstance
      letI : Q.LiesOver P := inferInstance
      let EP := Localization.AtPrime P
      let TQ := Localization.AtPrime Q
      Q.comap Algebra.TensorProduct.includeRight.toRingHom = q ∧
        Q.ramificationIdx E = N ∧
          ∃ hPDomain : IsDomain EP,
            letI : IsDomain EP := hPDomain
            ∃ hPDVR : IsDiscreteValuationRing EP,
              letI : IsDiscreteValuationRing EP := hPDVR
              ∃ hQDomain : IsDomain TQ,
                letI : IsDomain TQ := hQDomain
                ∃ hQDVR : IsDiscreteValuationRing TQ,
                  letI : IsDiscreteValuationRing TQ := hQDVR
                  letI : Algebra EP TQ :=
                    Localization.AtPrime.algebraOfLiesOver P Q
                  let KP := FractionRing EP
                  let KQ := FractionRing TQ
                  letI : Algebra TQ KQ := inferInstance
                  letI : SMul TQ KQ :=
                    (inferInstance : Algebra TQ KQ).toSMul
                  letI : FaithfulSMul TQ KQ :=
                    (faithfulSMul_iff_algebraMap_injective TQ KQ).mpr
                      (IsFractionRing.injective TQ KQ)
                  letI : Algebra EP KQ :=
                    ((algebraMap TQ KQ).comp (algebraMap EP TQ)).toAlgebra
                  letI : SMul EP KQ :=
                    (((algebraMap TQ KQ).comp
                      (algebraMap EP TQ)).toAlgebra).toSMul
                  letI : IsScalarTower EP TQ KQ :=
                    IsScalarTower.of_algebraMap_eq' rfl
                  letI : FaithfulSMul EP KQ :=
                    FaithfulSMul.trans EP TQ KQ
                  letI : Algebra KP KQ := FractionRing.liftAlgebra EP KQ
                  letI : IsScalarTower EP KP KQ :=
                    FractionRing.isScalarTower_liftAlgebra EP KQ
                  let base := EtaleFundamentalGroups.standardDVFOfDVR EP KP
                  let target := EtaleFundamentalGroups.standardDVFOfDVR TQ KQ
                  base.valuation.HasExtension target.valuation := by
  let T := E ⊗[V] C
  let : Algebra E T := Algebra.TensorProduct.leftAlgebra
  obtain ⟨Q, hQPrime, hQRight, hQRam,
      hPDomain, hPDVR, hQDomain, hQDVR⟩ :=
    exists_tensorProduct_prime_over_right_with_localDVRs_ramificationIdx_eq_of_etale
      (V := V) (C := C) (E := E) q N hqRam
  refine ⟨Q, hQPrime, ?_⟩
  let : Q.IsPrime := hQPrime
  let P := Q.under E
  let : P.IsPrime := inferInstance
  let : Q.LiesOver P := inferInstance
  let EP := Localization.AtPrime P
  let TQ := Localization.AtPrime Q
  refine ⟨hQRight, hQRam, hPDomain, hPDVR,
    hQDomain, hQDVR, ?_⟩
  let : IsDomain EP := hPDomain
  let : IsDiscreteValuationRing EP := hPDVR
  let : IsDomain TQ := hQDomain
  let : IsDiscreteValuationRing TQ := hQDVR
  let : Algebra EP TQ :=
    Localization.AtPrime.algebraOfLiesOver P Q
  let KP := FractionRing EP
  let KQ := FractionRing TQ
  let : Algebra TQ KQ := inferInstance
  let : SMul TQ KQ := (inferInstance : Algebra TQ KQ).toSMul
  let : FaithfulSMul TQ KQ :=
    (faithfulSMul_iff_algebraMap_injective TQ KQ).mpr
      (IsFractionRing.injective TQ KQ)
  let : Algebra EP KQ :=
    ((algebraMap TQ KQ).comp (algebraMap EP TQ)).toAlgebra
  let : SMul EP KQ :=
    (((algebraMap TQ KQ).comp (algebraMap EP TQ)).toAlgebra).toSMul
  let : IsScalarTower EP TQ KQ :=
    IsScalarTower.of_algebraMap_eq' rfl
  let : FaithfulSMul EP KQ := FaithfulSMul.trans EP TQ KQ
  let : Algebra KP KQ := FractionRing.liftAlgebra EP KQ
  let : IsScalarTower EP KP KQ :=
    FractionRing.isScalarTower_liftAlgebra EP KQ
  let base := EtaleFundamentalGroups.standardDVFOfDVR EP KP
  let target := EtaleFundamentalGroups.standardDVFOfDVR TQ KQ
  have hcomm :
      (algebraMap TQ KQ).comp (algebraMap EP TQ) =
        (algebraMap KP KQ).comp (algebraMap EP KP) := by
    ext z
    change algebraMap TQ KQ (algebraMap EP TQ z) =
      algebraMap KP KQ (algebraMap EP KP z)
    calc
      algebraMap TQ KQ (algebraMap EP TQ z) =
          algebraMap EP KQ z :=
        (IsScalarTower.algebraMap_apply EP TQ KQ z).symm
      _ = algebraMap KP KQ (algebraMap EP KP z) :=
        IsScalarTower.algebraMap_apply EP KP KQ z
  exact EtaleFundamentalGroups.standardDVFOfDVR_hasExtension
    (algebraMap EP TQ) hcomm

end EtaleFundamentalGroups.Kummer

end
