/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.RingTheory.Etale.Locus
import Nyll.EtaleFundamentalGroups.FiniteEtale.Local.OverDiscreteValuationRing
import Nyll.EtaleFundamentalGroups.Kummer.NormalCrossings.SelectedBranch.OtherPrefixEtale

/-!
# Local DVRs after adjoining the selected normalization branch

The other-root prefix is etale over the selected branch DVR.  After tensoring
it with a normalization factor, a prime chosen over the right tensor factor
has two useful contractions.  Its contraction to the etale prefix lies over
the closed point, while localization at the tensor prime is a DVR over the
localized normalization branch.  The ramification-index equality from the
etale tensor base change is retained verbatim.

No module-finiteness of either chosen prime localization is used.
-/

noncomputable section

open scoped TensorProduct

namespace EtaleFundamentalGroups.Kummer

open IsLocalRing

universe uV uC uE

/-- Choose a tensor-product prime above a normalization branch and construct
the two local DVRs attached to its left contraction and to the tensor prime.
The chosen prime retains both its explicit right contraction and the exact
ramification index supplied by the normalization branch.

The flatness of `C / V` is only used to keep the later left-local map flat;
no finiteness of either localization is asserted. -/
theorem
    exists_tensorProduct_prime_over_right_with_localDVRs_ramificationIdx_eq_of_etale
    {V : Type uV} {C : Type uC} {E : Type uE}
    [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    [CommRing C] [IsDedekindDomain C]
    [Algebra V C] [FaithfulSMul V C] [Module.Flat V C]
    [CommRing E] [Algebra V E]
    [Algebra.Etale V E] [Module.FaithfullyFlat V E]
    (q : Ideal C) [q.IsPrime] [q.LiesOver (maximalIdeal V)]
    (N : ℕ) (hqRam : q.ramificationIdx V = N) :
    ∃ Q : Ideal (E ⊗[V] C), ∃ hQPrime : Q.IsPrime,
      letI : Q.IsPrime := hQPrime
      let P := Q.under E
      Q.comap Algebra.TensorProduct.includeRight.toRingHom = q ∧
        Q.ramificationIdx E = N ∧
          ∃ hPDomain : IsDomain (Localization.AtPrime P),
            letI : IsDomain (Localization.AtPrime P) := hPDomain
            IsDiscreteValuationRing (Localization.AtPrime P) ∧
              ∃ hQDomain : IsDomain (Localization.AtPrime Q),
                letI : IsDomain (Localization.AtPrime Q) := hQDomain
                IsDiscreteValuationRing (Localization.AtPrime Q) := by
  let T := E ⊗[V] C
  obtain ⟨Q, hQPrime, hQRight, hQRam⟩ :=
    exists_tensorProduct_prime_over_right_ramificationIdx_eq_of_etale
      (R := V) (B := C) (E := E) q
  refine ⟨Q, hQPrime, ?_⟩
  let : Q.IsPrime := hQPrime
  let : Algebra E T := Algebra.TensorProduct.leftAlgebra
  let : IsScalarTower V E T :=
    inferInstance
  let : Algebra C T := Algebra.TensorProduct.rightAlgebra
  let : IsScalarTower V C T :=
    Algebra.TensorProduct.right_isScalarTower
  let : Q.LiesOver q :=
    ⟨by
        simpa [Ideal.under_def,
          Algebra.TensorProduct.algebraMap_eq_includeRight] using
          hQRight.symm⟩
  let P := Q.under E
  let : P.IsPrime := inferInstance
  let : Q.LiesOver P := inferInstance
  have hQOverMaximal : Q.LiesOver (maximalIdeal V) :=
    Ideal.LiesOver.trans Q q (maximalIdeal V)
  let : Q.LiesOver (maximalIdeal V) := hQOverMaximal
  have hPOverMaximal : P.LiesOver (maximalIdeal V) :=
    Ideal.LiesOver.tower_bot Q P (maximalIdeal V)
  let : P.LiesOver (maximalIdeal V) := hPOverMaximal
  obtain ⟨hPDomain, hPDVR⟩ :=
    (open _root_.EtaleFundamentalGroups in
      exists_isDiscreteValuationRing_localizationAtPrime_of_etale_liesOver_maximalIdeal
        (V := V) (E := E) P)
  have hqNe : q ≠ ⊥ := by
    intro hqBot
    have hmaxBot : maximalIdeal V = ⊥ := by
      calc
        maximalIdeal V = q.under V := q.over_def (maximalIdeal V)
        _ = ⊥ := by
          rw [hqBot, Ideal.under_def]
          exact Ideal.comap_bot_of_injective
            (algebraMap V C)
            (FaithfulSMul.algebraMap_injective V C)
    exact IsDiscreteValuationRing.not_a_field V hmaxBot
  let Cq := Localization.AtPrime q
  let TQ := Localization.AtPrime Q
  let : IsDiscreteValuationRing Cq :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain
      C hqNe Cq
  let commC : (C ⊗[V] E) ≃ₐ[C] T :=
    { toRingEquiv :=
        (Algebra.TensorProduct.comm V C E).toRingEquiv
      commutes' := by
        intro c
        exact
          (Algebra.TensorProduct.right_algebraMap_apply c).symm }
  let : Algebra.Etale C T := Algebra.Etale.of_equiv commC
  let : IsNoetherianRing T :=
    Algebra.FiniteType.isNoetherianRing C T
  let : Algebra.IsUnramifiedAt C Q := by
    exact
      (Algebra.formallyUnramified_iff_forall.mp
        (inferInstance : Algebra.FormallyUnramified C T))
          (PrimeSpectrum.mk Q inferInstance)
  let : Algebra Cq TQ :=
    Localization.AtPrime.algebraOfLiesOver q Q
  let : IsScalarTower C Cq TQ := inferInstance
  let : Algebra.EssFiniteType C TQ := inferInstance
  let : Algebra.EssFiniteType Cq TQ :=
    Algebra.EssFiniteType.of_comp C Cq TQ
  obtain ⟨hQDomain, hQDVR⟩ :=
    EtaleFundamentalGroups.isDiscreteValuationRing_of_flat_of_formallyUnramified_of_isLocalHom
      (V := Cq) (C := TQ)
  refine ⟨hQRight, hQRam.trans hqRam, hPDomain, hPDVR,
    hQDomain, hQDVR⟩

end EtaleFundamentalGroups.Kummer

end
