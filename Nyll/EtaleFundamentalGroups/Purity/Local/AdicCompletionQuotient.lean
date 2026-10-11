/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.RingTheory.AdicCompletion.LocalRing

/-!
# The first quotient of an adic completion

For a finitely generated ideal `I`, reduction of the `I`-adic completion
modulo the extended ideal is canonically the original quotient `R ⧸ I`.
This is the closed-fibre comparison used by formal gluing along completion.
-/

noncomputable section

namespace EtaleFundamentalGroups

universe u

open IsLocalRing

/-- Reduction modulo the extended ideal identifies the first quotient of an
adic completion with the original quotient. -/
noncomputable def adicCompletionQuotientEquiv
    {R : Type u} [CommRing R] (I : Ideal R) (hI : I.FG) :
    AdicCompletion I R ⧸ I.map (algebraMap R (AdicCompletion I R)) ≃+*
      R ⧸ I :=
  (Ideal.quotEquivOfEq (AdicCompletion.ker_evalOneₐ_eq_map I hI).symm).trans
    (RingHom.quotientKerEquivOfSurjective
      (AdicCompletion.evalOneₐ_surjective I))

@[simp]
theorem adicCompletionQuotientEquiv_mk
    {R : Type u} [CommRing R] (I : Ideal R) (hI : I.FG)
    (x : AdicCompletion I R) :
    adicCompletionQuotientEquiv I hI
        (Ideal.Quotient.mk (I.map (algebraMap R (AdicCompletion I R))) x) =
      AdicCompletion.evalOneₐ I x := by
  rw [adicCompletionQuotientEquiv, RingEquiv.trans_apply,
    Ideal.quotEquivOfEq_mk,
    RingHom.quotientKerEquivOfSurjective_apply_mk]
  rfl

@[simp]
theorem adicCompletionQuotientEquiv_algebraMap_mk
    {R : Type u} [CommRing R] (I : Ideal R) (hI : I.FG) (x : R) :
    adicCompletionQuotientEquiv I hI
        (Ideal.Quotient.mk (I.map (algebraMap R (AdicCompletion I R)))
          (algebraMap R (AdicCompletion I R) x)) =
      Ideal.Quotient.mk I x := by
  rw [adicCompletionQuotientEquiv_mk]
  change AdicCompletion.evalOneₐ I (AdicCompletion.of I R x) =
    Ideal.Quotient.mk I x
  exact AdicCompletion.evalOneₐ_of I x

/-- The closed-fibre comparison, regarded as an `R`-algebra map from the
adic completion to `R ⧸ I`. -/
noncomputable def adicCompletionClosedFiberAlgHom
    {R : Type u} [CommRing R] (I : Ideal R) (hI : I.FG) :
    AdicCompletion I R →ₐ[R] R ⧸ I where
  toRingHom := (adicCompletionQuotientEquiv I hI).toRingHom.comp
    (Ideal.Quotient.mk (I.map (algebraMap R (AdicCompletion I R))))
  commutes' x := adicCompletionQuotientEquiv_algebraMap_mk I hI x

@[simp]
theorem adicCompletionClosedFiberAlgHom_apply
    {R : Type u} [CommRing R] (I : Ideal R) (hI : I.FG)
    (x : AdicCompletion I R) :
    adicCompletionClosedFiberAlgHom I hI x =
      adicCompletionQuotientEquiv I hI
        (Ideal.Quotient.mk
          (I.map (algebraMap R (AdicCompletion I R))) x) :=
  rfl

@[simp]
theorem adicCompletionClosedFiberAlgHom_algebraMap
    {R : Type u} [CommRing R] (I : Ideal R) (hI : I.FG) (x : R) :
    adicCompletionClosedFiberAlgHom I hI
        (algebraMap R (AdicCompletion I R) x) =
      Ideal.Quotient.mk I x :=
  adicCompletionQuotientEquiv_algebraMap_mk I hI x

/-- Every element of an adic completion is congruent modulo the extended
ideal to an element of the original ring. -/
theorem adicCompletion_exists_sub_mem_map
    {R : Type u} [CommRing R] (I : Ideal R) (hI : I.FG)
    (x : AdicCompletion I R) :
    ∃ r : R,
      x - algebraMap R (AdicCompletion I R) r ∈
        I.map (algebraMap R (AdicCompletion I R)) := by
  obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective
    (adicCompletionQuotientEquiv I hI
      (Ideal.Quotient.mk
        (I.map (algebraMap R (AdicCompletion I R))) x))
  refine ⟨r, (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp ?_⟩
  apply (adicCompletionQuotientEquiv I hI).injective
  change adicCompletionQuotientEquiv I hI
      (Ideal.Quotient.mk
        (I.map (algebraMap R (AdicCompletion I R))) x) =
    adicCompletionQuotientEquiv I hI
      (Ideal.Quotient.mk
        (I.map (algebraMap R (AdicCompletion I R)))
        (algebraMap R (AdicCompletion I R) r))
  rw [adicCompletionQuotientEquiv_algebraMap_mk]
  exact hr.symm

/-- The kernel of reduction of an `I`-adic completion modulo `I ^ n` is
the extension of `I ^ n` to the completion. -/
theorem adicCompletion_ker_evalₐ_eq_map_pow
    {R : Type u} [CommRing R] (I : Ideal R) (hI : I.FG) (n : ℕ) :
    RingHom.ker (AdicCompletion.evalₐ I n).toRingHom =
      (I ^ n).map (algebraMap R (AdicCompletion I R)) := by
  ext x
  change AdicCompletion.evalₐ I n x = 0 ↔ _
  rw [← Submodule.restrictScalars_mem R, ← Ideal.smul_top_eq_map,
    AdicCompletion.pow_smul_top_eq_ker_eval hI]
  change AdicCompletion.evalₐ I n x = 0 ↔
    AdicCompletion.eval I R n x = 0
  constructor
  · intro hx
    let hle : I ^ n ≤ I ^ n • (⊤ : Ideal R) := by simp
    calc
      AdicCompletion.eval I R n x =
          Ideal.Quotient.factor hle (AdicCompletion.evalₐ I n x) :=
        (AdicCompletion.factor_evalₐ_eq_eval I x hle).symm
      _ = Ideal.Quotient.factor hle 0 := congrArg _ hx
      _ = 0 := map_zero _
  · intro hx
    let hle : I ^ n • (⊤ : Ideal R) ≤ I ^ n := by simp
    calc
      AdicCompletion.evalₐ I n x =
          Ideal.Quotient.factor hle (AdicCompletion.eval I R n x) :=
        (AdicCompletion.factor_eval_eq_evalₐ I x hle).symm
      _ = Ideal.Quotient.factor hle 0 := congrArg _ hx
      _ = 0 := map_zero _

/-- Reduction modulo any power of a finitely generated adic ideal commutes
with completion. -/
noncomputable def adicCompletionPowQuotientEquiv
    {R : Type u} [CommRing R] (I : Ideal R) (hI : I.FG) (n : ℕ) :
    AdicCompletion I R ⧸
        (I ^ n).map (algebraMap R (AdicCompletion I R)) ≃+*
      R ⧸ I ^ n :=
  (Ideal.quotEquivOfEq
      (adicCompletion_ker_evalₐ_eq_map_pow I hI n).symm).trans
    (RingHom.quotientKerEquivOfSurjective
      (AdicCompletion.surjective_evalₐ I n))

@[simp]
theorem adicCompletionPowQuotientEquiv_mk
    {R : Type u} [CommRing R] (I : Ideal R) (hI : I.FG) (n : ℕ)
    (x : AdicCompletion I R) :
    adicCompletionPowQuotientEquiv I hI n
        (Ideal.Quotient.mk
          ((I ^ n).map (algebraMap R (AdicCompletion I R))) x) =
      AdicCompletion.evalₐ I n x := by
  rw [adicCompletionPowQuotientEquiv, RingEquiv.trans_apply,
    Ideal.quotEquivOfEq_mk,
    RingHom.quotientKerEquivOfSurjective_apply_mk]
  rfl

@[simp]
theorem adicCompletionPowQuotientEquiv_algebraMap_mk
    {R : Type u} [CommRing R] (I : Ideal R) (hI : I.FG) (n : ℕ)
    (x : R) :
    adicCompletionPowQuotientEquiv I hI n
        (Ideal.Quotient.mk
          ((I ^ n).map (algebraMap R (AdicCompletion I R)))
          (algebraMap R (AdicCompletion I R) x)) =
      Ideal.Quotient.mk (I ^ n) x := by
  rw [adicCompletionPowQuotientEquiv_mk]
  exact AdicCompletion.evalₐ_of I n x

/-- Every element of an `I`-adic completion is congruent modulo the
extension of `I ^ n` to an element of the original ring. -/
theorem adicCompletion_exists_sub_mem_map_pow
    {R : Type u} [CommRing R] (I : Ideal R) (hI : I.FG) (n : ℕ)
    (x : AdicCompletion I R) :
    ∃ r : R,
      x - algebraMap R (AdicCompletion I R) r ∈
        (I ^ n).map (algebraMap R (AdicCompletion I R)) := by
  obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective
    (AdicCompletion.evalₐ I n x)
  refine ⟨r, ?_⟩
  rw [← adicCompletion_ker_evalₐ_eq_map_pow I hI n,
    RingHom.mem_ker]
  change AdicCompletion.evalₐ I n
      (x - algebraMap R (AdicCompletion I R) r) = 0
  rw [map_sub, AdicCompletion.algebraMap_apply,
    AdicCompletion.evalₐ_of, ← hr]
  simp

/-- The residue ring of a Noetherian local ring is unchanged by maximal-adic
completion.  The source ideal is stated as the actual maximal ideal of the
completed local ring. -/
noncomputable def maximalAdicCompletionResidueEquiv
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] :
    AdicCompletion (maximalIdeal R) R ⧸
        maximalIdeal (AdicCompletion (maximalIdeal R) R) ≃+*
      R ⧸ maximalIdeal R :=
  (Ideal.quotEquivOfEq AdicCompletion.maximalIdeal_eq_map).trans
    (adicCompletionQuotientEquiv (maximalIdeal R)
      (maximalIdeal R).fg_of_isNoetherianRing)

@[simp]
theorem maximalAdicCompletionResidueEquiv_mk
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (x : AdicCompletion (maximalIdeal R) R) :
    maximalAdicCompletionResidueEquiv R
        (Ideal.Quotient.mk
          (maximalIdeal (AdicCompletion (maximalIdeal R) R)) x) =
      AdicCompletion.evalOneₐ (maximalIdeal R) x := by
  rw [maximalAdicCompletionResidueEquiv, RingEquiv.trans_apply,
    Ideal.quotEquivOfEq_mk, adicCompletionQuotientEquiv_mk]

@[simp]
theorem maximalAdicCompletionResidueEquiv_algebraMap_mk
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (x : R) :
    maximalAdicCompletionResidueEquiv R
        (Ideal.Quotient.mk
          (maximalIdeal (AdicCompletion (maximalIdeal R) R))
          (algebraMap R (AdicCompletion (maximalIdeal R) R) x)) =
      Ideal.Quotient.mk (maximalIdeal R) x := by
  rw [maximalAdicCompletionResidueEquiv_mk]
  change AdicCompletion.evalOneₐ (maximalIdeal R)
      (AdicCompletion.of (maximalIdeal R) R x) =
    Ideal.Quotient.mk (maximalIdeal R) x
  exact AdicCompletion.evalOneₐ_of (maximalIdeal R) x

end EtaleFundamentalGroups

end
