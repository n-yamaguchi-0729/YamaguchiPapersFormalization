/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.Yamaguchi26AbfaithfulGalois.Kummer.RelativeAbelianModPowerAction
import Nyll.GaloisCohomology.Kummer.Concrete.FixedSubgroupAbsoluteAction
import Nyll.ProCGroups.ProC.MaximalQuotients.ResidualAbelianizationPrimePowers
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.FieldTheory.Perfect
import Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.FiniteExtension.ProlongationDiscrete
import Nyll.Yamaguchi26AbfaithfulGalois.GroupTheory.SigmaPrimeOrderTest
import Nyll.ProCGroups.ProC.MaximalQuotients.ResidualQuotientTransport
import Nyll.ProCGroups.Abelian.TopologicalAbelianization
import Nyll.ProCGroups.FiniteGroups.PrimeOrderHom

/-!
# From prime-degree field detection to Sigma-ab-faithfulness

Fixed-field comparison transports the actual mod-prime action to conjugation
on the residual abelianization. Discrete prolongations supply the hypothesis
on each open layer without completeness or Henselianity assumptions.
-/

namespace Yamaguchi26AbfaithfulGalois

open KummerTheory ProCGroups ProCGroups.ProC ProCGroups.Abelian

universe u

attribute [local instance] KummerTheory.fixingSubgroup_normal

/-- A moved mod-prime class detects nontrivial residual conjugation on the fixing subgroup. -/
theorem fixingSubgroup_residualAbelianization_ne_one_of_moved_mod_prime
    {F Ω : Type u} [Field F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] [CharZero F]
    (S : IntermediateField F Ω) [FiniteDimensional F S] [IsGalois F S]
    (p : ℕ) [Fact p.Prime] (τ : Gal(S/F))
    (z : abelianModPower Gal(AlgebraicClosure S/S) p)
    (hz : relativeGaloisAbelianModPowerTransform F S p τ z ≠ z) :
    residualAbelianizationQuotientConjugation
      (FiniteGroupClass.sigmaGroup_fullFormation {p}) S.fixingSubgroup
        (InfiniteGalois.fixingSubgroup_isClosed S) ≠ 1 := by
  intro htriv
  have hpow := (residualAbelianizationQuotientConjugation_eq_one_iff_primePower
    (sigma := {p}) S.fixingSubgroup (InfiniteGalois.fixingSubgroup_isClosed S)).mp htriv
  obtain ⟨g, hg⟩ := AlgEquiv.restrictNormalHom_surjective Ω τ
  let e := fixingSubgroupAbsoluteAbelianizationEquiv S
  let q : TopologicalAbelianization Gal(AlgebraicClosure S/S) →*
      abelianModPower Gal(AlgebraicClosure S/S) p := QuotientGroup.mk' _
  obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective
    (powMonoidHom (α := TopologicalAbelianization Gal(AlgebraicClosure S/S)) p).range z
  obtain ⟨b, hb⟩ := hpow (QuotientGroup.mk' S.fixingSubgroup g) (e.symm a)
    p rfl (Fact.out : p.Prime) 1 (by decide)
  rw [pow_one] at hb
  have heq := congrArg e hb
  rw [map_mul, map_pow, ContinuousMulEquiv.apply_symm_apply] at heq
  rw [fixingSubgroupAbsoluteAbelianizationEquiv_quotient_conjugation,
    ContinuousMulEquiv.apply_symm_apply] at heq
  change absoluteGaloisAbelianizationAction
    ((AlgEquiv.restrictNormalHom S) g).toRingEquiv a = a * (e b) ^ p at heq
  rw [hg] at heq
  have hqpow : q (e b) ^ p = 1 := by
    rw [← map_pow]
    exact (QuotientGroup.eq_one_iff
      (N := (powMonoidHom (α := TopologicalAbelianization Gal(AlgebraicClosure S/S)) p).range)
      ((e b)^p)).mpr ⟨e b, rfl⟩
  have hq := congrArg q heq
  rw [map_mul, map_pow, hqpow, mul_one] at hq
  apply hz
  calc
    relativeGaloisAbelianModPowerTransform F S p τ (q a) =
        q (absoluteGaloisAbelianizationAction τ.toRingEquiv a) := by
      obtain ⟨σ, rfl⟩ := TopologicalAbelianization.surjective_mk _ a
      rfl
    _ = q a := hq

open ValuationTheory.DiscreteValuationField ProCGroups.FiniteStepSolvableQuotients

private theorem primeDegree_openSubgroup_residualAbelianization_faithful
    {F Ω : Type u} [Field F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] [CharZero F]
    (p : ℕ) [Fact p.Prime] {r : ℕ} [Fact r.Prime]
    (hdetect : ∀ (S : IntermediateField F Ω) [IsGalois F S],
      Module.finrank F S = r →
        ∃ τ : Gal(S/F), ∃ z : abelianModPower Gal(AlgebraicClosure S/S) p,
          relativeGaloisAbelianModPowerTransform F S p τ z ≠ z)
    (N : Subgroup Gal(Ω/F)) [N.Normal]
    (hN : IsOpen (N : Set Gal(Ω/F))) (hindex : N.index = r) :
    Function.Injective (residualAbelianizationQuotientConjugation
      (FiniteGroupClass.sigmaGroup_fullFormation {p}) N (N.isClosed_of_isOpen hN)) := by
  let H : ClosedSubgroup Gal(Ω/F) := ⟨N, N.isClosed_of_isOpen hN⟩
  let S : IntermediateField F Ω := IntermediateField.fixedField N
  have hfix : S.fixingSubgroup = N := InfiniteGalois.fixingSubgroup_fixedField H
  have : FiniteDimensional F S := (InfiniteGalois.isOpen_iff_finite S).mp
    (by rw [hfix]; exact hN)
  have hcard : Nat.card (Gal(Ω/F) ⧸ N) = r := N.index_eq_card.symm.trans hindex
  have hdegree : Module.finrank F S = r :=
    (IsGalois.card_aut_eq_finrank F S).symm.trans
      ((Nat.card_congr (InfiniteGalois.normalAutEquivQuotient H).toEquiv).symm.trans hcard)
  obtain ⟨τ, z, hz⟩ := hdetect S hdegree
  have hfaith := fixingSubgroup_residualAbelianization_ne_one_of_moved_mod_prime S p τ z hz
  let P : Subgroup Gal(Ω/F) → Prop := fun U =>
    ∀ hU : U.Normal, letI : U.Normal := hU
      ∀ hclosed : IsClosed (U : Set Gal(Ω/F)),
        residualAbelianizationQuotientConjugation
          (FiniteGroupClass.sigmaGroup_fullFormation {p}) U hclosed ≠ 1
  have hP : P S.fixingSubgroup := fun _ _ => hfaith
  have hPN : P N := hfix ▸ hP
  apply (injective_iff_ne_one_of_prime_card _ (hcard.symm ▸ (Fact.out : r.Prime))).mpr
  exact hPN inferInstance (N.isClosed_of_isOpen hN)

universe v

private theorem primeDegree_openLayer_residual_faithful
    (p : ℕ) [Fact p.Prime]
    (hdetect : ∀ (F E : Type u) [Field F] [Field E] [Algebra F E]
      [IsGalois F E] [CharZero F]
      (base : DVF.{u, v} F) [CharP base.residueField p]
      (r : ℕ) [Fact r.Prime], Module.finrank F E = r →
        ∃ τ : Gal(E/F), τ ≠ 1 ∧
          ∃ z : abelianModPower Gal(AlgebraicClosure E/E) p,
            relativeGaloisAbelianModPowerTransform F E p τ z ≠ z)
    {K Ω : Type u} [Field K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] [CharZero K]
    (base : DVF.{u, v} K) [CharP base.residueField p]
    (H : OpenSubgroup Gal(Ω/K))
    [CompactSpace (H : Subgroup Gal(Ω/K))]
    (N : OpenNormalSubgroup (H : Subgroup Gal(Ω/K)))
    (hprime : (N : Subgroup (H : Subgroup Gal(Ω/K))).index.Prime) :
    Function.Injective (residualAbelianizationQuotientConjugation
      (FiniteGroupClass.sigmaGroup_fullFormation {p})
      (N : Subgroup (H : Subgroup Gal(Ω/K))) N.isClosed) := by
  let F : IntermediateField K Ω := IntermediateField.fixedField (H : Subgroup Gal(Ω/K))
  let closedH : ClosedSubgroup Gal(Ω/K) := ⟨H.toSubgroup, H.isClosed⟩
  have hfix : F.fixingSubgroup = (H : Subgroup Gal(Ω/K)) :=
    InfiniteGalois.fixingSubgroup_fixedField closedH
  have : FiniteDimensional K F := (InfiniteGalois.isOpen_iff_finite F).mp (by
    rw [hfix]
    exact H.isOpen)
  have : IsAlgClosure F Ω :=
    ⟨IsAlgClosure.isAlgClosed K, Algebra.IsAlgebraic.tower_top (K := K) F⟩
  have : T2Space Gal(Ω/F) := krullTopology_t2 (K := F) (L := Ω)
  obtain ⟨target, _, hres⟩ := base.exists_extension_residueChar (L := F) p
  have : CharP target.residueField p := hres
  let e₀ : (H : Subgroup Gal(Ω/K)) ≃ₜ* F.fixingSubgroup :=
    { toMulEquiv := MulEquiv.subgroupCongr hfix.symm
      continuous_toFun := Continuous.subtype_mk continuous_subtype_val
        (fun x => hfix.symm ▸ x.property)
      continuous_invFun := Continuous.subtype_mk continuous_subtype_val
        (fun x => hfix ▸ x.property) }
  let e : (H : Subgroup Gal(Ω/K)) ≃ₜ* Gal(Ω/F) := e₀.trans (fixingSubgroupContinuousEquiv F)
  let M : Subgroup Gal(Ω/F) := (N : Subgroup (H : Subgroup Gal(Ω/K))).map e.toMulEquiv.toMonoidHom
  have : M.Normal :=
    (inferInstance : (N : Subgroup (H : Subgroup Gal(Ω/K))).Normal).map
      e.toMulEquiv.toMonoidHom e.surjective
  have hM : IsOpen (M : Set Gal(Ω/F)) := e.toHomeomorph.isOpenMap N N.isOpen
  let r : ℕ := (N : Subgroup (H : Subgroup Gal(Ω/K))).index
  have : Fact r.Prime := ⟨hprime⟩
  have hindex : M.index = r := (N : Subgroup (H : Subgroup Gal(Ω/K))).index_map_equiv e.toMulEquiv
  have hfaith := primeDegree_openSubgroup_residualAbelianization_faithful p
    (fun S _ hdeg => by
      obtain ⟨τ, _, z, hz⟩ := hdetect F S target r hdeg
      exact ⟨τ, z, hz⟩) M hM hindex
  have hNfaith := (residualAbelianizationQuotientConjugation_injective_map_iff
    (FiniteGroupClass.sigmaGroup_fullFormation {p}) e
    (N : Subgroup (H : Subgroup Gal(Ω/K))) N.isClosed).mp hfaith
  exact hNfaith

/-- Prime-degree field detection gives Sigma-ab-faithfulness on every open layer. -/
theorem isSigmaAbFaithful_of_primeDegree_detection
    (p : ℕ) [Fact p.Prime]
    (hdetect : ∀ (F E : Type u) [Field F] [Field E] [Algebra F E]
      [IsGalois F E] [CharZero F]
      (base : DVF.{u, v} F) [CharP base.residueField p]
      (r : ℕ) [Fact r.Prime], Module.finrank F E = r →
        ∃ τ : Gal(E/F), τ ≠ 1 ∧
          ∃ z : abelianModPower Gal(AlgebraicClosure E/E) p,
            relativeGaloisAbelianModPowerTransform F E p τ z ≠ z)
    {K : Type u} [Field K] [CharZero K]
    (base : DVF.{u, v} K) [CharP base.residueField p] :
    IsSigmaAbFaithful {p} Gal(AlgebraicClosure K/K) := by
  apply isSigmaAbFaithful_iff_prime_order_test.mpr
  intro H
  have : CompactSpace (H : Subgroup Gal(AlgebraicClosure K/K)) :=
    H.isClosed.isClosedEmbedding_subtypeVal.compactSpace
  intro N hprime
  have hNfaith := primeDegree_openLayer_residual_faithful p hdetect base H N hprime
  exact (injective_iff_ne_one_of_prime_card _ hprime).mp hNfaith

end Yamaguchi26AbfaithfulGalois
