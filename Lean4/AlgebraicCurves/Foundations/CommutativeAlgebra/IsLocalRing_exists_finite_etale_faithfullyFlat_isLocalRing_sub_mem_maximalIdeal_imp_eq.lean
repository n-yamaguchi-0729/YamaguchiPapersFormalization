/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_IsLocalRing_exists_finite_etale_faithfullyFlat_isLocalRing_sub_mem_maximalIdeal_imp_eq.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.RingTheory.Etale.StandardEtale
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.Tactic.Choose
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring.RingNF

/-!
# Is Local Ring exists finite etale faithfully Flat is Local Ring sub mem maximal Ideal imp
eq
-/

section ProofImplementation

namespace AlgebraicCurves.Foundations.CommutativeAlgebra.Proofs
namespace IsLocalRing_exists_finite_etale_faithfullyFlat_isLocalRing_sub_mem_maximalIdeal_imp_eq

universe u

open _root_.Polynomial
open _root_.IsLocalRing

namespace IsLocalRing
open _root_.IsLocalRing
namespace ResidueExtImpl
open _root_.IsLocalRing

section AdjoinRoot

variable {R : Type u} [CommRing R] [IsLocalRing R] (P : R[X])

/-- The extension of the maximal ideal to the algebra obtained by adjoining the polynomial root. -/
noncomputable def m0 : Ideal (AdjoinRoot P) := (maximalIdeal R).map (AdjoinRoot.of P)

/-- The quotient equivalence identifying reduction of the root algebra with the reduced
polynomial root algebra. -/
noncomputable def quotEquiv :
    AdjoinRoot P ⧸ m0 P ≃+* AdjoinRoot (P.map (residue R)) :=
  (AdjoinRoot.quotEquivQuotMap P (maximalIdeal R)).toRingEquiv

theorem quotEquiv_mk (g : R[X]) :
    quotEquiv P (Ideal.Quotient.mk (m0 P) (AdjoinRoot.mk P g)) =
      AdjoinRoot.mk (P.map (residue R)) (g.map (residue R)) :=
  AdjoinRoot.quotEquivQuotMap_apply_mk P g (maximalIdeal R)

variable {P}

theorem m0_isMaximal (hirr : Irreducible (P.map (residue R))) : (m0 P).IsMaximal := by
  have := Fact.mk hirr
  apply Ideal.Quotient.maximal_of_isField
  exact MulEquiv.isField (Field.toIsField (AdjoinRoot (P.map (residue R))))
    (quotEquiv P).toMulEquiv

theorem nontrivial (hirr : Irreducible (P.map (residue R))) :
    Nontrivial (AdjoinRoot P) :=
  nontrivial_of_ne 0 1 fun h => (m0_isMaximal hirr).ne_top
    ((Ideal.eq_top_iff_one _).mpr (h ▸ (m0 P).zero_mem))

theorem isLocalRing (hP : P.Monic) (hirr : Irreducible (P.map (residue R))) :
    IsLocalRing (AdjoinRoot P) := by
  have : Module.Finite R (AdjoinRoot P) := (AdjoinRoot.powerBasis' hP).finite
  have : Algebra.IsIntegral R (AdjoinRoot P) := Algebra.IsIntegral.of_finite R _
  refine IsLocalRing.of_unique_max_ideal ⟨m0 P, m0_isMaximal hirr, fun M hM => ?_⟩
  have := hM
  have hc : (M.comap (algebraMap R (AdjoinRoot P))) = maximalIdeal R :=
    IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := R) M)
  have hle : m0 P ≤ M := by
    rw [m0, ← AdjoinRoot.algebraMap_eq, ← hc]
    exact Ideal.map_comap_le
  exact ((m0_isMaximal hirr).eq_of_le hM.ne_top hle).symm

theorem maximalIdeal_eq (hP : P.Monic) (hirr : Irreducible (P.map (residue R))) :
    letI := isLocalRing hP hirr
    maximalIdeal (AdjoinRoot P) = m0 P :=
  letI := isLocalRing hP hirr
  (IsLocalRing.eq_maximalIdeal (m0_isMaximal hirr)).symm

theorem isLocalHom (hP : P.Monic) (hirr : Irreducible (P.map (residue R))) :
    IsLocalHom (algebraMap R (AdjoinRoot P)) := by
  let := isLocalRing hP hirr
  refine ⟨fun a ha => ?_⟩
  by_contra hna
  have hmem : algebraMap R (AdjoinRoot P) a ∈ maximalIdeal (AdjoinRoot P) := by
    rw [maximalIdeal_eq hP hirr, m0, ← AdjoinRoot.algebraMap_eq]
    exact Ideal.mem_map_of_mem _ ((mem_maximalIdeal _).mpr hna)
  exact (mem_maximalIdeal _).mp hmem ha

theorem etale (hP : P.Monic) (hirr : Irreducible (P.map (residue R)))
    (hsep : (P.map (residue R)).Separable) : Algebra.Etale R (AdjoinRoot P) := by
  let := isLocalRing hP hirr
  have := nontrivial hirr
  obtain ⟨a, b, hab⟩ := hsep
  obtain ⟨b', hb'⟩ := Polynomial.map_surjective (residue R) Ideal.Quotient.mk_surjective b
  have := Fact.mk hirr
  have hg1 : quotEquiv P (Ideal.Quotient.mk (m0 P) (AdjoinRoot.mk P (derivative P * b'))) = 1 := by
    rw [quotEquiv_mk, Polynomial.map_mul, ← Polynomial.derivative_map, hb',
      ← map_one (AdjoinRoot.mk (P.map (residue R))), eq_comm, ← sub_eq_zero,
      ← map_sub, AdjoinRoot.mk_eq_zero]
    exact ⟨a, by linear_combination -hab⟩
  have hgu : IsUnit (AdjoinRoot.mk P (derivative P * b')) := by
    by_contra hnu
    have hmem : AdjoinRoot.mk P (derivative P * b') ∈ maximalIdeal (AdjoinRoot P) :=
      (mem_maximalIdeal _).mpr hnu
    rw [maximalIdeal_eq hP hirr] at hmem
    have h0 : Ideal.Quotient.mk (m0 P) (AdjoinRoot.mk P (derivative P * b')) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr hmem
    rw [h0, map_zero] at hg1
    exact zero_ne_one hg1
  let Q : StandardEtalePair R :=
    { f := P, monic_f := hP, g := derivative P * b', cond := ⟨b', 0, 1, by ring⟩ }
  let e₁ : Q.Ring ≃ₐ[R] Localization.Away (AdjoinRoot.mk P (derivative P * b')) :=
    Q.equivAwayAdjoinRoot
  let e₂ : AdjoinRoot P ≃ₐ[AdjoinRoot P] Localization.Away (AdjoinRoot.mk P (derivative P * b')) :=
    IsLocalization.atUnit (R := AdjoinRoot P) (S := Localization.Away (AdjoinRoot.mk P (derivative
      P * b'))) _ hgu
  exact Algebra.Etale.of_equiv (e₁.trans (e₂.restrictScalars R).symm)

theorem exists_residues {n : ℕ}
    (y : Fin (n + 1) → AdjoinRoot (P.map (residue R))) (hy : Function.Injective y) :
    ∃ x : Fin (n + 1) → AdjoinRoot P, ∀ i j, x i - x j ∈ m0 P → i = j := by
  have hsurj : Function.Surjective (fun z : AdjoinRoot P => quotEquiv P (Ideal.Quotient.mk (m0 P)
    z)) :=
    (quotEquiv P).surjective.comp Ideal.Quotient.mk_surjective
  choose x hx using fun i => hsurj (y i)
  refine ⟨x, fun i j hij => hy ?_⟩
  rw [← Ideal.Quotient.eq] at hij
  rw [← hx i, ← hx j]
  exact congrArg (quotEquiv P) hij

end AdjoinRoot

section Field

variable (k : Type u) [Field k] [Fintype k]

omit [Fintype k] in
theorem exists_irreducible_card_gt [Finite k] (n : ℕ) :
    ∃ Pb : k[X], Pb.Monic ∧ Irreducible Pb ∧ Pb.Separable ∧
      ∃ y : Fin (n + 1) → AdjoinRoot Pb, Function.Injective y := by
  classical
  let : Fintype k := Fintype.ofFinite k
  obtain ⟨p, hchar⟩ := CharP.exists k
  have := hchar
  set q := Fintype.card k with hq
  set N := q ^ (n + 1) with hN
  have hq2 : 2 ≤ q := by rw [hq]; exact Fintype.one_lt_card
  have hnN : n + 1 < N := by
    rw [hN]
    calc n + 1 < 2 ^ (n + 1) := Nat.lt_two_pow_self
      _ ≤ q ^ (n + 1) := Nat.pow_le_pow_left hq2 _
  have hpN : p ∣ N := by
    obtain ⟨m, hprime, hm⟩ := FiniteField.card k p
    rw [hN, hq, hm, ← pow_mul]
    exact dvd_pow_self p (Nat.mul_ne_zero (PNat.ne_zero m) (Nat.succ_ne_zero n))
  let F : k[X] := X ^ N - X
  have hFsep : F.Separable := galois_poly_separable p N hpN
  have hFdeg : F.natDegree = N := FiniteField.X_pow_card_sub_X_natDegree_eq k (by omega)
  let K := F.SplittingField
  have : Finite K := Module.finite_of_finite k
  let : Fintype K := Fintype.ofFinite K
  have hcardK : n + 1 ≤ Fintype.card K := by
    have h1 : Fintype.card (F.rootSet K) = F.natDegree :=
      card_rootSet_eq_natDegree hFsep (SplittingField.splits F)
    have h2 : Fintype.card (F.rootSet K) ≤ Fintype.card K := Fintype.card_subtype_le _
    omega
  obtain ⟨θ, hθ⟩ := Field.exists_primitive_element_of_finite_bot k K
  have hθi : IsIntegral k θ := .of_finite k θ
  refine ⟨minpoly k θ, minpoly.monic hθi, minpoly.irreducible hθi,
    PerfectField.separable_of_irreducible (minpoly.irreducible hθi), ?_⟩
  let e : AdjoinRoot (minpoly k θ) ≃ K :=
    ((IntermediateField.adjoinRootEquivAdjoin k hθi).trans
      ((IntermediateField.equivOfEq hθ).trans IntermediateField.topEquiv)).toEquiv
  let : Fintype (AdjoinRoot (minpoly k θ)) := Fintype.ofEquiv K e.symm
  have hcard : Fintype.card (Fin (n + 1)) ≤ Fintype.card (AdjoinRoot (minpoly k θ)) := by
    rw [Fintype.card_fin, Fintype.card_congr e]; exact hcardK
  obtain ⟨emb⟩ := Function.Embedding.nonempty_of_card_le hcard
  exact ⟨emb, emb.injective⟩

end Field

theorem main (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (n : ℕ) :
    ∃ (R₀ : Type u) (_ : CommRing R₀) (_ : Algebra R R₀) (_ : Module.Finite R R₀)
      (_ : Algebra.Etale R R₀) (_ : Module.FaithfullyFlat R R₀) (_ : IsLocalRing R₀) (_ :
        IsNoetherianRing R₀)
      (_ : IsLocalHom (algebraMap R R₀)) (x : Fin (n + 1) → R₀),
      ∀ i j, x i - x j ∈ IsLocalRing.maximalIdeal R₀ → i = j := by
  classical
  rcases finite_or_infinite (ResidueField R) with hfin | hinf
  · let : Fintype (ResidueField R) := Fintype.ofFinite _
    obtain ⟨Pb, hPbm, hirr, hsep, y, hy⟩ := exists_irreducible_card_gt (ResidueField R) n
    obtain ⟨P, hPmap, -, hP⟩ :=
      Polynomial.lifts_and_natDegree_eq_and_monic
        ((Polynomial.mem_lifts _).mpr (Polynomial.map_surjective _ Ideal.Quotient.mk_surjective
          Pb)) hPbm
    subst hPmap
    let := isLocalRing hP hirr
    have : Module.Finite R (AdjoinRoot P) := (AdjoinRoot.powerBasis' hP).finite
    have : Module.Free R (AdjoinRoot P) := .of_basis (AdjoinRoot.powerBasis' hP).basis
    have := nontrivial hirr
    have : Module.FaithfullyFlat R (AdjoinRoot P) := inferInstance
    have : IsNoetherianRing (AdjoinRoot P) := isNoetherian_of_tower R inferInstance
    obtain ⟨x, hx⟩ := exists_residues y hy
    refine ⟨AdjoinRoot P, inferInstance, inferInstance, inferInstance, etale hP hirr hsep,
      inferInstance,
      inferInstance, inferInstance, isLocalHom hP hirr, x, fun i j hij => hx i j ?_⟩
    rwa [maximalIdeal_eq hP hirr] at hij
  · obtain ⟨x, hx⟩ : ∃ x : Fin (n + 1) → R, ∀ i j, x i - x j ∈ maximalIdeal R → i = j := by
      let y : Fin (n + 1) → ResidueField R := fun i => Infinite.natEmbedding (ResidueField R) i
      have hy : Function.Injective y := fun i j h =>
        Fin.ext ((Infinite.natEmbedding (ResidueField R)).injective h)
      choose x hx using fun i => (Ideal.Quotient.mk_surjective : Function.Surjective (residue R))
        (y i)
      refine ⟨x, fun i j hij => hy ?_⟩
      rw [← hx i, ← hx j]
      exact (Ideal.Quotient.eq).mpr hij
    exact ⟨R, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
      inferInstance,
      inferInstance, ⟨fun a ha => ha⟩, x, hx⟩

end IsLocalRing.ResidueExtImpl

theorem
  _root_.IsLocalRing.exists_finite_etale_faithfullyFlat_isLocalRing_sub_mem_maximalIdeal_imp_eq
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (n : ℕ) :
    ∃ (R₀ : Type u) (_ : CommRing R₀) (_ : Algebra R R₀) (_ : Module.Finite R R₀)
      (_ : Algebra.Etale R R₀) (_ : Module.FaithfullyFlat R R₀) (_ : IsLocalRing R₀) (_ :
        IsNoetherianRing R₀)
      (_ : IsLocalHom (algebraMap R R₀)) (x : Fin (n + 1) → R₀),
      ∀ i j, x i - x j ∈ IsLocalRing.maximalIdeal R₀ → i = j :=
  IsLocalRing.ResidueExtImpl.main R n
end IsLocalRing_exists_finite_etale_faithfullyFlat_isLocalRing_sub_mem_maximalIdeal_imp_eq
end AlgebraicCurves.Foundations.CommutativeAlgebra.Proofs
end ProofImplementation
