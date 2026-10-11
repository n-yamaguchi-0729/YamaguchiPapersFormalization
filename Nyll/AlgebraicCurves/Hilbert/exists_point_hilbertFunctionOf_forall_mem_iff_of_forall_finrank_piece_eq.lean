/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_HilbertFunctor_exists_point_hilbertFunctionOf_forall_mem_iff_of_forall_finrank_piece_eq.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.Data.Sym.Card
import Nyll.SchemeTheory.ProjectiveSpace.Basic
import Nyll.AlgebraicCurves.Hilbert.Functor.Basic

/-!
# exists point hilbert Function Of forall mem iff of forall finrank piece eq
-/

section ProofImplementation

namespace AlgebraicCurves.Hilbert.Proofs.HilbertFunctionPoint

open MvPolynomial CategoryTheory CategoryTheory.Limits AlgebraicGeometry
  AlgebraicGeometry.HilbertFunctor
attribute [local instance] MvPolynomial.gradedAlgebra

namespace P2mWs30PointPackaging

variable {n : ℕ}

theorem finite_homogeneousSubmodule (A : Type) [CommRing A] (d : ℕ) :
    Module.Finite A ↥(homogeneousSubmodule (Fin (n + 1)) A d) := by
  rw [MvPolynomial.homogeneousSubmodule_eq_finsupp_supported]
  have : Finite {x : Fin (n + 1) →₀ ℕ | x.degree = d} :=
    ((Finsupp.finite_of_degree_le d).subset fun x (hx : x.degree = d) => le_of_eq hx).to_subtype
  exact Module.Finite.of_basis (MvPolynomial.basisRestrictSupport A {x : Fin (n + 1) →₀ ℕ |
    x.degree = d})

theorem natCard_degree_eq (d : ℕ) : Nat.card {s : Fin (n + 1) →₀ ℕ // s.degree = d} = (n +
  d).choose n := by
  classical
  let e : {s : Fin (n + 1) →₀ ℕ // s.degree = d} ≃ Sym (Fin (n + 1)) d :=
    { toFun := fun s => ⟨Finsupp.toMultiset s.1, by
        have h2 := s.2
        rw [Finsupp.degree_apply] at h2
        rw [Finsupp.card_toMultiset]
        simpa [Finsupp.sum] using h2⟩
      invFun := fun t => ⟨Multiset.toFinsupp (t : Multiset (Fin (n + 1))), by
        have h1 := Finsupp.card_toMultiset (Multiset.toFinsupp (t : Multiset (Fin (n + 1))))
        rw [Multiset.toFinsupp_toMultiset] at h1
        rw [Finsupp.degree_apply]
        have h2 : (t : Multiset (Fin (n + 1))).card = d := t.2
        simpa only [Finsupp.sum, id_eq, h2] using h1.symm⟩
      left_inv := fun s => by
        apply Subtype.ext
        simp
      right_inv := fun t => by
        apply Subtype.ext
        simp }
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Sym.card_sym_eq_choose, Fintype.card_fin,
    show n + 1 + d - 1 = n + d by omega, Nat.choose_symm_add]

theorem finrank_homogeneousSubmodule (A : Type) [CommRing A] [Nontrivial A] (d : ℕ) :
    Module.finrank A ↥(homogeneousSubmodule (Fin (n + 1)) A d) = (n + d).choose n := by
  rw [MvPolynomial.homogeneousSubmodule_eq_finsupp_supported]
  exact (Module.finrank_eq_nat_card_basis
    (MvPolynomial.basisRestrictSupport A {x : Fin (n + 1) →₀ ℕ | x.degree = d})).trans
      (natCard_degree_eq d)

theorem decompose_eq {A : Type} [CommRing A] (q : MvPolynomial (Fin (n + 1)) A) (d : ℕ) :
    (DirectSum.decompose (homogeneousSubmodule (Fin (n + 1)) A) q d : MvPolynomial (Fin (n + 1)) A)
      =
      homogeneousComponent d q :=
  MvPolynomial.decomposition.decompose'_apply q d

theorem homogeneousComponent_mul_of_lt {A : Type} [CommRing A] {G : MvPolynomial (Fin (n + 1)) A}
  {m : ℕ}
    (hG : G.IsHomogeneous m) (a : MvPolynomial (Fin (n + 1)) A) {e : ℕ} (he : e < m) :
    homogeneousComponent e (a * G) = 0 := by
  classical
  have := DirectSum.coe_decompose_mul_of_right_mem (𝒜 := homogeneousSubmodule (Fin (n + 1)) A)
    (a := a) e (show G ∈ homogeneousSubmodule (Fin (n + 1)) A m from hG)
  rw [decompose_eq, ite_eq_right (not_le.mpr he)] at this
  exact this

end P2mWs30PointPackaging
end AlgebraicCurves.Hilbert.Proofs.HilbertFunctionPoint

namespace AlgebraicGeometry.HilbertFunctor

open _root_.AlgebraicCurves.Hilbert.Proofs.HilbertFunctionPoint
open _root_.MvPolynomial _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
  _root_.AlgebraicGeometry.HilbertFunctor
attribute [local instance] MvPolynomial.gradedAlgebra


open _root_.AlgebraicCurves.Hilbert.Proofs.HilbertFunctionPoint.P2mWs30PointPackaging in
theorem exists_point_hilbertFunctionOf_forall_mem_iff_of_forall_finrank_piece_eq
    (n : ℕ) (k : Type) [Field k] (P : Polynomial ℚ) (m : ℕ)
    (I : Ideal (MvPolynomial (Fin (n + 1)) k))
    (_ : ∀ p ∈ I, ∀ d : ℕ, homogeneousComponent d p ∈ I)
    (hP : ∀ d : ℕ, m ≤ d → (Module.finrank k (piece I d) : ℚ) = P.eval (d : ℚ)) :
    ∃ q : Point k n (hilbertFunctionOf n P m),
      ∀ (d : ℕ), m ≤ d → ∀ (F : MvPolynomial (Fin (n + 1)) k), F.IsHomogeneous d → (F ∈ q.I ↔ F ∈
        I) := by
  classical
  let S : Set (MvPolynomial (Fin (n + 1)) k) := {p | p ∈ I ∧ ∃ d : ℕ, m ≤ d ∧ p.IsHomogeneous d}
  let J : Ideal (MvPolynomial (Fin (n + 1)) k) := Ideal.span S
  have hJI : J ≤ I := Ideal.span_le.mpr fun p hp => hp.1
  have hJhom : ∀ p ∈ J, ∀ d : ℕ, homogeneousComponent d p ∈ J := by
    intro p hp d
    have H := Ideal.homogeneous_span (homogeneousSubmodule (Fin (n + 1)) k) S
      (fun x hx => by obtain ⟨-, d', -, hd'⟩ := hx; exact ⟨d', hd'⟩)
    have := H d hp
    rwa [decompose_eq] at this
  have hJlt : ∀ p ∈ J, ∀ d : ℕ, d < m → homogeneousComponent d p = 0 := by
    intro p hp d hd
    obtain ⟨N, f, g, rfl⟩ := Submodule.mem_span_set'.mp hp
    rw [map_sum]
    refine Finset.sum_eq_zero fun i _ => ?_
    obtain ⟨-, d', hd', hg⟩ := (g i).2
    exact homogeneousComponent_mul_of_lt hg (f i) (lt_of_lt_of_le hd hd')
  have hmemS : ∀ (d : ℕ), m ≤ d → ∀ F : MvPolynomial (Fin (n + 1)) k, F.IsHomogeneous d → F ∈ I → F
    ∈ J :=
    fun d hd F hF hFI => Ideal.subset_span ⟨hFI, d, hd, hF⟩
  have hcomap_ge : ∀ d : ℕ, m ≤ d →
      Submodule.comap (homogeneousSubmodule (Fin (n + 1)) k d).subtype (J.restrictScalars k) =
        Submodule.comap (homogeneousSubmodule (Fin (n + 1)) k d).subtype (I.restrictScalars k) := by
    intro d hd
    ext ⟨F, hF⟩
    simp only [Submodule.mem_comap, Submodule.subtype_apply, Submodule.restrictScalars_mem]
    exact ⟨fun h => hJI h, fun h => hmemS d hd F ((mem_homogeneousSubmodule d F).mp hF) h⟩
  have hcomap_lt : ∀ d : ℕ, d < m →
      Submodule.comap (homogeneousSubmodule (Fin (n + 1)) k d).subtype (J.restrictScalars k) = ⊥ :=
        by
    intro d hd
    rw [eq_bot_iff]
    rintro ⟨F, hF⟩ hFJ
    simp only [Submodule.mem_comap, Submodule.subtype_apply, Submodule.restrictScalars_mem] at hFJ
    have h1 : homogeneousComponent d F = F := by
      rw [homogeneousComponent_of_mem hF, ite_eq_left rfl]
    have h2 := hJlt F hFJ d hd
    rw [h1] at h2
    simp [h2]
  have hrank_ge : ∀ d : ℕ, m ≤ d → Module.finrank k (piece J d) = Module.finrank k (piece I d) :=
    fun d hd => (Submodule.quotEquivOfEq _ _ (hcomap_ge d hd)).finrank_eq
  have hrank_lt : ∀ d : ℕ, d < m → Module.finrank k (piece J d) = (n + d).choose n := by
    intro d hd
    rw [(Submodule.quotEquivOfEqBot _ (hcomap_lt d hd)).finrank_eq]
    exact finrank_homogeneousSubmodule k d
  refine ⟨{ I := J
            homogeneous := hJhom
            finite_piece := fun d => by
              have := finite_homogeneousSubmodule (n := n) k d
              exact Module.Finite.quotient k _
            projective_piece := fun d => inferInstance
            rankAtStalk_piece := ?_ }, ?_⟩
  · intro d p
    rw [Module.rankAtStalk_eq_finrank_of_free]
    change Module.finrank k (piece J d) = hilbertFunctionOf n P m d
    unfold hilbertFunctionOf
    by_cases hdm : d < m
    · rw [ite_eq_left hdm, hrank_lt d hdm]
    · rw [ite_eq_right hdm, hrank_ge d (not_lt.mp hdm), ← hP d (not_lt.mp hdm), Int.floor_natCast,
        Int.toNat_natCast]
  · intro d hd F hF
    exact ⟨fun h => hJI h, fun h => hmemS d hd F hF h⟩
end AlgebraicGeometry.HilbertFunctor
end ProofImplementation
