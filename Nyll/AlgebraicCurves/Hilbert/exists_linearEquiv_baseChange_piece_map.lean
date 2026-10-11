/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_HilbertFunctor_exists_linearEquiv_baseChange_piece_map.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.RingTheory.GradedAlgebra.Basic
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Conv
import Nyll.AlgebraicCurves.Hilbert.Functor.Basic

/-!
# exists linear Equiv base Change piece map
-/

section ProofImplementation

namespace AlgebraicCurves.Hilbert.Proofs
namespace S_AlgebraicGeometry_HilbertFunctor_exists_linearEquiv_baseChange_piece_map

open MvPolynomial AlgebraicGeometry.HilbertFunctor
open scoped TensorProduct

attribute [local instance] MvPolynomial.gradedAlgebra

namespace HilbPieceBC

variable {n : ℕ} {A B : Type} [CommRing A] [CommRing B] [Algebra A B]

omit [Algebra A B] in
theorem homogeneousComponent_map (φ : A →+* B) (d : ℕ) (p : MvPolynomial (Fin (n + 1)) A) :
    homogeneousComponent d (MvPolynomial.map φ p) = MvPolynomial.map φ (homogeneousComponent d p)
      := by
  ext c
  simp only [coeff_homogeneousComponent, coeff_map]
  split_ifs <;> simp

theorem degree_eq_of_mem_support {R : Type} [CommRing R] {p : MvPolynomial (Fin (n + 1)) R} {d : ℕ}
    (hp : p.IsHomogeneous d) {s : Fin (n + 1) →₀ ℕ} (hs : s ∈ p.support) : s.degree = d := by
  have h := hp (mem_support_iff.mp hs)
  have : (Finsupp.degree s : ℕ) = Finsupp.weight (fun _ => 1) s := by
    rw [Finsupp.degree_eq_weight_one]
  rw [this]
  exact h

theorem decompose_eq (q : MvPolynomial (Fin (n + 1)) B) (d : ℕ) :
    (DirectSum.decompose (homogeneousSubmodule (Fin (n + 1)) B) q d : MvPolynomial (Fin (n + 1)) B)
      =
      homogeneousComponent d q :=
  MvPolynomial.decomposition.decompose'_apply q d

variable (n A B) in
/-- The span after base change of homogeneous elements of the ideal in the specified degree. -/
noncomputable def T (I : Ideal (MvPolynomial (Fin (n + 1)) A)) (j : ℕ) :
    Submodule B (MvPolynomial (Fin (n + 1)) B) :=
  Submodule.span B
    (MvPolynomial.map (algebraMap A B) '' {p | p ∈ I ∧ p.IsHomogeneous j})

theorem map_mem_T {I : Ideal (MvPolynomial (Fin (n + 1)) A)} {j : ℕ} {p : MvPolynomial (Fin (n +
  1)) A}
    (hp : p ∈ I) (hpj : p.IsHomogeneous j) : MvPolynomial.map (algebraMap A B) p ∈ T n A B I j :=
  Submodule.subset_span ⟨p, ⟨hp, hpj⟩, rfl⟩

theorem mul_mem_T (I : Ideal (MvPolynomial (Fin (n + 1)) A)) {i j : ℕ}
    {g : MvPolynomial (Fin (n + 1)) B} (hg : g.IsHomogeneous i)
    {x : MvPolynomial (Fin (n + 1)) B} (hx : x ∈ T n A B I j) : g * x ∈ T n A B I (i + j) := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨p, ⟨hpI, hpj⟩, rfl⟩ := hy
    rw [MvPolynomial.as_sum g, Finset.sum_mul]
    refine Submodule.sum_mem _ fun s hs => ?_
    have hsdeg : s.degree = i := degree_eq_of_mem_support hg hs
    have hmono : (monomial s (g.coeff s) : MvPolynomial (Fin (n + 1)) B) =
        g.coeff s • MvPolynomial.map (algebraMap A B) (monomial s (1 : A)) := by
      rw [map_monomial, map_one, smul_monomial, smul_eq_mul, mul_one]
    rw [hmono, smul_mul_assoc, ← map_mul]
    refine Submodule.smul_mem _ _ (map_mem_T (I.mul_mem_left _ hpI) ?_)
    exact (isHomogeneous_monomial (1 : A) hsdeg).mul hpj
  | zero => simp
  | add y z _ _ hy hz => simpa [mul_add] using Submodule.add_mem _ hy hz
  | smul b y _ hy => simpa [mul_smul_comm] using Submodule.smul_mem _ b hy

theorem homogeneousComponent_mem_T (I : Ideal (MvPolynomial (Fin (n + 1)) A))
    (hI : ∀ p ∈ I, ∀ d : ℕ, homogeneousComponent d p ∈ I)
    {q : MvPolynomial (Fin (n + 1)) B} (hq : q ∈ I.map (MvPolynomial.map (algebraMap A B))) (d : ℕ)
      :
    homogeneousComponent d q ∈ T n A B I d := by
  revert d
  refine Submodule.span_induction (p := fun q _ => ∀ d : ℕ, homogeneousComponent d q ∈ T n A B I d)
    ?_ ?_ ?_ ?_ (show q ∈ Ideal.span _ from hq)
  · rintro y ⟨p, hpI, rfl⟩ d
    rw [homogeneousComponent_map]
    exact map_mem_T (hI p hpI d) (homogeneousComponent_isHomogeneous d p)
  · intro d
    simp
  · intro y z _ _ hy hz d
    simpa [map_add] using Submodule.add_mem _ (hy d) (hz d)
  · intro g y _ hy d
    rw [smul_eq_mul, ← sum_homogeneousComponent g, Finset.sum_mul, map_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    have hgi : homogeneousComponent i g ∈ homogeneousSubmodule (Fin (n + 1)) B i :=
      homogeneousComponent_mem i g
    have key := DirectSum.coe_decompose_mul_of_left_mem (𝒜 := homogeneousSubmodule (Fin (n + 1)) B)
      (b := y) d hgi
    rw [decompose_eq, decompose_eq] at key
    rw [key]
    split_ifs with hid
    · have := mul_mem_T I (homogeneousComponent_isHomogeneous i g) (hy (d - i))
      rwa [Nat.add_sub_cancel' hid] at this
    · exact Submodule.zero_mem _

theorem T_le (I : Ideal (MvPolynomial (Fin (n + 1)) A)) (d : ℕ) :
    T n A B I d ≤ (I.map (MvPolynomial.map (algebraMap A B))).restrictScalars B := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨p, ⟨hpI, -⟩, rfl⟩
  exact Ideal.mem_map_of_mem _ hpI

theorem map_homogeneous (I : Ideal (MvPolynomial (Fin (n + 1)) A))
    (hI : ∀ p ∈ I, ∀ d : ℕ, homogeneousComponent d p ∈ I) :
    ∀ q ∈ I.map (MvPolynomial.map (algebraMap A B)), ∀ d : ℕ,
      homogeneousComponent d q ∈ I.map (MvPolynomial.map (algebraMap A B)) :=
  fun _ hq d => T_le I d (homogeneousComponent_mem_T I hI hq d)

section Equiv

variable (I : Ideal (MvPolynomial (Fin (n + 1)) A)) (d : ℕ)

/-- The homogeneous polynomial submodule over the original base ring in the selected degree. -/
abbrev SA : Submodule A (MvPolynomial (Fin (n + 1)) A) := homogeneousSubmodule (Fin (n + 1)) A d

/-- The homogeneous polynomial submodule over the new base ring in the selected degree. -/
abbrev SB : Submodule B (MvPolynomial (Fin (n + 1)) B) := homogeneousSubmodule (Fin (n + 1)) B d

/-- The extension of the polynomial ideal along the change of coefficient ring. -/
noncomputable abbrev I' : Ideal (MvPolynomial (Fin (n + 1)) B) := I.map (MvPolynomial.map
  (algebraMap A B))

/-- The degree part of the ideal as a submodule of homogeneous polynomials over the original
ring. -/
noncomputable abbrev KA : Submodule A (SA (n := n) (A := A) d) :=
  Submodule.comap (SA (n := n) (A := A) d).subtype (I.restrictScalars A)

/-- The degree part of the extended ideal inside the homogeneous polynomials over the new ring. -/
noncomputable abbrev KB : Submodule B (SB (n := n) (B := B) d) :=
  Submodule.comap (SB (n := n) (B := B) d).subtype ((I' (B := B) I).restrictScalars B)

/-- The coefficient-change map between homogeneous polynomial submodules. -/
noncomputable def gd : SA (n := n) (A := A) d →ₗ[A] SB (n := n) (B := B) d where
  toFun p := ⟨MvPolynomial.map (algebraMap A B) (p : MvPolynomial (Fin (n + 1)) A),
    (show (p : MvPolynomial (Fin (n + 1)) A).IsHomogeneous d from p.2).map (algebraMap A B)⟩
  map_add' p q := by
    ext : 1
    simp
  map_smul' a p := by
    ext : 1
    simp only [RingHom.id_apply, Submodule.coe_smul_of_tower, SetLike.val_smul]
    rw [MvPolynomial.smul_eq_C_mul, map_mul, map_C, Algebra.smul_def, MvPolynomial.algebraMap_apply]

@[scoped simp] theorem gd_apply_coe (p : SA (n := n) (A := A) d) :
    ((gd (B := B) d p : SB (n := n) (B := B) d) : MvPolynomial (Fin (n + 1)) B) =
      MvPolynomial.map (algebraMap A B) (p : MvPolynomial (Fin (n + 1)) A) := rfl

/-- The induced map between quotient degree pieces under change of coefficients. -/
noncomputable def gbar : piece I d →ₗ[A] piece (I' (B := B) I) d :=
  (KA I d).liftQ (((KB (B := B) I d).mkQ.restrictScalars A) ∘ₗ gd (B := B) d) (by
    intro p hp
    simp only [LinearMap.mem_ker, LinearMap.coe_comp, Function.comp_apply,
      LinearMap.coe_restrictScalars, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero,
      Submodule.mem_comap, Submodule.coe_subtype, Submodule.restrictScalars_mem]
    exact Ideal.mem_map_of_mem _ hp)

theorem gbar_mk (p : SA (n := n) (A := A) d) :
    gbar (B := B) I d (Submodule.Quotient.mk p) = Submodule.Quotient.mk (gd (B := B) d p) := rfl

/-- The base-changed map from the tensor product of the original degree piece to the new degree
piece. -/
noncomputable def E : B ⊗[A] piece I d →ₗ[B] piece (I' (B := B) I) d :=
  (gbar (B := B) I d).liftBaseChange B

theorem E_tmul (b : B) (p : SA (n := n) (A := A) d) :
    E (B := B) I d (b ⊗ₜ[A] Submodule.Quotient.mk p) = b • Submodule.Quotient.mk (gd (B := B) d p)
      := by
  simp [E, LinearMap.liftBaseChange_tmul, gbar_mk]

/-- The tensor representing a monomial of the selected degree, and zero for other degrees. -/
noncomputable def v : (Fin (n + 1) →₀ ℕ) → B ⊗[A] piece I d := fun s =>
  if hs : s.degree = d then
    (1 : B) ⊗ₜ[A] Submodule.Quotient.mk (⟨monomial s (1 : A), isHomogeneous_monomial (1 : A) hs⟩ :
      SA (n := n) (A := A) d)
  else 0

/-- The linear map from polynomials to the tensor-product degree piece defined on monomials. -/
noncomputable def Psi' : MvPolynomial (Fin (n + 1)) B →ₗ[B] B ⊗[A] piece I d :=
  (MvPolynomial.basisMonomials (Fin (n + 1)) B).constr B (v (B := B) I d)

theorem Psi'_monomial (s : Fin (n + 1) →₀ ℕ) (b : B) :
    Psi' (B := B) I d (monomial s b) = b • v (B := B) I d s := by
  have h1 : (monomial s b : MvPolynomial (Fin (n + 1)) B) =
      b • (MvPolynomial.basisMonomials (Fin (n + 1)) B) s := by
    rw [MvPolynomial.coe_basisMonomials, smul_monomial, smul_eq_mul, mul_one]
  rw [h1, map_smul, Psi', Module.Basis.constr_basis]

theorem Psi'_map (p : MvPolynomial (Fin (n + 1)) A) (hp : p.IsHomogeneous d) :
    Psi' (B := B) I d (MvPolynomial.map (algebraMap A B) p) =
      (1 : B) ⊗ₜ[A] Submodule.Quotient.mk (⟨p, hp⟩ : SA (n := n) (A := A) d) := by
  classical
  have hw : ∀ s : Fin (n + 1) →₀ ℕ, (monomial s (p.coeff s) : MvPolynomial (Fin (n + 1))
    A).IsHomogeneous d := by
    intro s
    by_cases hs : p.coeff s = 0
    · rw [hs, monomial_zero]
      exact isHomogeneous_zero _ _ _
    · exact isHomogeneous_monomial _ (degree_eq_of_mem_support hp (mem_support_iff.mpr hs))
  let w : (Fin (n + 1) →₀ ℕ) → SA (n := n) (A := A) d := fun s => ⟨monomial s (p.coeff s), hw s⟩
  have hp_sum : (⟨p, hp⟩ : SA (n := n) (A := A) d) = ∑ s ∈ p.support, w s := by
    apply Subtype.ext
    simp only [w, AddSubmonoidClass.coe_finsetSum]
    exact p.as_sum
  have hmap : MvPolynomial.map (algebraMap A B) p =
      ∑ s ∈ p.support, monomial s (algebraMap A B (p.coeff s)) := by
    conv_lhs => rw [p.as_sum]
    simp only [map_sum, map_monomial]
  have hterm : ∀ s ∈ p.support, Psi' (B := B) I d (monomial s (algebraMap A B (p.coeff s))) =
      (1 : B) ⊗ₜ[A] Submodule.Quotient.mk (w s) := by
    intro s hs
    have hsd : s.degree = d := degree_eq_of_mem_support hp hs
    rw [Psi'_monomial]
    simp only [v, dite_eq_left hsd]
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one,
      show algebraMap A B (p.coeff s) = p.coeff s • (1 : B) by rw [Algebra.smul_def, mul_one],
      TensorProduct.smul_tmul, ← Submodule.Quotient.mk_smul]
    congr 2
    apply Subtype.ext
    simp [w, smul_monomial]
  rw [hmap, map_sum, Finset.sum_congr rfl hterm, ← TensorProduct.tmul_sum, hp_sum]
  congr 1
  simp only [← Submodule.mkQ_apply, map_sum]

theorem Psi'_map_eq_zero (p : MvPolynomial (Fin (n + 1)) A) (hpI : p ∈ I) (hp : p.IsHomogeneous d) :
    Psi' (B := B) I d (MvPolynomial.map (algebraMap A B) p) = 0 := by
  rw [Psi'_map I d p hp]
  have : (Submodule.Quotient.mk (⟨p, hp⟩ : SA (n := n) (A := A) d) : piece I d) = 0 := by
    rw [Submodule.Quotient.mk_eq_zero]
    simpa using hpI
  rw [this, TensorProduct.tmul_zero]

theorem T_le_ker : T n A B I d ≤ LinearMap.ker (Psi' (B := B) I d) := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨p, ⟨hpI, hpd⟩, rfl⟩
  exact Psi'_map_eq_zero I d p hpI hpd

/-- The map from the new quotient degree piece back to the tensor-product degree piece. -/
noncomputable def Psi (hI : ∀ p ∈ I, ∀ d : ℕ, homogeneousComponent d p ∈ I) :
    piece (I' (B := B) I) d →ₗ[B] B ⊗[A] piece I d :=
  (KB (B := B) I d).liftQ (Psi' (B := B) I d ∘ₗ (SB (n := n) (B := B) d).subtype) (by
    intro q hq
    have hqI : (q : MvPolynomial (Fin (n + 1)) B) ∈ I' (B := B) I := by simpa using hq
    have hqd : (q : MvPolynomial (Fin (n + 1)) B).IsHomogeneous d := q.2
    have hcomp : homogeneousComponent d (q : MvPolynomial (Fin (n + 1)) B) = q :=
      homogeneousComponent_of_mem (m := d) q.2 |>.trans (ite_eq_left rfl)
    rw [LinearMap.mem_ker, LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype, ← hcomp]
    exact T_le_ker I d (homogeneousComponent_mem_T I hI hqI d))

theorem Psi_mk (hI : ∀ p ∈ I, ∀ d : ℕ, homogeneousComponent d p ∈ I) (q : SB (n := n) (B := B) d) :
    Psi (B := B) I d hI (Submodule.Quotient.mk q) = Psi' (B := B) I d (q : MvPolynomial (Fin (n +
      1)) B) :=
  rfl

theorem Psi_E (hI : ∀ p ∈ I, ∀ d : ℕ, homogeneousComponent d p ∈ I) (x : B ⊗[A] piece I d) :
    Psi (B := B) I d hI (E (B := B) I d x) = x := by
  induction x using TensorProduct.inductionOn with
  | tmul b y =>
    obtain ⟨p, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    rw [E_tmul, map_smul, Psi_mk, gd_apply_coe, Psi'_map I d _ p.2, TensorProduct.smul_tmul',
      smul_eq_mul, mul_one]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

theorem E_Psi (hI : ∀ p ∈ I, ∀ d : ℕ, homogeneousComponent d p ∈ I) (z : piece (I' (B := B) I) d) :
    E (B := B) I d (Psi (B := B) I d hI z) = z := by
  classical
  obtain ⟨q, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  rw [Psi_mk]
  have hq : (q : MvPolynomial (Fin (n + 1)) B).IsHomogeneous d := q.2
  have hw : ∀ s : Fin (n + 1) →₀ ℕ,
      (monomial s ((q : MvPolynomial (Fin (n + 1)) B).coeff s) : MvPolynomial (Fin (n + 1))
        B).IsHomogeneous d := by
    intro s
    by_cases hs : (q : MvPolynomial (Fin (n + 1)) B).coeff s = 0
    · rw [hs, monomial_zero]
      exact isHomogeneous_zero _ _ _
    · exact isHomogeneous_monomial _ (degree_eq_of_mem_support hq (mem_support_iff.mpr hs))
  let w : (Fin (n + 1) →₀ ℕ) → SB (n := n) (B := B) d :=
    fun s => ⟨monomial s ((q : MvPolynomial (Fin (n + 1)) B).coeff s), hw s⟩
  have hq_sum : q = ∑ s ∈ (q : MvPolynomial (Fin (n + 1)) B).support, w s := by
    apply Subtype.ext
    simp only [w, AddSubmonoidClass.coe_finsetSum]
    exact (q : MvPolynomial (Fin (n + 1)) B).as_sum
  have hterm : ∀ s ∈ (q : MvPolynomial (Fin (n + 1)) B).support,
      E (B := B) I d (Psi' (B := B) I d (monomial s ((q : MvPolynomial (Fin (n + 1)) B).coeff s))) =
        Submodule.Quotient.mk (w s) := by
    intro s hs
    have hsd : s.degree = d := degree_eq_of_mem_support hq hs
    rw [Psi'_monomial]
    simp only [v, dite_eq_left hsd]
    rw [map_smul, E_tmul, one_smul, ← Submodule.Quotient.mk_smul]
    congr 1
    apply Subtype.ext
    simp [w, smul_monomial, map_monomial]
  conv_lhs => rw [(q : MvPolynomial (Fin (n + 1)) B).as_sum, map_sum, map_sum]
  rw [Finset.sum_congr rfl hterm, hq_sum]
  simp only [← Submodule.mkQ_apply, map_sum]
  rw [← hq_sum]

/-- The base-change equivalence for the degree pieces of the homogeneous quotient. -/
noncomputable def equiv (hI : ∀ p ∈ I, ∀ d : ℕ, homogeneousComponent d p ∈ I) :
    B ⊗[A] piece I d ≃ₗ[B] piece (I' (B := B) I) d :=
  LinearEquiv.ofLinearMap (E (B := B) I d) (Psi (B := B) I d hI)
    (LinearMap.ext fun z => E_Psi I d hI z) (LinearMap.ext fun x => Psi_E I d hI x)

theorem equiv_tmul_mk (hI : ∀ p ∈ I, ∀ d : ℕ, homogeneousComponent d p ∈ I)
    (p : MvPolynomial (Fin (n + 1)) A) (hp : p.IsHomogeneous d) :
    equiv (B := B) I d hI ((1 : B) ⊗ₜ[A] Submodule.Quotient.mk ⟨p, hp⟩) =
      Submodule.Quotient.mk ⟨MvPolynomial.map (algebraMap A B) p, hp.map (algebraMap A B)⟩ := by
  change E (B := B) I d _ = _
  rw [E_tmul, one_smul]
  rfl

end Equiv

end HilbPieceBC

attribute [local simp] HilbPieceBC.gd_apply_coe


theorem _root_.AlgebraicGeometry.HilbertFunctor.exists_linearEquiv_baseChange_piece_map
    (n : ℕ) (A B : Type) [CommRing A] [CommRing B] [Algebra A B]
    (I : Ideal (MvPolynomial (Fin (n + 1)) A))
    (hI : ∀ p ∈ I, ∀ d : ℕ, homogeneousComponent d p ∈ I) :
    (∀ q ∈ I.map (MvPolynomial.map (algebraMap A B)), ∀ d : ℕ,
        homogeneousComponent d q ∈ I.map (MvPolynomial.map (algebraMap A B))) ∧
    ∀ d : ℕ, ∃ e : B ⊗[A] piece I d ≃ₗ[B] piece (I.map (MvPolynomial.map (algebraMap A B))) d,
      ∀ (p : MvPolynomial (Fin (n + 1)) A) (hp : p.IsHomogeneous d),
        e (1 ⊗ₜ[A] Submodule.Quotient.mk ⟨p, hp⟩) =
          Submodule.Quotient.mk ⟨MvPolynomial.map (algebraMap A B) p, hp.map (algebraMap A B)⟩ :=
  ⟨HilbPieceBC.map_homogeneous I hI, fun d =>
    ⟨HilbPieceBC.equiv I d hI, fun p hp => HilbPieceBC.equiv_tmul_mk I d hI p hp⟩⟩
end S_AlgebraicGeometry_HilbertFunctor_exists_linearEquiv_baseChange_piece_map
end AlgebraicCurves.Hilbert.Proofs
end ProofImplementation
