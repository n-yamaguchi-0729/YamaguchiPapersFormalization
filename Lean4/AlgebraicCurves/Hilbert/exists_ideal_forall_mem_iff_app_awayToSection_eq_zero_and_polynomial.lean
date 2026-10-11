/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_HilbertFunctor_exists_ideal_forall_mem_iff_app_awayToSection_eq_zero_and_polynomial.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.Algebra.DirectSum.Decomposition
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Field.Rat
import Mathlib.Algebra.GradedMonoid
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.Group.Finsupp
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Algebra.Group.Monoid
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Algebra.Group.Submonoid.Defs
import Mathlib.Algebra.Group.Submonoid.Membership
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Module.Defs
import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Algebra.Module.Submodule.Defs
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.MonoidAlgebra.Defs
import Mathlib.Algebra.MonoidAlgebra.Module
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Ring.Hom.Defs
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Scheme
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Opposite
import Mathlib.Data.Rat.Init
import Mathlib.Geometry.RingedSpace.PresheafedSpace
import Mathlib.GroupTheory.MonoidLocalization.Basic
import Mathlib.GroupTheory.MonoidLocalization.MonoidWithZero
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Quotient.Defs
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Order.Defs.PartialOrder
import Mathlib.RingTheory.GradedAlgebra.Basic
import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization
import Mathlib.RingTheory.Ideal.Defs
import Mathlib.RingTheory.Localization.Defs
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Tactic.SplitIfs
import SchemeTheory.ProjectiveSpace.Basic
import AlgebraicCurves.Hilbert.Functor.Basic
import AlgebraicCurves.Foundations.Algebra.Nat_MacaulayPow
import AlgebraicCurves.Foundations.Polynomial.MvPolynomial_finrank_piece_succ_le_macaulayPow
import AlgebraicCurves.Foundations.Algebra.Nat_exists_forall_eq_macaulayPow_of_forall_le_macaulayPow
import AlgebraicCurves.Foundations.Polynomial.Nat_exists_polynomial_forall_eval_eq_of_forall_eq_macaulayPow

/-!
# exists ideal forall mem iff app away To Section eq zero and polynomial
-/

section ProofImplementation

namespace AlgebraicCurves.Hilbert.Proofs.HilbertIdealPolynomial

open MvPolynomial CategoryTheory CategoryTheory.Limits AlgebraicGeometry
  AlgebraicGeometry.HilbertFunctor
attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable section

namespace E2SOL

section Sat

variable {n : ℕ} {k : Type} [Field k]
    {Zk : Scheme.{0}} (ιk : Zk ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k))

local notation "𝒜" => MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k

/-- The dth power of a variable, regarded as a homogeneous polynomial of degree d. -/
def xpow (i : Fin (n + 1)) (d : ℕ) : ↥(homogeneousSubmodule (Fin (n + 1)) k d) :=
  ⟨MvPolynomial.X i ^ d, (MvPolynomial.mem_homogeneousSubmodule d _).mpr
    (MvPolynomial.isHomogeneous_X_pow i d)⟩

/-- The degree-zero homogeneous fraction with numerator F and denominator the dth variable power. -/
def frac (i : Fin (n + 1)) (d : ℕ) (F : ↥(homogeneousSubmodule (Fin (n + 1)) k d)) :
    HomogeneousLocalization.Away 𝒜 (MvPolynomial.X i) :=
  HomogeneousLocalization.mk
    { deg := d
      num := F
      den := xpow (k := k) i d
      den_mem := ⟨d, rfl⟩ }

theorem frac_zero (i : Fin (n + 1)) (d : ℕ) : frac (k := k) i d 0 = 0 := by
  apply HomogeneousLocalization.val_injective
  simp only [frac, HomogeneousLocalization.val_mk, HomogeneousLocalization.val_zero,
    Submodule.coe_zero]
  exact Localization.mk_zero _

theorem frac_add (i : Fin (n + 1)) (d : ℕ) (F G : ↥(homogeneousSubmodule (Fin (n + 1)) k d)) :
    frac i d (F + G) = frac i d F + frac i d G := by
  apply HomogeneousLocalization.val_injective
  simp only [frac, HomogeneousLocalization.val_mk, HomogeneousLocalization.val_add,
    Submodule.coe_add]
  rw [Localization.add_mk_self]

theorem frac_mul (i : Fin (n + 1)) (e d : ℕ) (G : ↥(homogeneousSubmodule (Fin (n + 1)) k e))
    (F : ↥(homogeneousSubmodule (Fin (n + 1)) k d)) :
    frac i (e + d) ⟨(G : MvPolynomial (Fin (n + 1)) k) * (F : MvPolynomial (Fin (n + 1)) k),
      SetLike.mul_mem_graded G.2 F.2⟩ =
      frac i e G * frac i d F := by
  apply HomogeneousLocalization.val_injective
  simp only [frac, HomogeneousLocalization.val_mk, HomogeneousLocalization.val_mul]
  rw [Localization.mk_mul]
  congr 1
  ext
  simp [xpow, pow_add]

/-- The homomorphism from a projective affine chart to sections on its inverse image. -/
noncomputable def chartHom (i : Fin (n + 1)) :
    HomogeneousLocalization.Away 𝒜 (MvPolynomial.X i) →+*
      ↑(Zk.presheaf.obj (Opposite.op (ιk ⁻¹ᵁ (Proj.basicOpen 𝒜 (MvPolynomial.X i))))) :=
  (Proj.awayToSection 𝒜 (MvPolynomial.X i) ≫ ιk.app (Proj.basicOpen 𝒜 (MvPolynomial.X i))).hom

/-- The condition that a homogeneous polynomial vanishes on every standard projective chart. -/
def Van (d : ℕ) (F : ↥(homogeneousSubmodule (Fin (n + 1)) k d)) : Prop :=
  ∀ i : Fin (n + 1), chartHom ιk i (frac i d F) = 0

theorem Van_zero (d : ℕ) : Van ιk d 0 := by
  intro i; rw [frac_zero, map_zero]

theorem Van_add {d : ℕ} {F G : ↥(homogeneousSubmodule (Fin (n + 1)) k d)}
    (hF : Van ιk d F) (hG : Van ιk d G) : Van ιk d (F + G) := by
  intro i; rw [frac_add, map_add, hF i, hG i, add_zero]

theorem Van_mul_left (e : ℕ) {d : ℕ} (G : ↥(homogeneousSubmodule (Fin (n + 1)) k e))
    {F : ↥(homogeneousSubmodule (Fin (n + 1)) k d)} (hF : Van ιk d F) :
    Van ιk (e + d) ⟨(G : MvPolynomial (Fin (n + 1)) k) * (F : MvPolynomial (Fin (n + 1)) k),
      SetLike.mul_mem_graded G.2 F.2⟩ := by
  intro i; rw [frac_mul, map_mul, hF i, mul_zero]

/-- The homogeneous degree-d component of a polynomial, with its homogeneity proof. -/
def comp (d : ℕ) (p : MvPolynomial (Fin (n + 1)) k) : ↥(homogeneousSubmodule (Fin (n + 1)) k d) :=
  ⟨homogeneousComponent d p, homogeneousComponent_mem d p⟩
omit ιk in
theorem comp_zero (d : ℕ) : comp (k := k) (n := n) d 0 = 0 := Subtype.ext (by simp [comp])
omit ιk in
theorem comp_add (d : ℕ) (p q : MvPolynomial (Fin (n + 1)) k) : comp d (p + q) = comp d p + comp d
  q :=
  Subtype.ext (by simp [comp])
omit ιk in
theorem coe_decompose (φ : MvPolynomial (Fin (n + 1)) k) (i : ℕ) :
    ((DirectSum.decompose 𝒜 φ) i : MvPolynomial (Fin (n + 1)) k) = homogeneousComponent i φ :=
  MvPolynomial.decomposition.decompose'_apply φ i
omit ιk in
theorem homogeneousComponent_mul_of_mem_left {e : ℕ} {c : MvPolynomial (Fin (n + 1)) k}
    (hc : c ∈ homogeneousSubmodule (Fin (n + 1)) k e) (p : MvPolynomial (Fin (n + 1)) k) (d : ℕ) :
    homogeneousComponent d (c * p) = if e ≤ d then c * homogeneousComponent (d - e) p else 0 := by
  have h := DirectSum.coe_decompose_mul_of_left_mem 𝒜 (b := p) d hc
  simpa only [coe_decompose] using h
omit ιk in
theorem comp_of_mem {e : ℕ} {F : MvPolynomial (Fin (n + 1)) k}
    (hF : F ∈ homogeneousSubmodule (Fin (n + 1)) k e) (d : ℕ) :
    comp d F = if h : d = e then ⟨F, h ▸ hF⟩ else 0 := by
  apply Subtype.ext
  simp only [comp, homogeneousComponent_of_mem hF]
  split_ifs <;> rfl

theorem Van_comp_sum {ι : Type} (s : Finset ι) (f : ι → MvPolynomial (Fin (n + 1)) k) (d : ℕ)
    (h : ∀ a ∈ s, Van ιk d (comp d (f a))) : Van ιk d (comp d (∑ a ∈ s, f a)) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, comp_zero]; exact Van_zero ιk d
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, comp_add]
      exact Van_add ιk (h a (Finset.mem_insert_self a s))
        (ih fun b hb => h b (Finset.mem_insert_of_mem hb))

/-- The ideal whose homogeneous components vanish on every standard projective chart. -/
noncomputable def satIdeal : Ideal (MvPolynomial (Fin (n + 1)) k) where
  carrier := {p | ∀ d : ℕ, Van ιk d (comp d p)}
  zero_mem' := by
    intro d; rw [comp_zero]; exact Van_zero ιk d
  add_mem' := by
    intro p q hp hq d
    rw [comp_add]; exact Van_add ιk (hp d) (hq d)
  smul_mem' := by
    intro c p hp d
    rw [smul_eq_mul, ← sum_homogeneousComponent c, Finset.sum_mul]
    apply Van_comp_sum
    intro e _
    rcases Nat.lt_or_ge d e with hde | hed
    · have hc0 : comp d (homogeneousComponent e c * p) = 0 := by
        apply Subtype.ext
        simp only [comp, homogeneousComponent_mul_of_mem_left (homogeneousComponent_mem e c) p d,
          ite_eq_right (not_le.mpr hde), Submodule.coe_zero]
      rw [hc0]; exact Van_zero ιk d
    · obtain ⟨d', rfl⟩ := Nat.exists_eq_add_of_le hed
      have hceq : comp (e + d') (homogeneousComponent e c * p) =
          ⟨(comp e c : MvPolynomial (Fin (n + 1)) k) * (comp d' p : MvPolynomial (Fin (n + 1)) k),
            SetLike.mul_mem_graded (comp e c).2 (comp d' p).2⟩ := by
        apply Subtype.ext
        simp only [comp, homogeneousComponent_mul_of_mem_left (homogeneousComponent_mem e c) p (e +
          d'),
          ite_eq_left (Nat.le_add_right e d'), Nat.add_sub_cancel_left]
      rw [hceq]
      exact Van_mul_left ιk e (comp e c) (hp d')

theorem mem_satIdeal_iff (p : MvPolynomial (Fin (n + 1)) k) :
    p ∈ satIdeal ιk ↔ ∀ d : ℕ, Van ιk d (comp d p) := Iff.rfl

theorem satIdeal_homogeneous (p : MvPolynomial (Fin (n + 1)) k) (hp : p ∈ satIdeal ιk) (d : ℕ) :
    homogeneousComponent d p ∈ satIdeal ιk := by
  rw [mem_satIdeal_iff] at hp ⊢
  intro e
  rw [comp_of_mem (homogeneousComponent_mem d p)]
  split_ifs with h
  · subst h; exact hp _
  · exact Van_zero ιk e

theorem mem_satIdeal_iff_of_isHomogeneous {d : ℕ} {F : MvPolynomial (Fin (n + 1)) k}
    (hF : F.IsHomogeneous d) :
    F ∈ satIdeal ιk ↔ Van ιk d ⟨F, (MvPolynomial.mem_homogeneousSubmodule d F).mpr hF⟩ := by
  rw [mem_satIdeal_iff]
  constructor
  · intro h
    have := h d
    rwa [comp_of_mem ((MvPolynomial.mem_homogeneousSubmodule d F).mpr hF), dite_eq_left rfl] at this
  · intro h e
    rw [comp_of_mem ((MvPolynomial.mem_homogeneousSubmodule d F).mpr hF)]
    split_ifs with hed
    · subst hed; exact h
    · exact Van_zero ιk e

end Sat

end E2SOL
end
end AlgebraicCurves.Hilbert.Proofs.HilbertIdealPolynomial

namespace AlgebraicGeometry.HilbertFunctor
noncomputable section

open _root_.AlgebraicCurves.Hilbert.Proofs.HilbertIdealPolynomial
open _root_.MvPolynomial _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
  _root_.AlgebraicGeometry.HilbertFunctor
attribute [local instance] MvPolynomial.gradedAlgebra


open E2SOL in
theorem exists_ideal_forall_mem_iff_app_awayToSection_eq_zero_and_polynomial
    (n : ℕ) (k : Type) [Field k]
    (Zk : Scheme.{0}) (ιk : Zk ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k))
    (_hιk : IsClosedImmersion ιk) :
    ∃ (I : Ideal (MvPolynomial (Fin (n + 1)) k)),
      (∀ p ∈ I, ∀ d : ℕ, homogeneousComponent d p ∈ I) ∧
      (∀ (d : ℕ) (F : MvPolynomial (Fin (n + 1)) k) (hF : F.IsHomogeneous d),
        (F ∈ I ↔ ∀ i : Fin (n + 1),
                  (ιk.app (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k)
                    (MvPolynomial.X i)))
                    (Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k)
                      (MvPolynomial.X i)
                      (HomogeneousLocalization.mk
                        { deg := d
                          num := ⟨F, (MvPolynomial.mem_homogeneousSubmodule d F).mpr hF⟩
                          den := ⟨MvPolynomial.X i ^ d, (MvPolynomial.mem_homogeneousSubmodule d
                            _).mpr
                            (MvPolynomial.isHomogeneous_X_pow i d)⟩
                          den_mem := ⟨d, rfl⟩ })) = 0)) ∧
      ∃ (P : Polynomial ℚ) (D₀ : ℕ), ∀ d : ℕ, D₀ ≤ d → (Module.finrank k (piece I d) : ℚ) = P.eval
        (d : ℚ) := by
  refine ⟨satIdeal ιk, satIdeal_homogeneous ιk, ?_, ?_⟩
  · intro d F hF
    exact mem_satIdeal_iff_of_isHomogeneous ιk hF
  · have hmac : ∀ d, 1 ≤ d →
        (fun d => Module.finrank k (piece (satIdeal ιk) d)) (d + 1) ≤
          Nat.macaulayPow d ((fun d => Module.finrank k (piece (satIdeal ιk) d)) d) :=
      fun d hd => MvPolynomial.finrank_piece_succ_le_macaulayPow n d hd k (satIdeal ιk)
        (satIdeal_homogeneous ιk)
    obtain ⟨D₀, hD₀⟩ := Nat.exists_forall_eq_macaulayPow_of_forall_le_macaulayPow
      (fun d => Module.finrank k (piece (satIdeal ιk) d)) 1 le_rfl hmac
    obtain ⟨P, hP⟩ := Nat.exists_polynomial_forall_eval_eq_of_forall_eq_macaulayPow
      (fun d => Module.finrank k (piece (satIdeal ιk) d)) (max D₀ 1) (le_max_right _ _)
      (fun e he => hD₀ e (le_trans (le_max_left _ _) he))
    exact ⟨P, max D₀ 1, fun d hd => hP d hd⟩

end
end AlgebraicGeometry.HilbertFunctor
end ProofImplementation
