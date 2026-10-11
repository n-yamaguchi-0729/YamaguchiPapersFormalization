/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_Algebra_FormallySmooth_exists_linearMap_eq_of_symmetric_hochschild_two_cocycle.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.RingTheory.Smooth.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Module

/-!
# Algebra Formally Smooth exists linear Map eq of symmetric hochschild two cocycle
-/

section ProofImplementation

namespace AlgebraicCurves.Foundations.Algebra.Proofs
namespace Algebra_FormallySmooth_exists_linearMap_eq_of_symmetric_hochschild_two_cocycle

universe u v w

noncomputable section

namespace HochschildSplitSol

variable {R : Type u} [CommRing R] {S : Type v} [CommRing S] [Algebra R S]
  {M : Type w} [AddCommGroup M] [Module R M] [Module S M]

/-- A symmetric normalized Hochschild two-cocycle with values in the module. -/
structure Cocycle (R : Type u) [CommRing R] (S : Type v) [CommRing S] [Algebra R S]
    (M : Type w) [AddCommGroup M] [Module R M] [Module S M] where
  /-- The bilinear two-cocycle. -/
  ψ : S →ₗ[R] S →ₗ[R] M
  /-- The cocycle is symmetric. -/
  symm : ∀ x y, ψ x y = ψ y x
  /-- The cocycle vanishes when the first argument is one. -/
  one : ∀ y, ψ 1 y = 0
  /-- The Hochschild cocycle identity. -/
  coc : ∀ x y z, x • ψ y z - ψ (x * y) z + ψ x (y * z) - z • ψ x y = 0

/-- The underlying pair of a scalar and a module element in the extension defined by the
cocycle. -/
structure Ext (c : Cocycle R S M) where
  /-- The scalar component. -/
  fst : S
  /-- The module component. -/
  snd : M

namespace Ext

variable (c : Cocycle R S M)

@[scoped ext] theorem ext {a b : Ext c} (h1 : a.fst = b.fst) (h2 : a.snd = b.snd) : a = b := by
  cases a; cases b; congr

/-- The identification of the underlying extension with the Cartesian product. -/
def equiv : Ext c ≃ S × M where
  toFun a := (a.fst, a.snd)
  invFun q := ⟨q.1, q.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

scoped instance : AddCommGroup (Ext c) := (equiv c).addCommGroup

/-- The additive identification of the extension with the product of the two additive groups. -/
def addEquiv : Ext c ≃+ S × M where
  toEquiv := equiv c
  map_add' _ _ := rfl

scoped instance instModule : Module R (Ext c) := (addEquiv c).module R

@[scoped simp] theorem fst_add (a b : Ext c) : (a + b).fst = a.fst + b.fst := rfl
@[scoped simp] theorem snd_add (a b : Ext c) : (a + b).snd = a.snd + b.snd := rfl
@[scoped simp] theorem fst_zero : (0 : Ext c).fst = 0 := rfl
@[scoped simp] theorem snd_zero : (0 : Ext c).snd = 0 := rfl
@[scoped simp] theorem fst_neg (a : Ext c) : (-a).fst = -a.fst := rfl
@[scoped simp] theorem snd_neg (a : Ext c) : (-a).snd = -a.snd := rfl
@[scoped simp] theorem fst_smul (r : R) (a : Ext c) : (r • a).fst = r • a.fst := rfl
@[scoped simp] theorem snd_smul (r : R) (a : Ext c) : (r • a).snd = r • a.snd := rfl
@[scoped simp] theorem fst_mk (x : S) (u : M) : (Ext.mk x u : Ext c).fst = x := rfl
@[scoped simp] theorem snd_mk (x : S) (u : M) : (Ext.mk x u : Ext c).snd = u := rfl

scoped instance : Mul (Ext c) :=
  ⟨fun a b => ⟨a.fst * b.fst, a.fst • b.snd + b.fst • a.snd + c.ψ a.fst b.fst⟩⟩

scoped instance : One (Ext c) := ⟨⟨1, 0⟩⟩

@[scoped simp] theorem fst_mul (a b : Ext c) : (a * b).fst = a.fst * b.fst := rfl
@[scoped simp] theorem snd_mul (a b : Ext c) :
    (a * b).snd = a.fst • b.snd + b.fst • a.snd + c.ψ a.fst b.fst := rfl
@[scoped simp] theorem fst_one : (1 : Ext c).fst = 1 := rfl
@[scoped simp] theorem snd_one : (1 : Ext c).snd = 0 := rfl

theorem mul_comm' (a b : Ext c) : a * b = b * a := by
  ext
  · simp only [fst_mul, mul_comm]
  · simp only [snd_mul, c.symm a.fst b.fst]
    abel

theorem mul_assoc' (a b d : Ext c) : a * b * d = a * (b * d) := by
  ext
  · simp only [fst_mul, mul_assoc]
  · simp only [snd_mul, fst_mul, smul_add]
    rw [← sub_eq_zero]
    have h := c.coc a.fst b.fst d.fst
    calc _ = -(a.fst • c.ψ b.fst d.fst - c.ψ (a.fst * b.fst) d.fst +
          c.ψ a.fst (b.fst * d.fst) - d.fst • c.ψ a.fst b.fst) := by
          simp only [smul_smul]
          module
      _ = 0 := by rw [h, neg_zero]

theorem one_mul' (a : Ext c) : 1 * a = a := by
  ext
  · simp only [fst_mul, fst_one, one_mul]
  · simp only [snd_mul, fst_one, snd_one, one_smul, smul_zero, add_zero, c.one]

scoped instance instCommRing : CommRing (Ext c) where
  __ := (inferInstance : AddCommGroup (Ext c))
  mul := (· * ·)
  one := 1
  mul_assoc := mul_assoc' c
  one_mul := one_mul' c
  mul_one a := by rw [mul_comm']; exact one_mul' c a
  zero_mul a := by
    ext
    · simp only [fst_mul, fst_zero, zero_mul]
    · simp only [snd_mul, fst_zero, snd_zero, zero_smul, smul_zero, map_zero,
        LinearMap.zero_apply, add_zero]
  mul_zero a := by
    ext
    · simp only [fst_mul, fst_zero, mul_zero]
    · simp only [snd_mul, fst_zero, snd_zero, zero_smul, smul_zero, map_zero, add_zero]
  left_distrib a b d := by
    ext
    · simp only [fst_mul, fst_add, mul_add]
    · simp only [snd_mul, fst_add, snd_add, smul_add, add_smul, map_add]
      abel
  right_distrib a b d := by
    ext
    · simp only [fst_mul, fst_add, add_mul]
    · simp only [snd_mul, fst_add, snd_add, smul_add, add_smul, map_add, LinearMap.add_apply]
      abel
  mul_comm := mul_comm' c

variable [IsScalarTower R S M]

theorem smul_mul_assoc' (r : R) (a b : Ext c) : (r • a) * b = r • (a * b) := by
  ext
  · simp only [fst_mul, fst_smul, smul_mul_assoc]
  · simp only [snd_mul, fst_smul, snd_smul, smul_add, LinearMap.map_smul₂, smul_assoc]
    rw [smul_comm b.fst r a.snd]

scoped instance instAlgebra : Algebra R (Ext c) :=
  Algebra.ofModule (smul_mul_assoc' c) fun r a b => by
    rw [mul_comm', smul_mul_assoc', mul_comm']

/-- The algebra homomorphism projecting the extension to its scalar component. -/
def fstHom : Ext c →ₐ[R] S where
  toFun := Ext.fst
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' r := by
    rw [Algebra.algebraMap_eq_smul_one, fst_smul, fst_one, Algebra.algebraMap_eq_smul_one]

theorem fstHom_apply (a : Ext c) : fstHom c a = a.fst := rfl

theorem fstHom_surjective : Function.Surjective (fstHom c) := fun x => ⟨⟨x, 0⟩, rfl⟩

theorem fst_eq_zero_of_mem_ker {a : Ext c} (ha : a ∈ RingHom.ker (fstHom c : Ext c →+* S)) :
    a.fst = 0 := ha

theorem ker_sq_eq_bot : RingHom.ker (fstHom c : Ext c →+* S) ^ 2 = ⊥ := by
  rw [pow_two, eq_bot_iff, Ideal.mul_le]
  intro a ha b hb
  rw [Ideal.mem_bot]
  have ha' := fst_eq_zero_of_mem_ker c ha
  have hb' := fst_eq_zero_of_mem_ker c hb
  ext
  · simp only [fst_mul, ha', zero_mul, fst_zero]
  · simp only [snd_mul, ha', hb', zero_smul, map_zero, add_zero, snd_zero]

theorem isNilpotent_ker : IsNilpotent (RingHom.ker (fstHom c : Ext c →+* S)) :=
  ⟨2, ker_sq_eq_bot c⟩

variable [Algebra.FormallySmooth R S]

/-- A section of the extension projection supplied by formal smoothness. -/
def sect : S →ₐ[R] Ext c :=
  Algebra.FormallySmooth.liftOfSurjective (AlgHom.id R S) (fstHom c) (fstHom_surjective c)
    (isNilpotent_ker c)

theorem fst_sect (x : S) : (sect c x).fst = x := by
  have h := Algebra.FormallySmooth.liftOfSurjective_apply (AlgHom.id R S) (fstHom c)
    (fstHom_surjective c) (isNilpotent_ker c) x
  exact h

/-- The linear map given by the module component of the chosen section. -/
def ell : S →ₗ[R] M where
  toFun x := (sect c x).snd
  map_add' x y := by rw [map_add, snd_add]
  map_smul' r x := by rw [map_smul, snd_smul, RingHom.id_apply]

theorem ell_apply (x : S) : ell c x = (sect c x).snd := rfl

theorem ell_one : ell c 1 = 0 := by rw [ell_apply, map_one, snd_one]

theorem ψ_eq (x y : S) : c.ψ x y = ell c (x * y) - x • ell c y - y • ell c x := by
  have h := congrArg Ext.snd (map_mul (sect c) x y)
  rw [snd_mul, fst_sect, fst_sect] at h
  rw [ell_apply, ell_apply, ell_apply, h]
  abel

end Ext

end HochschildSplitSol

end

open HochschildSplitSol in
theorem _root_.Algebra.FormallySmooth.exists_linearMap_eq_of_symmetric_hochschild_two_cocycle
    (R : Type u) [CommRing R] (S : Type v) [CommRing S] [Algebra R S] [Algebra.FormallySmooth R S]
    (M : Type w) [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
    (ψ : S →ₗ[R] S →ₗ[R] M)
    (hsymm : ∀ x y, ψ x y = ψ y x)
    (hone : ∀ y, ψ 1 y = 0)
    (hcoc : ∀ x y z, x • ψ y z - ψ (x * y) z + ψ x (y * z) - z • ψ x y = 0) :
    ∃ l : S →ₗ[R] M, l 1 = 0 ∧ ∀ x y, ψ x y = l (x * y) - x • l y - y • l x :=
  let c : Cocycle R S M := ⟨ψ, hsymm, hone, hcoc⟩
  ⟨Ext.ell c, Ext.ell_one c, Ext.ψ_eq c⟩
end Algebra_FormallySmooth_exists_linearMap_eq_of_symmetric_hochschild_two_cocycle
end AlgebraicCurves.Foundations.Algebra.Proofs
end ProofImplementation
