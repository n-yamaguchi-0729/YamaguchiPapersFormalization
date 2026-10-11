/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_ProjSpace_isQuasicoherent_twist.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.Tactic.Ring.RingNF
import Mathlib.Tactic.Choose
import AlgebraicCurves.Geometry.Projective.ProjTwistDatum
import SchemeTheory.Cohomology.Sheaves.OModulePresheafHom

/-!
# Proj Space is Quasicoherent twist
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Projective.Proofs.ProjSpace_isQuasicoherent_twist

open CategoryTheory AlgebraicGeometry

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable section

namespace P2mTwistQC

open AlgebraicGeometry.ProjSpace

variable {A : Type u} [CommRing A] {N : ℕ} {X : Scheme.{u}}
  (π : X ⟶ Spec (.of A)) (φ : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) A)) (m : ℕ)

theorem restrictFun_injective_of_ge {W W' : X.Opens} (h : W ≤ W') (h' : W' ≤ W) :
    Function.Injective (restrictFun h) := by
  intro a b hab
  have := congrArg (restrictFun h') hab
  rwa [restrictFun_restrictFun, restrictFun_restrictFun, restrictFun_refl, restrictFun_refl] at this

theorem basicOpen_restrictFun {V W : X.Opens} (h : V ≤ W) (f : Γ(X, W)) :
    X.basicOpen (restrictFun h f) = V ⊓ X.basicOpen f :=
  X.basicOpen_res f (homOfLE h).op

theorem exists_pow_mul_eq_zero {V : X.Opens} (hV : IsAffineOpen V) (s x : Γ(X, V))
    (hx : restrictFun (X.basicOpen_le s) x = 0) : ∃ n : ℕ, s ^ n * x = 0 := by
  have := hV.isLocalization_basicOpen s
  have h0 : algebraMap Γ(X, V) Γ(X, X.basicOpen s) x = 0 := hx
  obtain ⟨⟨_, n, rfl⟩, h⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers s) _ _).mp h0
  exact ⟨n, h⟩

theorem exists_restrictFun_eq_mul_pow {V : X.Opens} (hV : IsAffineOpen V) (s : Γ(X, V)) (z : Γ(X,
  X.basicOpen s)) :
    ∃ (n : ℕ) (a : Γ(X, V)),
      restrictFun (X.basicOpen_le s) a = z * restrictFun (X.basicOpen_le s) (s ^ n) := by
  have := hV.isLocalization_basicOpen s
  obtain ⟨⟨a, ⟨_, n, rfl⟩⟩, h⟩ := IsLocalization.surj (Submonoid.powers s) z
  exact ⟨n, a, h.symm⟩

theorem restrictFun_mul_pow_eq {V : X.Opens} (s : Γ(X, V)) (z : Γ(X, X.basicOpen s)) {n : ℕ} {a :
  Γ(X, V)}
    (h : restrictFun (X.basicOpen_le s) a = z * restrictFun (X.basicOpen_le s) (s ^ n)) {n' : ℕ}
      (hn : n ≤ n') :
    restrictFun (X.basicOpen_le s) (s ^ (n' - n) * a) = z * restrictFun (X.basicOpen_le s) (s ^ n')
      := by
  rw [map_mul, h, show n' = n + (n' - n) by omega, Nat.add_sub_cancel_left]
  simp only [map_pow, map_mul, pow_add]
  ring

section Pieces

variable (U : X.affineOpens) (f : Γ(X, U.1))

/-- The intersection of the affine open with the chosen pullback chart. -/
abbrev V (j : Fin (N + 1)) : X.Opens := U.1 ⊓ pullbackChart φ j

/-- The intersection of the affine open with two pullback charts. -/
abbrev V₂ (j l : Fin (N + 1)) : X.Opens := (U.1 ⊓ pullbackChart φ j) ⊓ pullbackChart φ l

theorem isAffineOpen_V [IsSeparated π] [IsAffineHom φ] (j : Fin (N + 1)) : IsAffineOpen (V φ U j) :=
  Scheme.OrderedAffineCover.isAffineOpen_inf_of_isSeparated π U.2 (isAffineOpen_pullbackChart φ j)

theorem isAffineOpen_V₂ [IsSeparated π] [IsAffineHom φ] (j l : Fin (N + 1)) : IsAffineOpen (V₂ φ U
  j l) :=
  Scheme.OrderedAffineCover.isAffineOpen_inf_of_isSeparated π (isAffineOpen_V π φ U j)
    (isAffineOpen_pullbackChart φ l)

/-- The restriction of the function to the intersection with one pullback chart. -/
abbrev fV (j : Fin (N + 1)) : Γ(X, V φ U j) := restrictFun inf_le_left f

/-- The restriction of the function to the intersection with two pullback charts. -/
abbrev fV₂ (j l : Fin (N + 1)) : Γ(X, V₂ φ U j l) := restrictFun (inf_le_left.trans inf_le_left) f

theorem basicOpen_fV (j : Fin (N + 1)) : X.basicOpen (fV φ U f j) = V φ U j ⊓ X.basicOpen f :=
  basicOpen_restrictFun _ f

theorem basicOpen_fV₂ (j l : Fin (N + 1)) : X.basicOpen (fV₂ φ U f j l) = V₂ φ U j l ⊓ X.basicOpen
  f :=
  basicOpen_restrictFun _ f

theorem inf_le_basicOpen_fV (j : Fin (N + 1)) : X.basicOpen f ⊓ pullbackChart φ j ≤ X.basicOpen (fV
  φ U f j) :=
  (le_inf (le_inf (inf_le_left.trans (X.basicOpen_le f)) inf_le_right) inf_le_left).trans
    (basicOpen_fV φ U f j).ge

theorem basicOpen_fV_le_inf (j : Fin (N + 1)) : X.basicOpen (fV φ U f j) ≤ X.basicOpen f ⊓
  pullbackChart φ j :=
  (basicOpen_fV φ U f j).le.trans (le_inf inf_le_right (inf_le_left.trans inf_le_right))

theorem basicOpen_fV₂_le_left (j l : Fin (N + 1)) : X.basicOpen (fV₂ φ U f j l) ≤ X.basicOpen (fV φ
  U f j) :=
  (basicOpen_fV₂ φ U f j l).le.trans ((inf_le_inf_right _ inf_le_left).trans (basicOpen_fV φ U f
    j).ge)

theorem basicOpen_fV₂_le_right (j l : Fin (N + 1)) : X.basicOpen (fV₂ φ U f j l) ≤ X.basicOpen (fV
  φ U f l) :=
  (basicOpen_fV₂ φ U f j l).le.trans
    ((inf_le_inf_right _ (le_inf (inf_le_left.trans inf_le_left) inf_le_right)).trans (basicOpen_fV
      φ U f l).ge)

theorem basicOpen_fV₂_le_inf (j l : Fin (N + 1)) :
    X.basicOpen (fV₂ φ U f j l) ≤ (X.basicOpen f ⊓ pullbackChart φ j) ⊓ pullbackChart φ l :=
  le_inf ((basicOpen_fV₂_le_left φ U f j l).trans (basicOpen_fV_le_inf φ U f j))
    ((X.basicOpen_le _).trans inf_le_right)

end Pieces

section Torsion

variable (U : X.affineOpens) (f : Γ(X, U.1))

theorem torsion [IsSeparated π] [IsAffineHom φ] (y : (twist π φ m).obj U.1) (hy : (twist π φ m).res
  (X.basicOpen_le f) y = 0) :
    ∃ n : ℕ, (f ^ n : Γ(X, U.1)) • y = 0 := by
  classical
  change twistObj π φ m U.1 at y
  have hyj : ∀ j, restrictFun (X.basicOpen_le (fV φ U f j)) ((y : twistObj π φ m U.1).val j) = 0 :=
    by
    intro j
    have h1 : restrictFun (inf_le_inf_right (pullbackChart φ j) (X.basicOpen_le f)) ((y : twistObj
      π φ m U.1).val j) = 0 := by
      have := congrArg (fun g : twistObj π φ m (X.basicOpen f) => g.val j) hy
      simp only [twist_res_val] at this
      exact this
    have h2 := congrArg (restrictFun (basicOpen_fV_le_inf φ U f j)) h1
    rw [restrictFun_restrictFun, map_zero] at h2
    exact h2
  choose n hn using fun j => exists_pow_mul_eq_zero (isAffineOpen_V π φ U j) (fV φ U f j) _ (hyj j)
  refine ⟨Finset.univ.sup n, twistObj.ext (funext fun j => ?_)⟩
  change restrictFun _ (f ^ _) * (y : twistObj π φ m U.1).val j = 0
  rw [map_pow]
  have hle : n j ≤ Finset.univ.sup n := Finset.le_sup (Finset.mem_univ j)
  rw [show Finset.univ.sup n = (Finset.univ.sup n - n j) + n j
    by omega, pow_add, mul_assoc, hn j, mul_zero]

end Torsion

section Extension

variable (U : X.affineOpens) (f : Γ(X, U.1)) (x : (twist π φ m).obj (X.basicOpen f))

/-- The chosen chart component of a twisted section, restricted to the corresponding basic open. -/
def z (j : Fin (N + 1)) : Γ(X, X.basicOpen (fV φ U f j)) :=
  restrictFun (basicOpen_fV_le_inf φ U f j) ((x : twistObj π φ m (X.basicOpen f)).val j)

theorem exists_numerators [IsSeparated π] [IsAffineHom φ] :
    ∃ (n : ℕ) (a : ∀ j : Fin (N + 1), Γ(X, V φ U j)),
      ∀ j, restrictFun (X.basicOpen_le (fV φ U f j)) (a j)
        = z π φ m U f x j * restrictFun (X.basicOpen_le (fV φ U f j)) (fV φ U f j ^ n) := by
  classical
  choose n a h using fun j => exists_restrictFun_eq_mul_pow (isAffineOpen_V π φ U j) (fV φ U f j)
    (z π φ m U f x j)
  refine ⟨Finset.univ.sup n, fun j => fV φ U f j ^ (Finset.univ.sup n - n j) * a j, fun j => ?_⟩
  exact restrictFun_mul_pow_eq (fV φ U f j) (z π φ m U f x j) (h j) (Finset.le_sup (Finset.mem_univ
    j))

/-- The difference between two candidate sections after applying the twist transition function. -/
def defect (a : ∀ j : Fin (N + 1), Γ(X, V φ U j)) (j l : Fin (N + 1)) : Γ(X, V₂ φ U j l) :=
  restrictFun (inf_le_left : V₂ φ U j l ≤ V φ U j) (a j)
    - restrictFun (inf_le_left.trans inf_le_right : V₂ φ U j l ≤ pullbackChart φ j) (frameUnit φ j
      l) ^ m
      * restrictFun (le_inf (inf_le_left.trans inf_le_left) inf_le_right : V₂ φ U j l ≤ V φ U l) (a
        l)

theorem restrictFun_defect_eq_zero {n : ℕ} {a : ∀ j : Fin (N + 1), Γ(X, V φ U j)}
    (ha : ∀ j, restrictFun (X.basicOpen_le (fV φ U f j)) (a j)
      = z π φ m U f x j * restrictFun (X.basicOpen_le (fV φ U f j)) (fV φ U f j ^ n)) (j l : Fin (N
        + 1)) :
    restrictFun (X.basicOpen_le (fV₂ φ U f j l)) (defect φ m U a j l) = 0 := by
  have haj := congrArg (restrictFun (basicOpen_fV₂_le_left φ U f j l)) (ha j)
  have hal := congrArg (restrictFun (basicOpen_fV₂_le_right φ U f j l)) (ha l)
  rw [restrictFun_restrictFun, map_mul, restrictFun_restrictFun] at haj hal
  have hx := congrArg (restrictFun (basicOpen_fV₂_le_inf φ U f j l)) ((x : twistObj π φ m
    (X.basicOpen f)).compat j l)
  rw [map_mul, map_pow, restrictFun_restrictFun, restrictFun_restrictFun, restrictFun_restrictFun]
    at hx
  simp only [defect, map_sub, map_mul, map_pow, restrictFun_restrictFun]
  rw [haj, hal]
  simp only [z, restrictFun_restrictFun, map_pow] at hx ⊢
  rw [hx]
  ring

theorem extension [IsSeparated π] [IsAffineHom φ] :
    ∃ (k : ℕ) (y : (twist π φ m).obj U.1),
      (twist π φ m).res (X.basicOpen_le f) y = restrictFun (X.basicOpen_le f) (f ^ k) • x := by
  classical
  obtain ⟨n, a, ha⟩ := exists_numerators π φ m U f x
  choose k hk using fun jl : Fin (N + 1) × Fin (N + 1) =>
    exists_pow_mul_eq_zero (isAffineOpen_V₂ π φ U jl.1 jl.2) (fV₂ φ U f jl.1 jl.2) _
      (restrictFun_defect_eq_zero π φ m U f x ha jl.1 jl.2)
  set K : ℕ := Finset.univ.sup k with hK
  have hkill : ∀ j l, fV₂ φ U f j l ^ K * defect φ m U a j l = 0 := by
    intro j l
    have hle : k (j, l) ≤ K := Finset.le_sup (Finset.mem_univ (j, l))
    rw [show K = (K - k (j, l)) + k (j, l) by omega, pow_add, mul_assoc, hk (j, l), mul_zero]
  let yv : ∀ j : Fin (N + 1), Γ(X, U.1 ⊓ pullbackChart φ j) := fun j => fV φ U f j ^ K * a j
  have hyc : TwistCompat φ m U.1 yv := by
    intro j l
    have h := hkill j l
    simp only [defect, mul_sub, sub_eq_zero] at h
    simp only [yv, map_mul, map_pow, restrictFun_restrictFun]
    rw [mul_left_comm]
    convert h using 2
  refine ⟨n + K, ⟨yv, hyc⟩, twistObj.ext (funext fun j => ?_)⟩
  rw [twist_res_val, twist_smul_val]
  apply restrictFun_injective_of_ge (basicOpen_fV_le_inf φ U f j) (inf_le_basicOpen_fV φ U f j)
  change restrictFun _ (restrictFun _ (fV φ U f j ^ K * a j)) = _
  rw [restrictFun_restrictFun, map_mul, map_pow, ha j, map_mul, restrictFun_restrictFun, map_pow,
    map_pow,
    restrictFun_restrictFun, pow_add]
  simp only [z, map_pow, map_mul, restrictFun_restrictFun]
  ring

end Extension

theorem main [IsSeparated π] [IsAffineHom φ] : (twist π φ m).IsQuasicoherent := by
  intro U f
  refine ⟨fun x => ?_, fun y hy => torsion π φ m U f y hy⟩
  obtain ⟨k, y, h⟩ := extension π φ m U f x
  exact ⟨k, y, h⟩

end P2mTwistQC

end

theorem _root_.AlgebraicGeometry.ProjSpace.isQuasicoherent_twist
    {A : Type u} [CommRing A] {N : ℕ} {X : Scheme.{u}}
    (π : X ⟶ Spec (.of A)) [IsSeparated π]
    (φ : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) A)) [IsAffineHom φ] (m : ℕ) :
    (ProjSpace.twist π φ m).IsQuasicoherent :=
  P2mTwistQC.main π φ m
end AlgebraicCurves.Geometry.Projective.Proofs.ProjSpace_isQuasicoherent_twist
end ProofImplementation

attribute [-simp] AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq
  AlgebraicGeometry.OModulePresheaf.Hom.id_app
  AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply
  AlgebraicGeometry.OModulePresheaf.AffHom.comp_app
  AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec
  AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe
  AlgebraicGeometry.OModulePresheaf.AffHom.id_app
  AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec
  AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app
  AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec
  AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec
  AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq
  AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq
  AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply
  AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq
