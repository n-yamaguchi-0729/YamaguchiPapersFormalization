/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_GoodReductionJacobian_RelativeGroupLaw_formallyUnramified_schemeNsmul_of_forall_sqZero.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Geometry.AbelianSchemes.GroupLaw.Kernel
import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified

/-!
# Relative Group Law formally Unramified scheme Nsmul of forall sq Zero
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.AbelianSchemes.Theorems.Proofs
namespace RelativeGroupLaw_formallyUnramified_schemeNsmul_of_forall_sqZero

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem
  _root_.GoodReductionJacobian.RelativeGroupLaw.formallyUnramified_schemeNsmul_of_forall_sqZero
    {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
    (G : RelativeGroupLaw R f)
    (hcomm : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f),
      G.mul t x y = G.mul t y x)
    (n : ℕ)
    (hTF : ∀ (R' S' : CommRingCat.{u}) (φ : R' ⟶ S'), Function.Surjective φ →
      RingHom.ker φ.hom ^ 2 = ⊥ →
      ∀ (t : Spec R' ⟶ Spec (CommRingCat.of R)) (k : SchemeHomOver t f),
        schemeHomOverComp (Spec.map φ) rfl k = G.one (Spec.map φ ≫ t) →
        G.nsmul t n k = G.one t → k = G.one t) :
    FormallyUnramified (G.schemeNsmul n) := by
  have schemeHomOverComp_idPoint : ∀ {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
      (x : SchemeHomOver t f), schemeHomOverComp x.1 x.2 (RelativeGroupLaw.idPoint (f := f)) = x :=
    fun x => Subtype.ext (Category.comp_id x.1)
  have nsmul_coe : ∀ {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} (m : ℕ) (x : SchemeHomOver
    t f),
      (G.nsmul t m x).1 = x.1 ≫ G.schemeNsmul m := by
    intro T t m x
    have h : schemeHomOverComp x.1 x.2 (G.nsmul f m RelativeGroupLaw.idPoint)
        = G.nsmul t m (schemeHomOverComp x.1 x.2 RelativeGroupLaw.idPoint) :=
      G.nsmul_natural f t x.1 x.2 m RelativeGroupLaw.idPoint
    rw [schemeHomOverComp_idPoint] at h
    exact (congrArg Subtype.val h).symm
  have pow_eq_nsmul : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (m : ℕ) (x :
    SchemeHomOver t f),
      (letI := G.pointGroup t; x ^ m) = G.nsmul t m x := by
    intro T t m x
    let := G.pointGroup t
    induction m with
    | zero => rfl
    | succ m ih => rw [pow_succ, ih, G.nsmul_succ]; rfl
  refine FormallyUnramified.of_hom_ext _ (fun R' S' φ hsurj hker g₁ g₂ hred hcomp => ?_)
  let t : Spec R' ⟶ Spec (CommRingCat.of R) := g₁ ≫ f
  have ht₂ : g₂ ≫ f = t := by
    have h₁ : g₁ ≫ f = g₁ ≫ G.schemeNsmul n ≫ f := by rw [G.schemeNsmul_over]
    have h₂ : g₂ ≫ f = g₂ ≫ G.schemeNsmul n ≫ f := by rw [G.schemeNsmul_over]
    rw [h₂, ← Category.assoc, ← hcomp, Category.assoc, ← h₁]
  let x₁ : SchemeHomOver t f := ⟨g₁, rfl⟩
  let x₂ : SchemeHomOver t f := ⟨g₂, ht₂⟩
  let : CommGroup (SchemeHomOver t f) :=
    { G.pointGroup t with mul_comm := hcomm t }
  have hnpow : x₁ ^ n = x₂ ^ n := by
    rw [pow_eq_nsmul, pow_eq_nsmul]
    exact Subtype.ext (((nsmul_coe n x₁).trans hcomp).trans (nsmul_coe n x₂).symm)
  let k : SchemeHomOver t f := x₁ * x₂⁻¹
  have hknpow : G.nsmul t n k = G.one t := by
    rw [← pow_eq_nsmul]
    change (x₁ * x₂⁻¹) ^ n = 1
    rw [← div_eq_mul_inv, div_pow, hnpow, div_self']
  let t' : Spec S' ⟶ Spec (CommRingCat.of R) := Spec.map φ ≫ t
  let grp' : Group (SchemeHomOver t' f) := G.pointGroup t'
  let red : SchemeHomOver t f →* SchemeHomOver t' f :=
    { toFun := schemeHomOverComp (Spec.map φ) rfl
      map_one' := G.one_natural t t' (Spec.map φ) rfl
      map_mul' := fun x y => G.mul_natural t t' (Spec.map φ) rfl x y }
  have hkred : schemeHomOverComp (Spec.map φ) rfl k = G.one (Spec.map φ ≫ t) := by
    have hx₁₂ : red x₁ = red x₂ := Subtype.ext hred
    change red (x₁ * x₂⁻¹) = 1
    rw [map_mul, map_inv, hx₁₂, mul_inv_cancel]
  have hkone : k = G.one t := hTF R' S' φ hsurj hker t k hkred hknpow
  have hx : x₁ = x₂ := by
    have : x₁ * x₂⁻¹ = 1 := hkone
    exact mul_inv_eq_one.mp this
  exact congrArg Subtype.val hx
end RelativeGroupLaw_formallyUnramified_schemeNsmul_of_forall_sqZero
end AlgebraicCurves.Geometry.AbelianSchemes.Theorems.Proofs
end ProofImplementation
