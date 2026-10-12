/-
Copyright (c) 2026 Naganori Yamaguchi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
https://github.com/n-yamaguchi-0729
-/

import Nyll.JacobianVarieties.Kummer.CurveCoverGenericCharacter
import Nyll.JacobianVarieties.Kummer.CurveCoverCharacter
import Nyll.JacobianVarieties.Kummer.CurveCoverAction
import Nyll.JacobianVarieties.Kummer.CurveCoverTorsor
import Nyll.EtaleFundamentalGroups.GeometricFiber.BasePoint
import Nyll.EtaleFundamentalGroups.GeometricFiber.GenericPointSurjective
import Nyll.SchemeTheory.LocalGeometry.SmoothStalkNormality
import Nyll.SchemeTheory.Normalization.Normal
import Mathlib.FieldTheory.IsSepClosed

/-!
# Multiplicativity of actual Kummer monodromy

At a geometric generic point the character on a product is computed using the
product of the actual roots. Surjectivity of the generic Galois map detects
equality of characters. Naturality of the same root-scaling automorphisms under
fiber-functor comparison carries this equality to every geometric basepoint.
-/

noncomputable section

universe u v

open AlgebraicGeometry CategoryTheory CategoryTheory.PreGaloisCategory
open EtaleFundamentalGroups.Cohomology
open scoped FintypeCatDiscrete

namespace AlgebraicCurve.CurveModel

variable {K : Type u} [Field K] [IsSepClosed K]
  {F : Type v} [Field F] [Algebra K F]
  (M : CurveModel K F) (n : ℕ+) (hn : IsUnit ((n : ℕ) : K))

private theorem character_basePoint_apply (u : Pic0.kummerUnits K F n)
    {Ω Ω' : Type u} [Field Ω] [Field Ω'] [IsSepClosed Ω] [IsSepClosed Ω']
    (xi : Spec (.of Ω) ⟶ M.C) (xi' : Spec (.of Ω') ⟶ M.C)
    (t : FiniteEtale.fiber xi ≅ FiniteEtale.fiber xi')
    (g : Aut (FiniteEtale.fiber xi)) :
    let : TopologicalSpace (rootsOfUnity (n : ℕ) K) := ⊥
    M.kummerMonodromyCharacter n u hn xi'
      (FiniteEtale.fundamentalGroupIsoOfFiberIso xi xi' t g) =
        M.kummerMonodromyCharacter n u hn xi g := by
  let : TopologicalSpace (rootsOfUnity (n : ℕ) K) := ⊥
  let T := M.kummerGeometricRootTorsor n u hn xi
  let T' := M.kummerGeometricRootTorsor n u hn xi'
  have := M.kummerGeometricRootAction_commutes n u hn xi
  have := M.kummerGeometricRootAction_commutes n u hn xi'
  let W := M.kummerCover n hn u
  let b := FiniteEtale.fundamentalGroupIsoOfFiberIso xi xi' t
  let x : (FiniteEtale.fiber xi).obj W := Classical.choice T.nonempty
  let y : (FiniteEtale.fiber xi').obj W := t.hom.app W x
  have hcoeff (ζ : rootsOfUnity (n : ℕ) K) : t.hom.app W (ζ • x) = ζ • y := by
    exact ConcreteCategory.congr_hom
      (t.hom.naturality (M.kummerCoverRootScale n u hn ζ).hom) x
  have hmon : t.hom.app W (g • x) = b g • y := by
    have hcat : g.hom.app W ≫ t.hom.app W = t.hom.app W ≫ (b g).hom.app W := by
      change g.hom.app W ≫ t.hom.app W = t.hom.app W ≫ (t.conjAut g).hom.app W
      simp only [Iso.conjAut_hom, Iso.conj_apply, NatTrans.comp_app]
      simp only [← Category.assoc, t.hom_inv_id_app, Category.id_comp]
    exact ConcreteCategory.congr_hom hcat x
  have hx : M.kummerMonodromyCharacter n u hn xi g • x = g • x := by
    rw [M.kummerMonodromyCharacter_eq_torsorCharacter n u hn xi x]
    exact sdiv_smul (g • x) x
  have hy : M.kummerMonodromyCharacter n u hn xi' (b g) • y = b g • y := by
    rw [M.kummerMonodromyCharacter_eq_torsorCharacter n u hn xi' y]
    exact sdiv_smul (b g • y) y
  exact (M.kummerGeometricRootAction_existsUnique n u hn xi' y (b g • y)).unique hy
    ((hcoeff (M.kummerMonodromyCharacter n u hn xi g)).symm.trans
      ((congrArg (t.hom.app W) hx).trans hmon))

omit [IsSepClosed K] in
private theorem genericGalois_surjective
    {Ω : Type u} [Field Ω] [Algebra M.C.functionField Ω]
    [IsSepClosed Ω] [IsSepClosure M.C.functionField Ω] :
    let xi := Spec.map (CommRingCat.ofHom (algebraMap M.C.functionField Ω))
    let j := M.C.fromSpecStalk (genericPoint M.C)
    Function.Surjective (fun σ : Ω ≃ₐ[M.C.functionField] Ω =>
      FiniteEtale.fundamentalGroupHom j xi
        (toAut (FiniteEtale.fiber xi) (Ω ≃ₐ[M.C.functionField] Ω) σ)) := by
  intro xi j
  have : Smooth M.toBase := SmoothOfRelativeDimension.smooth 1 M.toBase
  have : IsIntegrallyClosed Γ(Spec (.of K), ⊤) := IsIntegrallyClosed.of_equiv
    (Scheme.ΓSpecIso (.of K)).symm.commRingCatIsoToRingEquiv
  have : IsNormalIntegral M.C := IsNormalIntegral.of_stalks M.C
    (fun x => (Smooth.isDomain_and_isIntegrallyClosed_stalk M.toBase x).2)
  have : Subsingleton (Spec (M.C.presheaf.stalk (genericPoint M.C))) :=
    inferInstanceAs (Subsingleton (Spec (.of M.C.functionField)))
  have : QuasiCompact j :=
    { isCompact_preimage := fun U _ _ =>
        (Set.Subsingleton.finite (fun a _ b _ => Subsingleton.elim a b)).isCompact }
  have : IsDominant j := by
    rw [isDominant_iff, DenseRange, dense_iff_closure_eq]
    apply Set.eq_univ_of_forall
    intro x
    apply (genericPoint_specializes x).mem_closed isClosed_closure
    exact subset_closure ⟨IsLocalRing.closedPoint (CommRingCat.of M.C.functionField),
      Scheme.fromSpecStalk_closedPoint (X := M.C) (x := genericPoint M.C)⟩
  exact (FiniteEtale.fundamentalGroupHom_surjective_of_isPreimmersion_of_isDominant j xi).comp
    (toAut_bijective (FiniteEtale.fiber xi) (Ω ≃ₐ[M.C.functionField] Ω)).surjective

private theorem generic_character_mul_apply (u w : Pic0.kummerUnits K F n)
    {Ω : Type u} [Field Ω] [Algebra M.C.functionField Ω]
    [IsSepClosed Ω] [IsSepClosure M.C.functionField Ω]
    (σ : Ω ≃ₐ[M.C.functionField] Ω) :
    let : TopologicalSpace (rootsOfUnity (n : ℕ) K) := ⊥
    let xi := Spec.map (CommRingCat.ofHom (algebraMap M.C.functionField Ω))
    let j := M.C.fromSpecStalk (genericPoint M.C)
    let g := FiniteEtale.fundamentalGroupHom j xi
      (toAut (FiniteEtale.fiber xi) (Ω ≃ₐ[M.C.functionField] Ω) σ)
    M.kummerMonodromyCharacter n (u * w) hn (xi ≫ j) g =
      M.kummerMonodromyCharacter n u hn (xi ≫ j) g *
        M.kummerMonodromyCharacter n w hn (xi ≫ j) g := by
  intro tμ xi j g
  let ι : K →+* Ω := (algebraMap M.C.functionField Ω).comp (baseToFunctionField M.toBase)
  have hnΩ : IsUnit ((n : ℕ) : Ω) := by
    simpa only [map_natCast] using hn.map ι
  have : NeZero ((n : ℕ) : Ω) := ⟨hnΩ.ne_zero⟩
  obtain ⟨β, hβ⟩ := IsSepClosed.exists_pow_nat_eq
    (algebraMap M.C.functionField Ω (M.ffEquiv (u.val : F))) (n : ℕ)
  obtain ⟨γ, hγ⟩ := IsSepClosed.exists_pow_nat_eq
    (algebraMap M.C.functionField Ω (M.ffEquiv (w.val : F))) (n : ℕ)
  have hβγ : (β * γ) ^ (n : ℕ) =
      algebraMap M.C.functionField Ω (M.ffEquiv ((u * w).val : F)) := by
    rw [mul_pow, hβ, hγ]
    change _ = algebraMap M.C.functionField Ω (M.ffEquiv ((u.val : F) * (w.val : F)))
    rw [map_mul, map_mul]
  have hβγ0 : β * γ ≠ 0 := by
    apply mt (fun hz => congrArg (fun x : Ω => x ^ (n : ℕ)) hz)
    rw [hβγ, zero_pow n.ne_zero]
    exact (map_ne_zero (algebraMap M.C.functionField Ω)).mpr
      ((map_ne_zero M.ffEquiv).mpr (Units.ne_zero (u * w).val))
  have hu := M.kummerMonodromyCharacter_generic_mul_root n u β hβ hn σ
  have hw := M.kummerMonodromyCharacter_generic_mul_root n w γ hγ hn σ
  have huw := M.kummerMonodromyCharacter_generic_mul_root n (u * w) (β * γ) hβγ hn σ
  apply rootsOfUnity.coe_injective
  apply ι.injective
  apply mul_right_cancel₀ hβγ0
  change ι ((M.kummerMonodromyCharacter n (u * w) hn (xi ≫ j) g : Kˣ) : K) * (β * γ) = _
  calc
    _ = σ (β * γ) := huw
    _ = σ β * σ γ := map_mul σ β γ
    _ = (ι ((M.kummerMonodromyCharacter n u hn (xi ≫ j) g : Kˣ) : K) * β) *
        (ι ((M.kummerMonodromyCharacter n w hn (xi ≫ j) g : Kˣ) : K) * γ) :=
      congrArg₂ (· * ·) hu.symm hw.symm
    _ = ι (((M.kummerMonodromyCharacter n u hn (xi ≫ j) g *
        M.kummerMonodromyCharacter n w hn (xi ≫ j) g : rootsOfUnity (n : ℕ) K) : Kˣ) : K) *
          (β * γ) := by
      change _ = ι (((M.kummerMonodromyCharacter n u hn (xi ≫ j) g : Kˣ) : K) *
        ((M.kummerMonodromyCharacter n w hn (xi ≫ j) g : Kˣ) : K)) * (β * γ)
      rw [map_mul]
      exact mul_mul_mul_comm _ _ _ _

/-- The actual monodromy character respects multiplication of the original
Kummer functions, at every geometric basepoint. -/
theorem kummerMonodromyCharacter_mul (u w : Pic0.kummerUnits K F n)
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (xi : Spec (.of Ω) ⟶ M.C) :
    let : TopologicalSpace (rootsOfUnity (n : ℕ) K) := ⊥
    let : DiscreteTopology (rootsOfUnity (n : ℕ) K) := ⟨rfl⟩
    M.kummerMonodromyCharacter n (u * w) hn xi =
      M.kummerMonodromyCharacter n u hn xi * M.kummerMonodromyCharacter n w hn xi := by
  let : TopologicalSpace (rootsOfUnity (n : ℕ) K) := ⊥
  have : DiscreteTopology (rootsOfUnity (n : ℕ) K) := ⟨rfl⟩
  let Ωg := SeparableClosure M.C.functionField
  have : IsSepClosure M.C.functionField Ωg :=
    separableClosure.isSepClosure M.C.functionField (AlgebraicClosure M.C.functionField)
  let xig := Spec.map (CommRingCat.ofHom (algebraMap M.C.functionField Ωg))
  let j := M.C.fromSpecStalk (genericPoint M.C)
  let t := Classical.choice (FiniteEtale.nonempty_fiber_iso (xig ≫ j) xi)
  let b := FiniteEtale.fundamentalGroupIsoOfFiberIso (xig ≫ j) xi t
  apply ContinuousMonoidHom.ext
  intro g
  obtain ⟨g₀, rfl⟩ := b.surjective g
  obtain ⟨σ, rfl⟩ := M.genericGalois_surjective (Ω := Ωg) g₀
  change M.kummerMonodromyCharacter n (u * w) hn xi _ =
    M.kummerMonodromyCharacter n u hn xi _ * M.kummerMonodromyCharacter n w hn xi _
  rw [character_basePoint_apply, character_basePoint_apply, character_basePoint_apply]
  exact M.generic_character_mul_apply n hn u w σ

/-- The actual Kummer functions map homomorphically to the actual continuous
characters of the geometric fundamental group. -/
def kummerMonodromyHom
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (xi : Spec (.of Ω) ⟶ M.C) :
    let : TopologicalSpace (rootsOfUnity (n : ℕ) K) := ⊥
    let : DiscreteTopology (rootsOfUnity (n : ℕ) K) := ⟨rfl⟩
    Pic0.kummerUnits K F n →* (Aut (FiniteEtale.fiber xi) →ₜ* rootsOfUnity (n : ℕ) K) := by
  let : TopologicalSpace (rootsOfUnity (n : ℕ) K) := ⊥
  have : DiscreteTopology (rootsOfUnity (n : ℕ) K) := ⟨rfl⟩
  refine {
    toFun := fun u => M.kummerMonodromyCharacter n u hn xi
    map_one' := ?_
    map_mul' := fun u w => M.kummerMonodromyCharacter_mul n hn u w xi }
  apply mul_left_cancel (a := M.kummerMonodromyCharacter n 1 hn xi)
  rw [mul_one]
  simpa only [one_mul] using (M.kummerMonodromyCharacter_mul n hn 1 1 xi).symm

end AlgebraicCurve.CurveModel
