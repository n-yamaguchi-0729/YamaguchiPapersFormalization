/-
Copyright (c) 2026 Naganori Yamaguchi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
https://github.com/n-yamaguchi-0729
-/

import Nyll.JacobianVarieties.Kummer.OpenCurveCoverGenericCharacter
import Nyll.JacobianVarieties.Kummer.OpenCurveCoverCharacter
import Nyll.JacobianVarieties.Kummer.OpenCurveCoverAction
import Nyll.JacobianVarieties.Kummer.OpenCurveCoverTorsor
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

open AlgebraicGeometry CategoryTheory CategoryTheory.PreGaloisCategory TopologicalSpace
open EtaleFundamentalGroups.Cohomology
open scoped FintypeCatDiscrete

namespace AlgebraicCurve.CurveModel.OpenKummer

variable {K : Type u} [Field K] [IsSepClosed K]
  {F : Type v} [Field F] [Algebra K F]
  (M : CurveModel K F) (S : Set (Place K F)) (n : ℕ+)
  {X : Scheme.{u}} [IsIntegral X] [CompactSpace X]
  (j : X ⟶ M.C) [IsOpenImmersion j] (hj : DenseRange j)
  (hinterior : ∀ (y : X) (x : closedPoints M.C),
    x.val = j y → M.placeOfPoint x ∉ S)
  (hn : IsUnit ((n : ℕ) : K))

theorem character_basePoint_apply (u : Pic0.openKummerUnits K F S n)
    {Ω Ω' : Type u} [Field Ω] [Field Ω'] [IsSepClosed Ω] [IsSepClosed Ω']
    (xi : Spec (.of Ω) ⟶ X) (xi' : Spec (.of Ω') ⟶ X)
    (t : FiniteEtale.fiber xi ≅ FiniteEtale.fiber xi')
    (g : Aut (FiniteEtale.fiber xi)) :
    let : TopologicalSpace (rootsOfUnity (n : ℕ) K) := ⊥
    kummerMonodromyCharacter M S n u j hj hinterior hn xi'
      (FiniteEtale.fundamentalGroupIsoOfFiberIso xi xi' t g) =
        kummerMonodromyCharacter M S n u j hj hinterior hn xi g := by
  let : TopologicalSpace (rootsOfUnity (n : ℕ) K) := ⊥
  let T := kummerGeometricRootTorsor M S n u j hj hinterior hn xi
  let T' := kummerGeometricRootTorsor M S n u j hj hinterior hn xi'
  have := kummerGeometricRootAction_commutes M S n u j hj hinterior hn xi
  have := kummerGeometricRootAction_commutes M S n u j hj hinterior hn xi'
  let W := M.openKummerCover S n hn u j hj hinterior
  let b := FiniteEtale.fundamentalGroupIsoOfFiberIso xi xi' t
  let x : (FiniteEtale.fiber xi).obj W := Classical.choice T.nonempty
  let y : (FiniteEtale.fiber xi').obj W := t.hom.app W x
  have hcoeff (ζ : rootsOfUnity (n : ℕ) K) : t.hom.app W (ζ • x) = ζ • y := by
    exact ConcreteCategory.congr_hom
      (t.hom.naturality (kummerCoverRootScale M S n u j hj hinterior hn ζ).hom) x
  have hmon : t.hom.app W (g • x) = b g • y := by
    have hcat : g.hom.app W ≫ t.hom.app W = t.hom.app W ≫ (b g).hom.app W := by
      change g.hom.app W ≫ t.hom.app W = t.hom.app W ≫ (t.conjAut g).hom.app W
      simp only [Iso.conjAut_hom, Iso.conj_apply, NatTrans.comp_app]
      simp only [← Category.assoc, t.hom_inv_id_app, Category.id_comp]
    exact ConcreteCategory.congr_hom hcat x
  have hx : kummerMonodromyCharacter M S n u j hj hinterior hn xi g • x = g • x := by
    rw [kummerMonodromyCharacter_eq_torsorCharacter M S n u j hj hinterior hn xi x]
    exact sdiv_smul (g • x) x
  have hy : kummerMonodromyCharacter M S n u j hj hinterior hn xi' (b g) • y = b g • y := by
    rw [kummerMonodromyCharacter_eq_torsorCharacter M S n u j hj hinterior hn xi' y]
    exact sdiv_smul (b g • y) y
  exact (kummerGeometricRootAction_existsUnique M S n u j hj hinterior hn xi' y (b g • y)).unique hy
    ((hcoeff (kummerMonodromyCharacter M S n u j hj hinterior hn xi g)).symm.trans
      ((congrArg (t.hom.app W) hx).trans hmon))

include M j in
omit [IsSepClosed K] [CompactSpace X] in
private theorem genericGalois_surjective
    {Ω : Type u} [Field Ω] [Algebra X.functionField Ω]
    [IsSepClosed Ω] [IsSepClosure X.functionField Ω] :
    let xi := Spec.map (CommRingCat.ofHom (algebraMap X.functionField Ω))
    let genericMap := X.fromSpecStalk (genericPoint X)
    Function.Surjective (fun σ : Ω ≃ₐ[X.functionField] Ω =>
      FiniteEtale.fundamentalGroupHom genericMap xi
        (toAut (FiniteEtale.fiber xi) (Ω ≃ₐ[X.functionField] Ω) σ)) := by
  intro xi genericMap
  have : Smooth M.toBase := SmoothOfRelativeDimension.smooth 1 M.toBase
  have : Smooth (j ≫ M.toBase) := inferInstance
  have : IsIntegrallyClosed Γ(Spec (.of K), ⊤) := IsIntegrallyClosed.of_equiv
    (Scheme.ΓSpecIso (.of K)).symm.commRingCatIsoToRingEquiv
  have : IsNormalIntegral X := IsNormalIntegral.of_stalks X
    (fun x => (Smooth.isDomain_and_isIntegrallyClosed_stalk (j ≫ M.toBase) x).2)
  have : Subsingleton (Spec (X.presheaf.stalk (genericPoint X))) :=
    inferInstanceAs (Subsingleton (Spec (.of X.functionField)))
  have : QuasiCompact genericMap :=
    { isCompact_preimage := fun U _ _ =>
        (Set.Subsingleton.finite (fun a _ b _ => Subsingleton.elim a b)).isCompact }
  have : IsDominant genericMap := by
    rw [isDominant_iff, DenseRange, dense_iff_closure_eq]
    apply Set.eq_univ_of_forall
    intro x
    apply (genericPoint_specializes x).mem_closed isClosed_closure
    exact subset_closure ⟨IsLocalRing.closedPoint (CommRingCat.of X.functionField),
      Scheme.fromSpecStalk_closedPoint (X := X) (x := genericPoint X)⟩
  exact (FiniteEtale.fundamentalGroupHom_surjective_of_isPreimmersion_of_isDominant genericMap
    xi).comp
    (toAut_bijective (FiniteEtale.fiber xi) (Ω ≃ₐ[X.functionField] Ω)).surjective

private theorem generic_character_mul_apply (u w : Pic0.openKummerUnits K F S n)
    {Ω : Type u} [Field Ω] [Algebra X.functionField Ω]
    [IsSepClosed Ω] [IsSepClosure X.functionField Ω]
    (σ : Ω ≃ₐ[X.functionField] Ω) :
    let : TopologicalSpace (rootsOfUnity (n : ℕ) K) := ⊥
    let xi := Spec.map (CommRingCat.ofHom (algebraMap X.functionField Ω))
    let genericMap := X.fromSpecStalk (genericPoint X)
    let g := FiniteEtale.fundamentalGroupHom genericMap xi
      (toAut (FiniteEtale.fiber xi) (Ω ≃ₐ[X.functionField] Ω) σ)
    kummerMonodromyCharacter M S n (u * w) j hj hinterior hn (xi ≫ genericMap) g =
      kummerMonodromyCharacter M S n u j hj hinterior hn (xi ≫ genericMap) g *
        kummerMonodromyCharacter M S n w j hj hinterior hn (xi ≫ genericMap) g := by
  intro tμ xi genericMap g
  let ι : K →+* Ω := (algebraMap X.functionField Ω).comp (baseToFunctionField (j ≫ M.toBase))
  have hnΩ : IsUnit ((n : ℕ) : Ω) := by
    simpa only [map_natCast] using hn.map ι
  have : NeZero ((n : ℕ) : Ω) := ⟨hnΩ.ne_zero⟩
  obtain ⟨β, hβ⟩ := IsSepClosed.exists_pow_nat_eq
    (algebraMap X.functionField Ω (j.functionFieldMap hj (M.ffEquiv (u.val : F)))) (n : ℕ)
  obtain ⟨γ, hγ⟩ := IsSepClosed.exists_pow_nat_eq
    (algebraMap X.functionField Ω (j.functionFieldMap hj (M.ffEquiv (w.val : F)))) (n : ℕ)
  have hβγ : (β * γ) ^ (n : ℕ) =
      algebraMap X.functionField Ω (j.functionFieldMap hj (M.ffEquiv ((u * w).val : F))) := by
    rw [mul_pow, hβ, hγ]
    change _ = algebraMap X.functionField Ω (j.functionFieldMap hj (M.ffEquiv ((u.val : F) *
      (w.val : F))))
    rw [map_mul, map_mul, map_mul]
  have hβγ0 : β * γ ≠ 0 := by
    apply mt (fun hz => congrArg (fun x : Ω => x ^ (n : ℕ)) hz)
    rw [hβγ, zero_pow n.ne_zero]
    exact (map_ne_zero (algebraMap X.functionField Ω)).mpr
      ((map_ne_zero (j.functionFieldMap hj)).mpr
        ((map_ne_zero M.ffEquiv).mpr (Units.ne_zero (u * w).val)))
  have hu := kummerMonodromyCharacter_generic_mul_root M S n u j hj hinterior β hβ hn σ
  have hw := kummerMonodromyCharacter_generic_mul_root M S n w j hj hinterior γ hγ hn σ
  have huw := kummerMonodromyCharacter_generic_mul_root M S n (u * w) j hj hinterior (β * γ)
    hβγ hn σ
  apply rootsOfUnity.coe_injective
  apply ι.injective
  apply mul_right_cancel₀ hβγ0
  change ι ((kummerMonodromyCharacter M S n (u * w) j hj hinterior hn (xi ≫ genericMap) g :
    Kˣ) : K) * (β * γ) = _
  calc
    _ = σ (β * γ) := huw
    _ = σ β * σ γ := map_mul σ β γ
    _ = (ι ((kummerMonodromyCharacter M S n u j hj hinterior hn (xi ≫ genericMap) g : Kˣ) : K)
      * β) *
        (ι ((kummerMonodromyCharacter M S n w j hj hinterior hn (xi ≫ genericMap) g : Kˣ) : K)
          * γ) :=
      congrArg₂ (· * ·) hu.symm hw.symm
    _ = ι (((kummerMonodromyCharacter M S n u j hj hinterior hn (xi ≫ genericMap) g *
        kummerMonodromyCharacter M S n w j hj hinterior hn (xi ≫ genericMap) g : rootsOfUnity
          (n : ℕ) K) : Kˣ) : K) *
          (β * γ) := by
      change _ = ι (((kummerMonodromyCharacter M S n u j hj hinterior hn (xi ≫ genericMap) g :
        Kˣ) : K) *
        ((kummerMonodromyCharacter M S n w j hj hinterior hn (xi ≫ genericMap) g : Kˣ) : K)) *
          (β * γ)
      rw [map_mul]
      exact mul_mul_mul_comm _ _ _ _

/-- The actual monodromy character respects multiplication of the original
Kummer functions, at every geometric basepoint. -/
theorem kummerMonodromyCharacter_mul (u w : Pic0.openKummerUnits K F S n)
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (xi : Spec (.of Ω) ⟶ X) :
    let : TopologicalSpace (rootsOfUnity (n : ℕ) K) := ⊥
    let : DiscreteTopology (rootsOfUnity (n : ℕ) K) := ⟨rfl⟩
    kummerMonodromyCharacter M S n (u * w) j hj hinterior hn xi =
      kummerMonodromyCharacter M S n u j hj hinterior hn xi * kummerMonodromyCharacter M S n w
        j hj hinterior hn xi := by
  let : TopologicalSpace (rootsOfUnity (n : ℕ) K) := ⊥
  have : DiscreteTopology (rootsOfUnity (n : ℕ) K) := ⟨rfl⟩
  let Ωg := SeparableClosure X.functionField
  have : IsSepClosure X.functionField Ωg :=
    separableClosure.isSepClosure X.functionField (AlgebraicClosure X.functionField)
  let xig := Spec.map (CommRingCat.ofHom (algebraMap X.functionField Ωg))
  let genericMap := X.fromSpecStalk (genericPoint X)
  let t := Classical.choice (FiniteEtale.nonempty_fiber_iso (xig ≫ genericMap) xi)
  let b := FiniteEtale.fundamentalGroupIsoOfFiberIso (xig ≫ genericMap) xi t
  apply ContinuousMonoidHom.ext
  intro g
  obtain ⟨g₀, rfl⟩ := b.surjective g
  obtain ⟨σ, rfl⟩ := genericGalois_surjective M j (Ω := Ωg) g₀
  change kummerMonodromyCharacter M S n (u * w) j hj hinterior hn xi _ =
    kummerMonodromyCharacter M S n u j hj hinterior hn xi _ * kummerMonodromyCharacter M S n w
      j hj hinterior hn xi _
  rw [character_basePoint_apply, character_basePoint_apply, character_basePoint_apply]
  exact generic_character_mul_apply M S n j hj hinterior hn u w σ

/-- The actual Kummer functions map homomorphically to the actual continuous
characters of the geometric fundamental group. -/
def kummerMonodromyHom
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (xi : Spec (.of Ω) ⟶ X) :
    let : TopologicalSpace (rootsOfUnity (n : ℕ) K) := ⊥
    let : DiscreteTopology (rootsOfUnity (n : ℕ) K) := ⟨rfl⟩
    Pic0.openKummerUnits K F S n →* (Aut (FiniteEtale.fiber xi) →ₜ* rootsOfUnity (n : ℕ) K) := by
  let : TopologicalSpace (rootsOfUnity (n : ℕ) K) := ⊥
  have : DiscreteTopology (rootsOfUnity (n : ℕ) K) := ⟨rfl⟩
  refine {
    toFun := fun u => kummerMonodromyCharacter M S n u j hj hinterior hn xi
    map_one' := ?_
    map_mul' := fun u w => kummerMonodromyCharacter_mul M S n j hj hinterior hn u w xi }
  apply mul_left_cancel (a := kummerMonodromyCharacter M S n 1 j hj hinterior hn xi)
  rw [mul_one]
  simpa only [one_mul] using (kummerMonodromyCharacter_mul M S n j hj hinterior hn 1 1 xi).symm

end AlgebraicCurve.CurveModel.OpenKummer
