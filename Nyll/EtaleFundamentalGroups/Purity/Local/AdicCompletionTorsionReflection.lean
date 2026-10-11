/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Purity.Local.AdicCompletionAnnihilatedBaseChange
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import Mathlib.RingTheory.Flat.Equalizer
import Mathlib.RingTheory.Finiteness.Ideal

/-!
# Reflecting power-torsion through adic completion

For a finitely generated ideal `I`, an element of `\hat R \otimes_R M`
annihilated by `I ^ n` already comes from an `I ^ n`-annihilated element of
`M`.  This is the torsion-reflection calculation used in the mixed
completion/localization equalizer.
-/

noncomputable section

namespace EtaleFundamentalGroups

open scoped TensorProduct

universe u v

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/-- Simultaneous multiplication by a chosen generating family of an ideal. -/
private def idealGeneratorAction (J : Ideal R) :
    M →ₗ[R] (J.generators → M) where
  toFun m i := i.1 • m
  map_add' x y := by
    funext i
    exact smul_add _ _ _
  map_smul' r x := by
    funext i
    exact smul_comm _ _ _

private theorem idealGeneratorAction_mem_ker_iff
    (J : Ideal R) (m : M) :
    m ∈ LinearMap.ker (idealGeneratorAction (M := M) J) ↔
      ∀ r : J, r.1 • m = 0 := by
  constructor
  · intro hm r
    have hr : r.1 ∈ Submodule.span R (J.generators : Set R) := by
      rw [J.span_generators]
      exact r.2
    refine Submodule.span_induction (p := fun a : R ↦ fun _ ↦ a • m = 0)
      ?_ ?_ ?_ ?_ hr
    · intro a ha
      have hzero : idealGeneratorAction (M := M) J m = 0 := hm
      exact congrFun hzero ⟨a, ha⟩
    · exact zero_smul R m
    · intro a b _ _ ha hb
      rw [add_smul, ha, hb, add_zero]
    · intro a b _ hb
      rw [smul_eq_mul, mul_smul, hb, smul_zero]
  · intro hm
    rw [LinearMap.mem_ker]
    funext i
    exact hm ⟨i.1, Submodule.FG.generators_mem J i.2⟩

private theorem idealGeneratorAction_lTensor_piRight_apply
    (S : Type*) [CommRing S] [Algebra R S]
    (J : Ideal R) [Fintype J.generators] [DecidableEq J.generators]
    (x : S ⊗[R] M) (i : J.generators) :
    TensorProduct.piRight R S S (fun _ : J.generators ↦ M)
        ((idealGeneratorAction (M := M) J).lTensor S x) i =
      i.1 • x := by
  classical
  induction x using TensorProduct.inductionOn with
  | add x y hx hy =>
      simpa only [map_add, smul_add, Pi.add_apply] using
        congrArg₂ (fun a b ↦ a + b) hx hy
  | tmul s m => simp [idealGeneratorAction]

/-- Power-torsion in a completed tensor product is already defined over the
source.  The returned source element is annihilated by the same power. -/
theorem adicCompletion_exists_eq_tmul_of_isTorsionBySet_pow
    [IsNoetherianRing R] (I : Ideal R) (hI : I.FG) (n : ℕ)
    (x : AdicCompletion I R ⊗[R] M)
    (hx : ∀ r : (I ^ n : Ideal R), r.1 • x = 0) :
    ∃ m : M, (∀ r : (I ^ n : Ideal R), r.1 • m = 0) ∧
      x = 1 ⊗ₜ[R] m := by
  classical
  let J : Ideal R := I ^ n
  have hJ : J.FG := hI.pow
  let : Finite J.generators :=
    Set.finite_coe_iff.mpr (Submodule.FG.finite_generators hJ)
  let : Fintype J.generators := Fintype.ofFinite J.generators
  let a : M →ₗ[R] (J.generators → M) :=
    idealGeneratorAction (M := M) J
  have hxker : x ∈ LinearMap.ker (a.lTensor (AdicCompletion I R)) := by
    rw [LinearMap.mem_ker]
    apply (TensorProduct.piRight R (AdicCompletion I R)
      (AdicCompletion I R) (fun _ : J.generators ↦ M)).injective
    funext i
    rw [map_zero, Pi.zero_apply]
    exact idealGeneratorAction_lTensor_piRight_apply
      (M := M) (AdicCompletion I R) J x i |>.trans
        (hx ⟨i.1, Submodule.FG.generators_mem J i.2⟩)
  let z : AdicCompletion I R ⊗[R] LinearMap.ker a :=
    (LinearMap.tensorKerEquiv (AdicCompletion I R)
      (AdicCompletion I R) a).symm ⟨x, hxker⟩
  have hkerTorsion :
      Module.IsTorsionBySet R (LinearMap.ker a) J := by
    intro y r
    apply Subtype.ext
    exact (idealGeneratorAction_mem_ker_iff
      (M := M) J y.1).mp y.2 r
  obtain ⟨y, hy⟩ :=
    (adicCompletion_tensorProduct_mk_bijective_of_isTorsionBySet_pow
      I hI n hkerTorsion).2 z
  refine ⟨y.1, ?_, ?_⟩
  · exact (idealGeneratorAction_mem_ker_iff
      (M := M) J y.1).mp y.2
  · have hz := LinearMap.lTensor_ker_subtype_tensorKerEquiv_symm
      (AdicCompletion I R) (AdicCompletion I R) a ⟨x, hxker⟩
    have hz' : a.ker.subtype.lTensor (AdicCompletion I R) z = x := by
      simpa only [z] using hz
    rw [← hy] at hz'
    exact hz'.symm

end EtaleFundamentalGroups

end
