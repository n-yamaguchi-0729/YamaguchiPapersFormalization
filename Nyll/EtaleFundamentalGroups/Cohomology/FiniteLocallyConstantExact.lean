/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Cohomology.FiniteLocallyConstantPullbacks
import Nyll.EtaleFundamentalGroups.Cohomology.FiniteLocallyConstantEpis
import Nyll.EtaleFundamentalGroups.Cohomology.LocalTrivialization
import Nyll.EtaleFundamentalGroups.Cohomology.StalkFiber
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero
import Mathlib.Algebra.Category.Grp.Zero

/-!
# Exactness of finite local systems detected on one geometric stalk

Kernels are pullbacks along a zero object. The actual stalk functor detects
these pullbacks and detects epimorphisms for finite local systems on a
connected scheme. This proves short exactness of the descended sheaves,
without assuming exactness as descent data.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits EtaleCohomology

universe u

namespace EtaleFundamentalGroups.Cohomology

private theorem kernel_isPullback {C : Type*} [Category* C] [HasZeroMorphisms C]
    {K E H Z : C} (i : K ⟶ E) (p : E ⟶ H) (w : i ≫ p = 0)
    (h : IsLimit (KernelFork.ofι i w)) (hZ : IsZero Z) :
    IsPullback i (0 : K ⟶ Z) p (0 : Z ⟶ H) := by
  refine IsPullback.mk' (w.trans zero_comp.symm) ?_ ?_
  · intro T a b hab _
    exact Fork.IsLimit.hom_ext h hab
  · intro T a b hab
    let s := KernelFork.ofι a (hab.trans comp_zero)
    exact ⟨h.lift s, h.fac s WalkingParallelPair.zero, hZ.eq_of_tgt _ _⟩

private def kernel_of_isPullback {C : Type*} [Category* C] [HasZeroMorphisms C]
    {K E H Z : C} (i : K ⟶ E) (p : E ⟶ H) (w : i ≫ p = 0)
    (h : IsPullback i (0 : K ⟶ Z) p (0 : Z ⟶ H)) :
    IsLimit (KernelFork.ofι i w) := by
  refine Fork.IsLimit.mk _
    (fun s => h.lift s.ι 0 ((KernelFork.condition s).trans zero_comp.symm))
    (fun s => h.lift_fst _ _ _) ?_
  intro s m hm
  apply h.hom_ext
  · exact hm.trans (h.lift_fst _ _ _).symm
  · exact comp_zero.trans comp_zero.symm

variable {X : Scheme.{u}} [ConnectedSpace X]
  {Ω : Type u} [Field Ω] [IsSepClosed Ω] (ξ : Spec (.of Ω) ⟶ X)

/-- A short complex of finite locally constant abelian sheaves on a connected
scheme is short exact if its actual stalk at one geometric point is short exact. -/
theorem shortExact_of_finiteLocallyConstant_abelianStalk
    (S : ShortComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}))
    (h₁ : IsEtaleFiniteLocallyConstantSet
      ((sheafCompose X.smallEtaleTopology (forget AddCommGrpCat.{u})).obj S.X₁))
    (h₂ : IsEtaleFiniteLocallyConstantSet
      ((sheafCompose X.smallEtaleTopology (forget AddCommGrpCat.{u})).obj S.X₂))
    (h₃ : IsEtaleFiniteLocallyConstantSet
      ((sheafCompose X.smallEtaleTopology (forget AddCommGrpCat.{u})).obj S.X₃))
    (hs : (S.map (Scheme.pointSmallEtale ξ).sheafFiber).ShortExact) : S.ShortExact := by
  let Φ := (Scheme.pointSmallEtale ξ).sheafFiber (A := AddCommGrpCat.{u})
  let C := constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}
  let Z := C.obj (AddCommGrpCat.of PUnit.{u + 1})
  have hZ : IsZero Z := C.map_isZero (AddCommGrpCat.isZero_of_subsingleton _)
  have hm : IsPullback (Φ.map S.f) (0 : Φ.obj S.X₁ ⟶ Φ.obj Z)
      (Φ.map S.g) (0 : Φ.obj Z ⟶ Φ.obj S.X₃) :=
    kernel_isPullback _ _ _ hs.fIsKernel (Φ.map_isZero hZ)
  have hp : IsPullback S.f (0 : S.X₁ ⟶ Z) S.g (0 : Z ⟶ S.X₃) := by
    apply isPullback_of_finiteLocallyConstant_abelianStalk ξ _ _ _ _
      (S.zero.trans zero_comp.symm) h₁ h₂
      (constantAbelian_isFiniteLocallyConstant X (AddCommGrpCat.of PUnit.{u + 1})) h₃
    simpa only [Functor.map_zero] using hm
  let hk := kernel_of_isPullback S.f S.g S.zero hp
  have : Mono S.f := mono_of_isLimit_fork hk
  have : Epi S.g := epi_of_surjective_finiteLocallyConstant_abelianStalk ξ S.g h₂ h₃
    ((AddCommGrpCat.epi_iff_surjective _).mp hs.epi_g)
  exact ⟨S.exact_of_f_is_kernel hk⟩

end EtaleFundamentalGroups.Cohomology
