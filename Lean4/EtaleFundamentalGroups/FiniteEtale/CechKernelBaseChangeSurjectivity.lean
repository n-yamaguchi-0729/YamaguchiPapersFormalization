/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import AlgebraicCurves.Cohomology.Sheaves.OModulePresheaf_exists_cochain_baseChange_equiv_of_locallyTrivial
import AlgebraicCurves.Cohomology.Sheaves.OModulePresheaf_d_zero_ofModules_eq_zero_iff_existsUnique
import SchemeTheory.Cohomology.Cech.TwoChartCech

/-!
# Actual section surjectivity and the Čech kernel comparison

The affine-cochain tensor equivalence has an explicit formula in terms of
the pullback adjunction unit. Using that formula and actual sheaf gluing,
surjectivity of the pullback map on sections supplies surjectivity of the
canonical degree-zero kernel base-change map.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace AlgebraicGeometry.OModulePresheaf

universe u

/-- The actual pullback map on global sections supplies the surjectivity
hypothesis of the finite free H⁰ model. -/
theorem surjective_kerBaseChangeHom_of_surjective_pullbackUnit
    {R : Type u} [CommRing R] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R)) [IsSeparated f]
    (M : X.Modules) (𝒰 : X.OrderedAffineCover)
    (htriv : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
      Nonempty ((Scheme.Modules.pullback U.ι).obj M ≅
        SheafOfModules.unit U.toScheme.ringCatSheaf))
    (A : Type u) [CommRing A] [Algebra R A]
    (hSurjective : Function.Surjective
      (((Scheme.Modules.pullbackPushforwardAdjunction
        (pullback.fst f (Scheme.TwoAffineOpenCover.specMap R A))).unit.app M).app ⊤)) :
    Function.Surjective
      (TwoChartCech.kerBaseChangeHom ((ofModules f M).d 𝒰 0) A) := by
  let p := pullback.fst f (Scheme.TwoAffineOpenCover.specMap R A)
  let fA := pullback.snd f (Scheme.TwoAffineOpenCover.specMap R A)
  let MA := (Scheme.Modules.pullback p).obj M
  let F := ofModules f M
  let FA := ofModules fA MA
  let η := (Scheme.Modules.pullbackPushforwardAdjunction p).unit.app M
  obtain ⟨E, hEd, hEt⟩ := exists_cochain_baseChange_equiv_of_locallyTrivial f 𝒰 M htriv A
  intro z
  have hCocycle : FA.d (𝒰.baseChange f A) 0 (E 0 z.1) = 0 := by
    have h := LinearMap.congr_fun (hEd 0) z.1
    have hz : (F.d 𝒰 0).baseChange A z.1 = 0 := z.2
    change E 1 ((F.d 𝒰 0).baseChange A z.1) =
      FA.d (𝒰.baseChange f A) 0 (E 0 z.1) at h
    rw [hz, map_zero] at h
    exact h.symm
  obtain ⟨y, hy, _⟩ :=
    (d_zero_ofModules_eq_zero_iff_existsUnique fA MA (𝒰.baseChange f A) (E 0 z.1)).mp
      hCocycle
  obtain ⟨x, hx⟩ := hSurjective y
  let c : F.cochain 𝒰 0 :=
    fun s => F.res (show 𝒰.inter s ≤ ⊤ from le_top) x
  have hc : F.d 𝒰 0 c = 0 := by
    funext s
    have hd := F.d_apply 𝒰 0 c s
    rw [Fin.sum_univ_two] at hd
    simp only [Fin.val_zero, pow_zero, one_smul, Fin.val_one, pow_one,
      neg_smul, c, ← sub_eq_add_neg] at hd
    have h0 := F.res_res (𝒰.inter_le_inter_face s 0)
      (show 𝒰.inter (𝒰.face s 0) ≤ ⊤ from le_top) x
    have h1 := F.res_res (𝒰.inter_le_inter_face s 1)
      (show 𝒰.inter (𝒰.face s 1) ≤ ⊤ from le_top) x
    exact hd.trans ((congrArg₂ (fun a b : F.obj (𝒰.inter s) => a - b) h0 h1).trans
      (sub_self (F.res (show 𝒰.inter s ≤ ⊤ from le_top) x)))
  let cK : LinearMap.ker (F.d 𝒰 0) := ⟨c, hc⟩
  refine ⟨1 ⊗ₜ[R] cK, Subtype.ext ?_⟩
  change (LinearMap.ker (F.d 𝒰 0)).subtype.baseChange A (1 ⊗ₜ[R] cK) = z.1
  rw [LinearMap.baseChange_tmul]
  apply (E 0).injective
  refine funext (fun s : 𝒰.Idx 0 => ?_)
  have hUnit : (η.app (𝒰.inter s)).hom
        (M.presheaf.map (homOfLE (show 𝒰.inter s ≤ ⊤ from le_top)).op x) =
      MA.presheaf.map
        (homOfLE (p.preimage_mono (show 𝒰.inter s ≤ ⊤ from le_top))).op
        ((η.app ⊤).hom x) := by
    have hn := η.mapPresheaf.naturality
      (homOfLE (show 𝒰.inter s ≤ ⊤ from le_top)).op
    refine (ConcreteCategory.congr_hom hn x).trans ?_
    have hi : (TopologicalSpace.Opens.map p.base).map
        (homOfLE (show 𝒰.inter s ≤ ⊤ from le_top)) =
      homOfLE (p.preimage_mono (show 𝒰.inter s ≤ ⊤ from le_top)) := Subsingleton.elim _ _
    change MA.presheaf.map
        ((TopologicalSpace.Opens.map p.base).map
          (homOfLE (show 𝒰.inter s ≤ ⊤ from le_top))).op ((η.app ⊤).hom x) = _
    rw [hi]
  calc
    E 0 (1 ⊗ₜ[R] c) s =
        FA.res (𝒰.baseChange_inter_le f A s) ((η.app (𝒰.inter s)).hom (c s)) := by
      exact (hEt 0 1 c s).trans (one_smul A _)
    _ = FA.res (show (𝒰.baseChange f A).inter s ≤ ⊤ from le_top)
        ((η.app ⊤).hom x) := by
      dsimp only [c]
      rw [ofModules_res_apply, hUnit]
      change FA.res (𝒰.baseChange_inter_le f A s)
          (FA.res (p.preimage_mono (show 𝒰.inter s ≤ ⊤ from le_top))
            ((η.app ⊤).hom x)) =
        FA.res (show (𝒰.baseChange f A).inter s ≤ ⊤ from le_top) ((η.app ⊤).hom x)
      exact FA.res_res (𝒰.baseChange_inter_le f A s)
        (p.preimage_mono (show 𝒰.inter s ≤ ⊤ from le_top)) ((η.app ⊤).hom x)
    _ = FA.res (show (𝒰.baseChange f A).inter s ≤ ⊤ from le_top) y :=
      congrArg (FA.res (show (𝒰.baseChange f A).inter s ≤ ⊤ from le_top)) hx
    _ = E 0 z.1 s := (hy s).symm

end AlgebraicGeometry.OModulePresheaf
