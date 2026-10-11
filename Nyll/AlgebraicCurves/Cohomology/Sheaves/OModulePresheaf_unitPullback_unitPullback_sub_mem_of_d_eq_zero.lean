/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_OModulePresheaf_unitPullback_unitPullback_sub_mem_of_d_eq_zero.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.GroupTheory.Perm.Sign
import Mathlib.AlgebraicGeometry.Scheme
import Nyll.SchemeTheory.Cohomology.Cech.OrderedAffineCoverCech
import Nyll.AlgebraicCurves.Cohomology.Cech.OrderedAffineCoverCechCup
import Nyll.AlgebraicCurves.Cohomology.Sheaves.OrderedAffineCoverCochainPullback
import Nyll.AlgebraicCurves.Cohomology.Cech.OrderedAffineCoverCechOrdered

/-!
# OModule Presheaf unit Pullback unit Pullback sub mem of d eq zero
-/

section ProofImplementation

namespace AlgebraicCurves.Cohomology.Sheaves.Proofs
namespace OModulePresheaf_unitPullback_unitPullback_sub_mem_of_d_eq_zero

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace FHSOL


open _root_.AlgebraicGeometry.OModulePresheaf
open _root_.AlgebraicGeometry.Scheme


theorem comp_eq
    {R R' R'' : Type u} [CommRing R] [CommRing R'] [CommRing R''] {X Y Z : Scheme.{u}}
    (πX : X ⟶ Spec (CommRingCat.of R'')) (πY : Y ⟶ Spec (CommRingCat.of R')) (πZ : Z ⟶ Spec
      (CommRingCat.of R))
    (g : X ⟶ Y) (h : Y ⟶ Z)
    (𝒲 : X.OrderedAffineCover) (𝒱 : Y.OrderedAffineCover) (𝒦 : Z.OrderedAffineCover)
    (mu : 𝒲.ι → 𝒱.ι) (lam : 𝒱.ι → 𝒦.ι)
    (hmu : ∀ w, 𝒲.U w ≤ g ⁻¹ᵁ 𝒱.U (mu w)) (hlam : ∀ v, 𝒱.U v ≤ h ⁻¹ᵁ 𝒦.U (lam v))
    (hcomp : ∀ w, 𝒲.U w ≤ (g ≫ h) ⁻¹ᵁ 𝒦.U ((lam ∘ mu) w))
    (n : ℕ) (z : (OModulePresheaf.unit πZ).cochain 𝒦 n) :
    OModulePresheaf.unitPullback (πX := πX) g 𝒲 𝒱 mu hmu n
        (OModulePresheaf.unitPullback (πX := πY) h 𝒱 𝒦 lam hlam n z) =
      OModulePresheaf.unitPullback (πX := πX) (g ≫ h) 𝒲 𝒦 (lam ∘ mu) hcomp n z := by
  classical
  funext s
  have happLE : ∀ {A B : Scheme.{u}} (f : A ⟶ B) (U : B.Opens) (V : A.Opens) (e : V ≤ f ⁻¹ᵁ U) (x :
    Γ(B, U)),
      (A.presheaf.map (homOfLE e).op).hom ((f.app U).hom x) = (f.appLE U V e).hom x := by
    intro A B f U V e x
    rfl
  by_cases hinj : Function.Injective ((lam ∘ mu) ∘ s.1)
  · have hinj₁ : Function.Injective (mu ∘ s.1) := by
      intro a b hab
      exact hinj (congrArg lam hab)
    have hinj₂ : Function.Injective (lam ∘ (𝒲.sortIdx 𝒱 mu s hinj₁).1) := by
      rw [Scheme.OrderedAffineCover.sortIdx_val]
      exact hinj.comp (Tuple.sort (mu ∘ s.1)).injective
    rw [unitPullback_apply_of_injective _ _ _ _ _ _ _ _ hinj,
      unitPullback_apply_of_injective _ _ _ _ _ _ _ _ hinj₁,
      unitPullback_apply_of_injective _ _ _ _ _ _ _ _ hinj₂]
    have hidx : 𝒱.sortIdx 𝒦 lam (𝒲.sortIdx 𝒱 mu s hinj₁) hinj₂ = 𝒲.sortIdx 𝒦 (lam ∘ mu) s hinj := by
      apply Subtype.ext
      simp only [Scheme.OrderedAffineCover.sortIdx_val]
      exact Tuple.comp_perm_comp_sort_eq_comp_sort (f := (lam ∘ mu) ∘ s.1) (σ := Tuple.sort (mu ∘
        s.1))
    have hperm : Tuple.sort ((lam ∘ mu) ∘ s.1) =
        Tuple.sort (mu ∘ s.1) * Tuple.sort (lam ∘ (𝒲.sortIdx 𝒱 mu s hinj₁).1) := by
      apply DFunLike.coe_injective
      apply hinj.comp_left
      change ((lam ∘ mu) ∘ s.1) ∘ ⇑(Tuple.sort ((lam ∘ mu) ∘ s.1)) =
        ((lam ∘ mu) ∘ s.1) ∘ ⇑(Tuple.sort (mu ∘ s.1) * Tuple.sort (lam ∘ (𝒲.sortIdx 𝒱 mu s
          hinj₁).1))
      rw [Equiv.Perm.coe_mul, ← Function.comp_assoc]
      have h1 := congrArg Subtype.val hidx
      simp only [Scheme.OrderedAffineCover.sortIdx_val] at h1
      exact h1.symm
    rw [map_zsmul, map_zsmul, smul_smul, hperm, Equiv.Perm.sign_mul, Units.val_mul, mul_comm]
    congr 1
    change (∀ s : 𝒦.Idx n, Γ(Z, 𝒦.inter s)) at z
    rw [happLE, happLE, happLE, ← RingHom.comp_apply, ← CommRingCat.hom_comp,
      Scheme.Hom.appLE_comp_appLE]
    have key : ∀ (u u' : 𝒦.Idx n) (huu : u = u') (e : 𝒲.inter s ≤ (g ≫ h) ⁻¹ᵁ 𝒦.inter u)
        (e' : 𝒲.inter s ≤ (g ≫ h) ⁻¹ᵁ 𝒦.inter u'),
        ((g ≫ h).appLE (𝒦.inter u) (𝒲.inter s) e).hom (z u) = ((g ≫ h).appLE (𝒦.inter u') (𝒲.inter
          s) e').hom (z u') := by
      intro u u' huu e e'
      subst huu
      rfl
    exact key _ _ hidx _ _
  · rw [unitPullback_apply_of_not_injective _ _ _ _ _ _ _ _ hinj]
    by_cases hinj₁ : Function.Injective (mu ∘ s.1)
    · have hinj₂ : ¬ Function.Injective (lam ∘ (𝒲.sortIdx 𝒱 mu s hinj₁).1) := by
        intro h2
        apply hinj
        rw [Scheme.OrderedAffineCover.sortIdx_val, ← Function.comp_assoc] at h2
        exact (Function.Injective.of_comp_iff' _ (Tuple.sort (mu ∘ s.1)).bijective).mp h2
      have h0 : OModulePresheaf.unitPullback (πX := πY) h 𝒱 𝒦 lam hlam n z (𝒲.sortIdx 𝒱 mu s hinj₁)
        =
          (0 : Γ(Y, 𝒱.inter (𝒲.sortIdx 𝒱 mu s hinj₁))) :=
        unitPullback_apply_of_not_injective _ _ _ _ _ _ _ _ hinj₂
      rw [unitPullback_apply_of_injective _ _ _ _ _ _ _ _ hinj₁, h0, map_zero, map_zero, smul_zero]
      rfl
    · rw [unitPullback_apply_of_not_injective _ _ _ _ _ _ _ _ hinj₁]

end FHSOL

theorem _root_.AlgebraicGeometry.OModulePresheaf.unitPullback_unitPullback_sub_mem_of_d_eq_zero
    {R R' R'' : Type u} [CommRing R] [CommRing R'] [CommRing R''] {X Y Z : Scheme.{u}}
    (πX : X ⟶ Spec (CommRingCat.of R'')) (πY : Y ⟶ Spec (CommRingCat.of R')) (πZ : Z ⟶ Spec
      (CommRingCat.of R))
    (h : X ⟶ Y) (h' : Y ⟶ Z) (h'' : X ⟶ Z) (hh : h'' = h ≫ h')
    (𝒲 : X.OrderedAffineCover) (𝒦 : Y.OrderedAffineCover) (𝒦' : Z.OrderedAffineCover)
    (lam : 𝒲.ι → 𝒦.ι) (lam' : 𝒦.ι → 𝒦'.ι) (lam'' : 𝒲.ι → 𝒦'.ι) (hlc : lam'' = lam' ∘ lam)
    (hlam : ∀ w, 𝒲.U w ≤ h ⁻¹ᵁ 𝒦.U (lam w)) (hlam' : ∀ i, 𝒦.U i ≤ h' ⁻¹ᵁ 𝒦'.U (lam' i))
    (hlam'' : ∀ w, 𝒲.U w ≤ h'' ⁻¹ᵁ 𝒦'.U (lam'' w))
    (n : ℕ) (z : (OModulePresheaf.unit πZ).cochain 𝒦' n) (hz : (OModulePresheaf.unit πZ).d 𝒦' n z =
      0) :
    OModulePresheaf.unitPullback (πX := πX) h 𝒲 𝒦 lam hlam n (OModulePresheaf.unitPullback (πX :=
      πY) h' 𝒦 𝒦' lam' hlam' n z) -
        OModulePresheaf.unitPullback (πX := πX) h'' 𝒲 𝒦' lam'' hlam'' n z
      ∈ (show Submodule R'' ((OModulePresheaf.unit πX).cochain 𝒲 n) from
          match n with
          | 0 => ⊥
          | m + 1 => LinearMap.range ((OModulePresheaf.unit πX).d 𝒲 m)) := by
  subst hh hlc
  rw [FHSOL.comp_eq πX πY πZ h h' 𝒲 𝒦 𝒦' lam lam' hlam hlam' hlam'' n z, sub_self]
  exact Submodule.zero_mem _
end OModulePresheaf_unitPullback_unitPullback_sub_mem_of_d_eq_zero
end AlgebraicCurves.Cohomology.Sheaves.Proofs
end ProofImplementation
