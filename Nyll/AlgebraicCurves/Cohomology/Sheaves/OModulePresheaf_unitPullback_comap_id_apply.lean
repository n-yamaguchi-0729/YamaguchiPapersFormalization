/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_OModulePresheaf_unitPullback_comap_id_apply.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.GroupTheory.Perm.Sign
import Nyll.SchemeTheory.Cohomology.Cech.OrderedAffineCoverCech
import Nyll.AlgebraicCurves.Geometry.Schemes.OrderedAffineCoverComap
import Nyll.AlgebraicCurves.Cohomology.Sheaves.OrderedAffineCoverCochainPullback

/-!
# OModule Presheaf unit Pullback comap id apply
-/

section ProofImplementation

namespace AlgebraicCurves.Cohomology.Sheaves.Proofs.OModulePresheaf_unitPullback_comap_id_apply

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry

universe u

theorem _root_.AlgebraicGeometry.OModulePresheaf.unitPullback_comap_id_apply
    {R R' : Type u} [CommRing R] [CommRing R'] {X Y : Scheme.{u}}
    (πX : X ⟶ Spec (CommRingCat.of R')) (πY : Y ⟶ Spec (CommRingCat.of R))
    (h : X ⟶ Y) [IsAffineHom h] (𝒦 : Y.OrderedAffineCover)
    (hlam : ∀ w : (𝒦.comap h).ι, (𝒦.comap h).U w ≤ h ⁻¹ᵁ 𝒦.U w)
    (n : ℕ) (z : (OModulePresheaf.unit πY).cochain 𝒦 n) (s : (𝒦.comap h).Idx n) :
    OModulePresheaf.unitPullback (πX := πX) h (𝒦.comap h) 𝒦 (fun w => w) hlam n z s =
      (X.presheaf.map (homOfLE (𝒦.comap_inter_le h s)).op).hom ((h.app (𝒦.inter s)).hom (z s)) := by
  classical
  have hinj : Function.Injective ((fun w : (𝒦.comap h).ι => w) ∘ s.1) := s.2.injective
  have hgen : ∀ (f : Fin (n + 1) → 𝒦.ι), Monotone f → Tuple.sort f = Equiv.refl _ :=
    fun f hf => Tuple.sort_eq_refl_iff_monotone.mpr hf
  have hmono : Monotone (((fun w : (𝒦.comap h).ι => w) ∘ s.1 : Fin (n + 1) → 𝒦.ι)) := fun i j hij
    => s.2.monotone hij
  rw [OModulePresheaf.unitPullback_apply_of_injective (πX := πX) h (𝒦.comap h) 𝒦 (fun w => w) hlam
    n z s hinj]
  have hidx : (𝒦.comap h).sortIdx 𝒦 (fun w => w) s hinj = s := by
    apply Subtype.ext
    exact congrArg
      (fun e : Equiv.Perm (Fin (n + 1)) =>
        ((fun w : (𝒦.comap h).ι => (w : 𝒦.ι)) ∘ s.1) ∘ e)
      (hgen _ hmono)
  have key : ∀ (t : 𝒦.Idx n) (ht : t = s) (hle : (𝒦.comap h).inter s ≤ h ⁻¹ᵁ 𝒦.inter t) (σ :
    Equiv.Perm (Fin (n + 1))) (hσ : σ = Equiv.refl _),
      ((Equiv.Perm.sign σ : ℤˣ) : ℤ) • (X.presheaf.map (homOfLE hle).op).hom ((h.app (𝒦.inter
        t)).hom (z t)) =
        (X.presheaf.map (homOfLE (𝒦.comap_inter_le h s)).op).hom ((h.app (𝒦.inter s)).hom (z s)) :=
          by
    intro t ht hle σ hσ; subst ht; subst hσ
    rw [Equiv.Perm.sign_refl, Units.val_one, one_smul]
  exact key _ hidx _ _ (hgen _ hmono)
end AlgebraicCurves.Cohomology.Sheaves.Proofs.OModulePresheaf_unitPullback_comap_id_apply
end ProofImplementation
