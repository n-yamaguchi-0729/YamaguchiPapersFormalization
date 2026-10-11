/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_basis_one.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Geometry.Picard.Functor

/-!
# Local one-element bases of invertible module sheaves

An invertible module has a local generator whose restrictions form one-element
bases of the section modules on smaller opens.
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Sheaves.Proofs.Scheme_Modules_IsInvertible_exists_basis_one

universe u

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry
open _root_.Opposite
open _root_.TopologicalSpace

namespace AlgebraicGeometry
open _root_.AlgebraicGeometry
namespace Scheme
open _root_.AlgebraicGeometry.Scheme
namespace Modules
open _root_.AlgebraicGeometry.Scheme.Modules
open _root_.AlgebraicGeometry.Scheme.Modules
open _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry

variable {X : Scheme.{u}}

section helpers

lemma map_eq_map' {M : X.Modules} {W₁ W₂ : X.Opens} (i j : W₁ ⟶ W₂) (m : Γ(M, W₂)) :
    M.presheaf.map i.op m = M.presheaf.map j.op m := by
  rw [Subsingleton.elim i j]

lemma map_map_of_eq {M : X.Modules} {W₁ W₂ : X.Opens} (h : W₁ = W₂) (m : Γ(M, W₂)) :
    M.presheaf.map (homOfLE h.ge).op (M.presheaf.map (homOfLE h.le).op m) = m := by
  subst h
  rw [← CategoryTheory.comp_apply, ← Functor.map_comp]
  have : ((homOfLE (le_refl W₁)).op ≫ (homOfLE (le_refl W₁)).op) = 𝟙 _ := Subsingleton.elim _ _
  rw [this, CategoryTheory.Functor.map_id]
  rfl

lemma ringMap_ringMap_of_eq {W₁ W₂ : X.Opens} (h : W₁ = W₂) (a : Γ(X, W₂)) :
    X.presheaf.map (homOfLE h.ge).op (X.presheaf.map (homOfLE h.le).op a) = a := by
  subst h
  rw [← CategoryTheory.comp_apply, ← Functor.map_comp]
  have : ((homOfLE (le_refl W₁)).op ≫ (homOfLE (le_refl W₁)).op) = 𝟙 _ := Subsingleton.elim _ _
  rw [this, CategoryTheory.Functor.map_id]
  rfl

lemma image_preimage_eq_of_le {V W : X.Opens} (hW : W ≤ V) : V.ι ''ᵁ (V.ι ⁻¹ᵁ W) = W := by
  rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι, inf_eq_right.2 hW]

lemma restrictFunctor_obj_presheaf_map (M : X.Modules) (V : X.Opens) {W₁ W₂ : (V :
  Scheme.{u}).Opens}
    (i : W₁ ⟶ W₂) (m : Γ((restrictFunctor V.ι).obj M, W₂)) :
    ((restrictFunctor V.ι).obj M).presheaf.map i.op m =
      M.presheaf.map (homOfLE (V.ι.image_mono i.le)).op (m : Γ(M, V.ι ''ᵁ W₂)) := by
  rw [Scheme.Modules.restrict_map]
  exact map_eq_map' _ _ _

end helpers

namespace IsInvertible
open _root_.AlgebraicGeometry.Scheme.Modules.IsInvertible
end IsInvertible
namespace IsInvertible
open scoped _root_.AlgebraicGeometry.Scheme.Modules.IsInvertible in
private theorem _root_.AlgebraicGeometry.Scheme.Modules.IsInvertible.exists_basis_one_aux {L :
    X.Modules} (hL : IsInvertible L) (x : X) :
    ∃ (V : X.Opens), x ∈ V ∧ ∃ u : Γ(L, V), ∀ (W : X.Opens) (hW : W ≤ V),
      ∃ b : Module.Basis (Fin 1) Γ(X, W) Γ(L, W), b 0 = L.presheaf.map (homOfLE hW).op u := by
  obtain ⟨V, hxV, ⟨e⟩⟩ := hL.exists_trivialization x
  let t : (restrictFunctor V.ι).obj L ≅ SheafOfModules.unit (V : Scheme.{u}).ringCatSheaf :=
    (restrictFunctorIsoPullback V.ι).app L ≪≫ e
  have hV : V.ι ''ᵁ ⊤ = V := V.ι_image_top
  let one : ∀ (W' : (V : Scheme.{u}).Opens),
      Γ((SheafOfModules.unit (V : Scheme.{u}).ringCatSheaf : (V : Scheme.{u}).Modules), W') :=
    fun W' => (1 : ((V : Scheme.{u}).presheaf.obj (op W')))
  let u₀ : Γ(L, V.ι ''ᵁ ⊤) := (t.inv.app ⊤ (one ⊤) : Γ(L, V.ι ''ᵁ ⊤))
  refine ⟨V, hxV, L.presheaf.map (homOfLE hV.ge).op u₀, fun W hW => ?_⟩
  let W' : (V : Scheme.{u}).Opens := V.ι ⁻¹ᵁ W
  have hW' : V.ι ''ᵁ W' = W := image_preimage_eq_of_le hW
  let ρ : Γ(L, W) → Γ(L, V.ι ''ᵁ W') := fun m => L.presheaf.map (homOfLE hW'.le).op m
  let σ : Γ(L, V.ι ''ᵁ W') → Γ(L, W) := fun m => L.presheaf.map (homOfLE hW'.ge).op m
  let ρR : Γ(X, W) → Γ(X, V.ι ''ᵁ W') := fun a => X.presheaf.map (homOfLE hW'.le).op a
  let σR : Γ(X, V.ι ''ᵁ W') → Γ(X, W) := fun a => X.presheaf.map (homOfLE hW'.ge).op a
  have hσρ : ∀ m, σ (ρ m) = m := fun m => map_map_of_eq hW' m
  have hσρR : ∀ a, σR (ρR a) = a := fun a => ringMap_ringMap_of_eq hW' a
  have hρ_smul : ∀ (a : Γ(X, W)) (m : Γ(L, W)), ρ (a • m) = ρR a • ρ m :=
    fun a m => Modules.map_smul L _ a m
  have hσ_smul : ∀ (a : Γ(X, V.ι ''ᵁ W')) (m : Γ(L, V.ι ''ᵁ W')), σ (a • m) = σR a • σ m :=
    fun a m => Modules.map_smul L _ a m
  have hρ0 : ρ 0 = 0 := map_zero (ConcreteCategory.hom (L.presheaf.map (homOfLE hW'.le).op))
  have hσR0 : σR 0 = 0 := map_zero (ConcreteCategory.hom (X.presheaf.map (homOfLE hW'.ge).op))
  have hρsum : ∀ (f : Fin 1 → Γ(L, W)), ρ (∑ j, f j) = ∑ j, ρ (f j) :=
    fun f => map_sum (ConcreteCategory.hom (L.presheaf.map (homOfLE hW'.le).op)) _ _
  have hσsum : ∀ (f : Fin 1 → Γ(L, V.ι ''ᵁ W')), σ (∑ j, f j) = ∑ j, σ (f j) :=
    fun f => map_sum (ConcreteCategory.hom (L.presheaf.map (homOfLE hW'.ge).op)) _ _
  have key : ρ (L.presheaf.map (homOfLE hW).op (L.presheaf.map (homOfLE hV.ge).op u₀)) =
      (t.inv.app W' (one W') : Γ(L, V.ι ''ᵁ W')) := by
    have h1 : ρ (L.presheaf.map (homOfLE hW).op (L.presheaf.map (homOfLE hV.ge).op u₀)) =
        L.presheaf.map (homOfLE (V.ι.image_mono (le_top : W' ≤ ⊤))).op u₀ := by
      change L.presheaf.map _ (L.presheaf.map _ (L.presheaf.map _ u₀)) = _
      rw [← CategoryTheory.comp_apply, ← CategoryTheory.comp_apply, ← Functor.map_comp, ←
          Functor.map_comp]
      exact map_eq_map' _ _ _
    rw [h1]
    have h2 := congr($(t.inv.mapPresheaf.naturality (homOfLE (le_top : W' ≤ ⊤)).op) (one ⊤))
    simp only [CategoryTheory.comp_apply] at h2
    have h3 : (Scheme.Modules.presheaf (SheafOfModules.unit (V : Scheme.{u}).ringCatSheaf)).map
        (homOfLE (le_top : W' ≤ ⊤)).op (one ⊤) = one W' := by
      change (V : Scheme.{u}).presheaf.map (homOfLE (le_top : W' ≤ ⊤)).op 1 = 1
      exact map_one _
    rw [h3] at h2
    erw [h2]
    exact (restrictFunctor_obj_presheaf_map L V (homOfLE (le_top : W' ≤ ⊤)) _).symm
  let A : Type u := Γ((V : Scheme.{u}), W')
  let N : Type u := Γ((restrictFunctor V.ι).obj L, W')
  have ht₁ : ∀ m : N, (t.inv.app W') (t.hom.app W' m) = m := fun m => by
    erw [← CategoryTheory.comp_apply, ← Scheme.Modules.Hom.comp_app, t.hom_inv_id,
        Scheme.Modules.Hom.id_app]
    rfl
  have ht₂ : ∀ v : Γ((SheafOfModules.unit (V : Scheme.{u}).ringCatSheaf : (V : Scheme.{u}).Modules),
      W'),
      (t.hom.app W') (t.inv.app W' v) = v := fun v => by
    erw [← CategoryTheory.comp_apply, ← Scheme.Modules.Hom.comp_app, t.inv_hom_id,
        Scheme.Modules.Hom.id_app]
    rfl
  let tW : N ≃ₗ[A] A :=
    { toFun := fun m => (t.hom.app W' m : A)
      invFun := fun v => (t.inv.app W' v : N)
      map_add' := fun m m' => (t.hom.app W').hom.map_add m m'
      map_smul' := fun a m => by
        rw [RingHom.id_apply]
        exact Hom.app_smul t.hom a m
      left_inv := ht₁
      right_inv := ht₂ }
  let b' : Module.Basis (Fin 1) A N := (Module.Basis.singleton (Fin 1) A).map tW.symm
  have hb' : b' 0 = (t.inv.app W' (one W') : N) := by
    simp only [b', Module.Basis.map_apply, Module.Basis.singleton_apply]
    rfl
  have hXN : ∀ (a : Γ(X, V.ι ''ᵁ W')) (m : Γ(L, V.ι ''ᵁ W')), a • m = @HSMul.hSMul A N N _ a m := by
    intro a m
    change _ = (((V.ι.appIso W').inv a : Γ(X, V.ι ''ᵁ W')) • m : Γ(L, V.ι ''ᵁ W'))
    simp [Scheme.Opens.ι_appIso]; rfl
  let v : Fin 1 → Γ(L, W) := fun _ => L.presheaf.map (homOfLE hW).op (L.presheaf.map (homOfLE
      hV.ge).op u₀)
  have hρv : ∀ i, ρ (v i) = (b' i : Γ(L, V.ι ''ᵁ W')) := fun i => by
    rw [Subsingleton.elim i 0]
    exact key.trans hb'.symm
  have hli : LinearIndependent Γ(X, W) v := by
    rw [Fintype.linearIndependent_iff]
    intro c hc i
    have h0 : ∑ j, @HSMul.hSMul A N N _ (ρR (c j)) (b' j) = (0 : N) := by
      have h := congrArg ρ hc
      rw [hρ0, hρsum] at h
      erw [← h]
      exact Finset.sum_congr rfl (fun j _ =>
        ((hρ_smul (c j) (v j)).trans
          ((hXN (ρR (c j)) (ρ (v j))).trans
            (congrArg (fun z : N => (id (ρR (c j)) : A) • z) (hρv j)))).symm)
    have h1 : ρR (c i) = 0 :=
      (Fintype.linearIndependent_iff.mp b'.linearIndependent) (fun j => ρR (c j)) h0 i
    rw [← hσρR (c i)]
    change σR (ρR (c i)) = 0
    rw [h1, hσR0]
  have hsp : ⊤ ≤ Submodule.span (X.presheaf.obj (op W)) (Set.range v) := by
    rintro m -
    set r := b'.repr (ρ m) with hr
    have hm : ρ m = ∑ j, @HSMul.hSMul A N N _ (r j) (b' j) := (b'.sum_repr (ρ m)).symm
    have hm' : m = ∑ j, σR (r j) • v j := by
      conv_lhs => rw [← hσρ m]
      erw [hm, hσsum]
      exact Finset.sum_congr rfl (fun j _ => by erw [← hXN, hσ_smul, ← hρv, hσρ])
    rw [hm']
    exact Submodule.sum_mem _ (fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩))
  exact ⟨Module.Basis.mk hli hsp, by rw [Module.Basis.mk_apply]⟩

end IsInvertible
open _root_.AlgebraicGeometry.Scheme.Modules
end AlgebraicGeometry.Scheme.Modules

theorem _root_.AlgebraicGeometry.Scheme.Modules.IsInvertible.exists_basis_one {X :
  AlgebraicGeometry.Scheme.{u}} {L : X.Modules}
    (hL : AlgebraicGeometry.Scheme.Modules.IsInvertible L) (x : X) :
    ∃ (V : X.Opens), x ∈ V ∧ ∃ u : Γ(L, V), ∀ (W : X.Opens) (hW : W ≤ V),
      ∃ b : Module.Basis (Fin 1) Γ(X, W) Γ(L, W), b 0 = L.presheaf.map (homOfLE hW).op u :=
  hL.exists_basis_one_aux x
end AlgebraicCurves.Geometry.Sheaves.Proofs.Scheme_Modules_IsInvertible_exists_basis_one
end ProofImplementation
