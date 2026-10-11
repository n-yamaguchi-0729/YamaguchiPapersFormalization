/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_exists_app_eq_of_isCompact_of_isDirectLimit.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Lean.Elab.Command
import Mathlib.Tactic.Choose
import AlgebraicCurves.Foundations.Algebra.Mathlib_Algebra_IsDirectLimit
import SchemeTheory.Cohomology.Cech.TwoAffineOpenCover
import AlgebraicCurves.Geometry.Schemes.exists_algEquiv_sections_pullback_fst_preimage_tensor_of_isAffineOpen
import AlgebraicCurves.Foundations.Algebra.Algebra_TensorProduct_isDirectLimit_map_of_isDirectLimit
import AlgebraicCurves.Geometry.Schemes.Scheme_exists_app_eq_app_of_isCompact_of_isDirectLimit

/-!
# Scheme exists app eq of is Compact of is Direct Limit
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Schemes.Proofs.Scheme_exists_app_eq_of_isCompact_of_isDirectLimit

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite TensorProduct

universe u

noncomputable section

namespace LimitIsoFil

private def _root_.AlgebraicGeometry.Scheme.Hom.appInf {X Y : Scheme.{u}} (π : Y ⟶ X) (V W :
  X.Opens) :
    Γ(X, V ⊓ W) ⟶ Γ(Y, π ⁻¹ᵁ V ⊓ π ⁻¹ᵁ W) :=
  π.app (V ⊓ W)


open Lean Elab Command in
run_cmd
  let env ← getEnv
  let full := "AlgebraicGeometry.Scheme.Hom.appInf".toName
  let target := if env.contains full then some full else
    let prv := mkPrivateName env full
    if env.contains prv then some prv else none
  match target with
  | some target =>
      modifyEnv fun env => addAlias env
        ("AlgebraicCurves.Geometry.Schemes.Proofs." ++
          "Scheme_exists_app_eq_of_isCompact_of_isDirectLimit.AlgebraicGeometry.Scheme." ++
          "Hom.appInf").toName target
  | none => pure ()


open _root_.AlgebraicGeometry.Scheme.Modules


private theorem _root_.AlgebraicGeometry.Scheme.Hom.preimage_mono_inf {X Y : Scheme.{u}} (π : Y ⟶
  X) {W' V W : X.Opens}
    (h : W' ≤ V ⊓ W) : π ⁻¹ᵁ W' ≤ π ⁻¹ᵁ V ⊓ π ⁻¹ᵁ W := π.preimage_mono h


open Lean Elab Command in
run_cmd
  let env ← getEnv
  let full := "AlgebraicGeometry.Scheme.Hom.preimage_mono_inf".toName
  let target := if env.contains full then some full else
    let prv := mkPrivateName env full
    if env.contains prv then some prv else none
  match target with
  | some target =>
      modifyEnv fun env => addAlias env
        ("AlgebraicCurves.Geometry.Schemes.Proofs." ++
          "Scheme_exists_app_eq_of_isCompact_of_isDirectLimit.AlgebraicGeometry.Scheme." ++
          "Hom.preimage_mono_inf").toName target
  | none => pure ()

lemma appInf_res {X Y : Scheme.{u}} (π : Y ⟶ X) (V W W' : X.Opens) (h : W' ≤ V ⊓ W) (t : Γ(X, V ⊓
  W)) :
    Y.presheaf.map (homOfLE (π.preimage_mono_inf h)).op (π.appInf V W t) =
      π.app W' (X.presheaf.map (homOfLE h).op t) := by
  have e := congrArg (fun k => (ConcreteCategory.hom k) t) (π.naturality (homOfLE h).op)
  simp only [CategoryTheory.comp_apply] at e
  exact e.symm

lemma res_res {X : Scheme.{u}} {U V W : X.Opens} (h₁ : V ≤ U) (h₂ : W ≤ V) (s : Γ(X, U)) :
    X.presheaf.map (homOfLE h₂).op (X.presheaf.map (homOfLE h₁).op s) =
      X.presheaf.map (homOfLE (h₂.trans h₁)).op s := by
  rw [← CategoryTheory.comp_apply, ← Functor.map_comp]; rfl

lemma cocycle_res {X Y : Scheme.{u}} (π : Y ⟶ X) {V W W' : X.Opens} (h : W' ≤ V ⊓ W) (t₁ t₂ : Γ(X,
  V ⊓ W))
    (uV : Γ(Y, π ⁻¹ᵁ V)) (uW : Γ(Y, π ⁻¹ᵁ W))
    (hc : π.appInf V W t₁ * Y.presheaf.map (homOfLE (inf_le_left : π ⁻¹ᵁ V ⊓ π ⁻¹ᵁ W ≤ π ⁻¹ᵁ V)).op
      uV =
      Y.presheaf.map (homOfLE (inf_le_right : π ⁻¹ᵁ V ⊓ π ⁻¹ᵁ W ≤ π ⁻¹ᵁ W)).op uW * π.appInf V W
        t₂) :
    π.app W' (X.presheaf.map (homOfLE h).op t₁) *
        Y.presheaf.map (homOfLE (π.preimage_mono (h.trans inf_le_left))).op uV =
      Y.presheaf.map (homOfLE (π.preimage_mono (h.trans inf_le_right))).op uW *
        π.app W' (X.presheaf.map (homOfLE h).op t₂) := by
  have e := congrArg (Y.presheaf.map (homOfLE (π.preimage_mono_inf h)).op) hc
  rw [map_mul, map_mul, appInf_res, appInf_res, res_res, res_res] at e
  exact e

lemma map_swap {K : Type u} [CommRing K] {A A' B B' : Type u} [CommRing A] [CommRing A'] [CommRing
  B] [CommRing B']
    [Algebra K A] [Algebra K A'] [Algebra K B] [Algebra K B'] (ψ : A →ₐ[K] A') (ρ : B →ₐ[K] B') (x
      : A ⊗[K] B) :
    Algebra.TensorProduct.map ψ (AlgHom.id K B') (Algebra.TensorProduct.map (AlgHom.id K A) ρ x) =
      Algebra.TensorProduct.map (AlgHom.id K A') ρ (Algebra.TensorProduct.map ψ (AlgHom.id K B) x)
        := by
  rw [← AlgHom.comp_apply, ← Algebra.TensorProduct.map_comp, ← AlgHom.comp_apply, ←
    Algebra.TensorProduct.map_comp]
  simp only [AlgHom.comp_id, AlgHom.id_comp]

lemma map_one_tmul {K : Type u} [CommRing K] {A A' B : Type u} [CommRing A] [CommRing A'] [CommRing
  B]
    [Algebra K A] [Algebra K A'] [Algebra K B] (ψ : A →ₐ[K] A') (b : B) :
    Algebra.TensorProduct.map ψ (AlgHom.id K B) ((1 : A) ⊗ₜ[K] b) = (1 : A') ⊗ₜ[K] b := by
  rw [Algebra.TensorProduct.map_tmul, map_one]; rfl

lemma exists_ge₂ {J : Type u} [Preorder J] [Nonempty J] [IsDirected J (· ≤ ·)] {α β : Type*}
  [Finite α] [Finite β]
    (f : α → J) (g : β → J) : ∃ m : J, (∀ a, f a ≤ m) ∧ ∀ b, g b ≤ m := by
  classical
  have := Fintype.ofFinite α; have := Fintype.ofFinite β
  obtain ⟨m, hm⟩ := Finset.exists_le (Finset.univ.image f ∪ Finset.univ.image g)
  exact ⟨m, fun a => hm _ (Finset.mem_union_left _ (Finset.mem_image_of_mem f (Finset.mem_univ a))),
    fun b => hm _ (Finset.mem_union_right _ (Finset.mem_image_of_mem g (Finset.mem_univ b)))⟩

lemma nonempty_iso_pullback_of_fac {X Y Z : Scheme.{u}} (h : X ⟶ Y) (π : Y ⟶ Z) (p : X ⟶ Z) (hp : h
  ≫ π = p)
    (L₁ L₂ : Z.Modules)
    (e : Nonempty ((Scheme.Modules.pullback π).obj L₁ ≅ (Scheme.Modules.pullback π).obj L₂)) :
    Nonempty ((Scheme.Modules.pullback p).obj L₁ ≅ (Scheme.Modules.pullback p).obj L₂) := by
  obtain ⟨e⟩ := e
  exact ⟨((Scheme.Modules.pullbackComp h π).app L₁ ≪≫ (Scheme.Modules.pullbackCongr hp).app
    L₁).symm ≪≫
    (Scheme.Modules.pullback h).mapIso e ≪≫
    ((Scheme.Modules.pullbackComp h π).app L₂ ≪≫ (Scheme.Modules.pullbackCongr hp).app L₂)⟩

end LimitIsoFil

namespace LimitIsoFil

lemma res_injective_of_eq {Y : Scheme.{u}} {U U' : Y.Opens} (h : U' = U) :
    Function.Injective (Y.presheaf.map (homOfLE h.le).op) := by
  intro a b hab
  have e := congrArg (Y.presheaf.map (homOfLE h.ge).op) hab
  rw [res_res, res_res] at e
  have ha : Y.presheaf.map (homOfLE (h.ge.trans h.le)).op a = a := by
    have : homOfLE (h.ge.trans h.le) = 𝟙 U := rfl
    rw [this, op_id, Y.presheaf.map_id]; rfl
  have hb : Y.presheaf.map (homOfLE (h.ge.trans h.le)).op b = b := by
    have : homOfLE (h.ge.trans h.le) = 𝟙 U := rfl
    rw [this, op_id, Y.presheaf.map_id]; rfl
  rwa [ha, hb] at e

lemma appLE_app_of_comp_eq {Y Y' X : Scheme.{u}} (c : Y' ⟶ Y) (π : Y ⟶ X) (π' : Y' ⟶ X) (hc : c ≫ π
  = π')
    (U : X.Opens) (e : π' ⁻¹ᵁ U ≤ c ⁻¹ᵁ π ⁻¹ᵁ U) (a : Γ(X, U)) :
    c.appLE (π ⁻¹ᵁ U) (π' ⁻¹ᵁ U) e (π.app U a) = π'.app U a := by
  subst hc
  exact congrArg
    (fun f : Γ(X, U) ⟶ Γ(Y', (c ≫ π) ⁻¹ᵁ U) => f.hom a)
    ((Scheme.Hom.comp_appLE c π U ((c ≫ π) ⁻¹ᵁ U) le_rfl).symm.trans
      (Scheme.Hom.appLE_eq_app (c ≫ π)))

lemma appLE_appLE_of_comp_eq {Z Y Y' : Scheme.{u}} (c : Y' ⟶ Y) (s : Y ⟶ Z) (d : Y' ⟶ Z) (hc : c ≫
  s = d)
    (U : Z.Opens) (V : Y.Opens) (W : Y'.Opens) (e₁ : V ≤ s ⁻¹ᵁ U) (e₂ : W ≤ c ⁻¹ᵁ V) (e₃ : W ≤ d
      ⁻¹ᵁ U) (z : Γ(Z, U)) :
    c.appLE V W e₂ (s.appLE U V e₁ z) = d.appLE U W e₃ z := by
  subst hc
  rw [← CategoryTheory.comp_apply, Scheme.Hom.appLE_comp_appLE]

lemma nat_gamma (K : Type u) [CommRing K] {X : Scheme.{u}} (fX : X ⟶ Spec (CommRingCat.of K))
    (H H' : Type u) [CommRing H] [CommRing H'] [Algebra K H] [Algebra K H'] (ψ : H →ₐ[K] H')
    (c : Limits.pullback fX (Spec.map (CommRingCat.ofHom (algebraMap K H'))) ⟶
      Limits.pullback fX (Spec.map (CommRingCat.ofHom (algebraMap K H))))
    (hc₁ : c ≫ Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (algebraMap K H))) =
      Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (algebraMap K H'))))
    (hc₂ : c ≫ Limits.pullback.snd fX (Spec.map (CommRingCat.ofHom (algebraMap K H))) =
      Limits.pullback.snd fX (Spec.map (CommRingCat.ofHom (algebraMap K H'))) ≫ Spec.map
        (CommRingCat.ofHom ψ.toRingHom)) :
    letI instK : ∀ V : X.Opens, Algebra K Γ(X, V) := fun V =>
      Scheme.TwoAffineOpenCover.algebraOfHom fX V
    letI instH : ∀ W : (Limits.pullback fX (Spec.map (CommRingCat.ofHom (algebraMap K H)))).Opens,
        Algebra K Γ(Limits.pullback fX (Spec.map (CommRingCat.ofHom (algebraMap K H))), W) := fun W
          =>
      Scheme.TwoAffineOpenCover.algebraOfHom (Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom
        (algebraMap K H))) ≫ fX) W
    letI instH' : ∀ W : (Limits.pullback fX (Spec.map (CommRingCat.ofHom (algebraMap K H')))).Opens,
        Algebra K Γ(Limits.pullback fX (Spec.map (CommRingCat.ofHom (algebraMap K H'))), W) := fun
          W =>
      Scheme.TwoAffineOpenCover.algebraOfHom (Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom
        (algebraMap K H'))) ≫ fX) W
    ∀ (ε : ∀ (V : X.Opens) (_ : IsAffineOpen V),
        Γ(Limits.pullback fX (Spec.map (CommRingCat.ofHom (algebraMap K H))),
            (Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (algebraMap K H)))) ⁻¹ᵁ V) ≃ₐ[K]
              Γ(X, V) ⊗[K] H)
      (_ : ∀ (V : X.Opens) (hV : IsAffineOpen V) (a : Γ(X, V)),
        ε V hV (((Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (algebraMap K H)))).app
          V).hom a) = a ⊗ₜ[K] (1 : H))
      (_ : ∀ (V : X.Opens) (hV : IsAffineOpen V) (h : H),
        ε V hV (((Limits.pullback.snd fX (Spec.map (CommRingCat.ofHom (algebraMap K H)))).appLE ⊤
            ((Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (algebraMap K H)))) ⁻¹ᵁ V)
              le_top).hom
          ((Scheme.ΓSpecIso (CommRingCat.of H)).inv.hom h)) = (1 : Γ(X, V)) ⊗ₜ[K] h)
      (ε' : ∀ (V : X.Opens) (_ : IsAffineOpen V),
        Γ(Limits.pullback fX (Spec.map (CommRingCat.ofHom (algebraMap K H'))),
            (Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (algebraMap K H')))) ⁻¹ᵁ V) ≃ₐ[K]
              Γ(X, V) ⊗[K] H')
      (_ : ∀ (V : X.Opens) (hV : IsAffineOpen V) (a : Γ(X, V)),
        ε' V hV (((Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (algebraMap K H')))).app
          V).hom a) = a ⊗ₜ[K] (1 : H'))
      (_ : ∀ (V : X.Opens) (hV : IsAffineOpen V) (h : H'),
        ε' V hV (((Limits.pullback.snd fX (Spec.map (CommRingCat.ofHom (algebraMap K H')))).appLE ⊤
            ((Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (algebraMap K H')))) ⁻¹ᵁ V)
              le_top).hom
          ((Scheme.ΓSpecIso (CommRingCat.of H')).inv.hom h)) = (1 : Γ(X, V)) ⊗ₜ[K] h)
      (V : X.Opens) (hV : IsAffineOpen V)
      (s : Γ(Limits.pullback fX (Spec.map (CommRingCat.ofHom (algebraMap K H))),
            (Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (algebraMap K H)))) ⁻¹ᵁ V)),
      Algebra.TensorProduct.comm K Γ(X, V) H' (ε' V hV
        (c.appLE ((Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (algebraMap K H)))) ⁻¹ᵁ V)
          ((Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (algebraMap K H')))) ⁻¹ᵁ V)
          (by rw [← hc₁]; exact le_rfl) s)) =
      Algebra.TensorProduct.map ψ (AlgHom.id K Γ(X, V)) (Algebra.TensorProduct.comm K Γ(X, V) H (ε
        V hV s)) := by
  let instK : ∀ V : X.Opens, Algebra K Γ(X, V) := fun V => Scheme.TwoAffineOpenCover.algebraOfHom
    fX V
  let instH : ∀ W : (Limits.pullback fX (Spec.map (CommRingCat.ofHom (algebraMap K H)))).Opens,
      Algebra K Γ(Limits.pullback fX (Spec.map (CommRingCat.ofHom (algebraMap K H))), W) := fun W =>
    Scheme.TwoAffineOpenCover.algebraOfHom (Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom
      (algebraMap K H))) ≫ fX) W
  let instH' : ∀ W : (Limits.pullback fX (Spec.map (CommRingCat.ofHom (algebraMap K H')))).Opens,
      Algebra K Γ(Limits.pullback fX (Spec.map (CommRingCat.ofHom (algebraMap K H'))), W) := fun W
        =>
    Scheme.TwoAffineOpenCover.algebraOfHom (Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom
      (algebraMap K H'))) ≫ fX) W
  intro ε hε1 hε1' ε' hε'1 hε'1' V hV s
  obtain ⟨x, rfl⟩ : ∃ x, s = (ε V hV).symm x := ⟨ε V hV s, ((ε V hV).symm_apply_apply s).symm⟩
  rw [AlgEquiv.apply_symm_apply]
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a h =>
    have split : a ⊗ₜ[K] h = (a ⊗ₜ[K] (1 : H)) * ((1 : Γ(X, V)) ⊗ₜ[K] h) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rw [split, map_mul, map_mul, map_mul, map_mul, map_mul, map_mul]
    congr 1
    · have e1 : (ε V hV).symm (a ⊗ₜ[K] (1 : H)) =
          ((Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (algebraMap K H)))).app V).hom a :=
            by
        rw [← hε1 V hV a, AlgEquiv.symm_apply_apply]
      rw [e1]
      erw [appLE_app_of_comp_eq c _ _ hc₁ V _ a]
      erw [hε'1 V hV a]
      rw [Algebra.TensorProduct.comm_tmul, Algebra.TensorProduct.comm_tmul,
        Algebra.TensorProduct.map_tmul,
        map_one]
      rfl
    · have e2 : (ε V hV).symm ((1 : Γ(X, V)) ⊗ₜ[K] h) =
          ((Limits.pullback.snd fX (Spec.map (CommRingCat.ofHom (algebraMap K H)))).appLE ⊤
            ((Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (algebraMap K H)))) ⁻¹ᵁ V)
              le_top).hom
          ((Scheme.ΓSpecIso (CommRingCat.of H)).inv.hom h) := by
        rw [← hε1' V hV h, AlgEquiv.symm_apply_apply]
      rw [e2]
      have e3 : c.appLE ((Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (algebraMap K H))))
        ⁻¹ᵁ V)
          ((Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (algebraMap K H')))) ⁻¹ᵁ V)
            (by rw [← hc₁]; exact le_rfl)
          (((Limits.pullback.snd fX (Spec.map (CommRingCat.ofHom (algebraMap K H)))).appLE ⊤
            ((Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (algebraMap K H)))) ⁻¹ᵁ V)
              le_top).hom
            ((Scheme.ΓSpecIso (CommRingCat.of H)).inv.hom h)) =
          ((Limits.pullback.snd fX (Spec.map (CommRingCat.ofHom (algebraMap K H')))).appLE ⊤
            ((Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (algebraMap K H')))) ⁻¹ᵁ V)
              le_top).hom
            ((Scheme.ΓSpecIso (CommRingCat.of H')).inv.hom (ψ h)) := by
        erw [appLE_appLE_of_comp_eq c _ _ hc₂ ⊤ _ _ le_top _ le_top]
        have hcomp := congrArg
          (fun f : Γ(Spec (CommRingCat.of H), ⊤) ⟶
              Γ(Limits.pullback fX (Spec.map (CommRingCat.ofHom (algebraMap K H'))),
                (Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (algebraMap K H')))) ⁻¹ᵁ V) =>
            f.hom ((Scheme.ΓSpecIso (CommRingCat.of H)).inv.hom h))
          (Scheme.Hom.comp_appLE
            (Limits.pullback.snd fX (Spec.map (CommRingCat.ofHom (algebraMap K H'))))
            (Spec.map (CommRingCat.ofHom ψ.toRingHom)) ⊤
            ((Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (algebraMap K H')))) ⁻¹ᵁ V)
              le_top)
        have nat : (Scheme.ΓSpecIso (CommRingCat.of H')).inv.hom (ψ h) =
            (Spec.map (CommRingCat.ofHom ψ.toRingHom)).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of
              H)).inv.hom h) :=
          congrArg (fun k => (ConcreteCategory.hom k) h) (Scheme.ΓSpecIso_inv_naturality
            (CommRingCat.ofHom ψ.toRingHom))
        exact hcomp.trans (congrArg
          (fun a : Γ(Spec (CommRingCat.of H'), ⊤) =>
            ((Limits.pullback.snd fX (Spec.map (CommRingCat.ofHom (algebraMap K H')))).appLE ⊤
              ((Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (algebraMap K H')))) ⁻¹ᵁ V)
              le_top).hom a) nat.symm)
      erw [e3, hε'1' V hV (ψ h)]
      rw [Algebra.TensorProduct.comm_tmul, Algebra.TensorProduct.comm_tmul,
        Algebra.TensorProduct.map_tmul]
      rfl

end LimitIsoFil

open LimitIsoFil in
theorem _root_.AlgebraicGeometry.Scheme.exists_app_eq_of_isCompact_of_isDirectLimit
    {ι : Type u} [Preorder ι] [Nonempty ι] [IsDirected ι (· ≤ ·)]
    {G : ι → Type u} [∀ i, CommRing (G i)] (φ : ∀ i j : ι, i ≤ j → G i →+* G j)
    [DirectedSystem G fun i j h => ⇑(φ i j h)]
    {R : Type u} [CommRing R] (g : ∀ i, G i →+* R)
    (hR : IsDirectLimit (fun i j h => ⇑(φ i j h)) fun i => ⇑(g i))
    (i : ι) {X : Scheme.{u}} (fX : X ⟶ Spec (CommRingCat.of (G i))) [QuasiCompact fX]
      [QuasiSeparated fX]
    (W : X.Opens) (hW : IsCompact (W : Set X))
    (s : Γ(Limits.pullback fX (Spec.map (CommRingCat.ofHom (g i))), (Limits.pullback.fst fX
      (Spec.map (CommRingCat.ofHom (g i)))) ⁻¹ᵁ W)) :
    ∃ (j : ι) (hij : i ≤ j) (t : Γ(Limits.pullback fX (Spec.map (CommRingCat.ofHom (φ i j hij))),
      (Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (φ i j hij)))) ⁻¹ᵁ W)),
      ∀ (c : Limits.pullback fX (Spec.map (CommRingCat.ofHom (g i))) ⟶ Limits.pullback fX (Spec.map
        (CommRingCat.ofHom (φ i j hij)))),
        c ≫ Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (φ i j hij))) = Limits.pullback.fst
          fX (Spec.map (CommRingCat.ofHom (g i))) →
        c ≫ Limits.pullback.snd fX (Spec.map (CommRingCat.ofHom (φ i j hij))) = Limits.pullback.snd
          fX (Spec.map (CommRingCat.ofHom (g i))) ≫ Spec.map (CommRingCat.ofHom (g j)) →
        ∀ e : (Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (g i)))) ⁻¹ᵁ W = c ⁻¹ᵁ
          ((Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (φ i j hij)))) ⁻¹ᵁ W),
          (Limits.pullback fX (Spec.map (CommRingCat.ofHom (g i)))).presheaf.map (eqToHom e).op
            (c.app ((Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (φ i j hij)))) ⁻¹ᵁ W) t) =
            s := by
  classical
  have : CompactSpace ↥(Spec (CommRingCat.of (G i))) := (inferInstance : CompactSpace
    (PrimeSpectrum (G i)))
  have : CompactSpace ↥X := QuasiCompact.compactSpace_of_compactSpace fX
  have : QuasiSeparatedSpace ↥X := (quasiSeparated_iff_quasiSeparatedSpace fX).mp inferInstance
  let J : Type u := {j : ι // i ≤ j}
  have : Nonempty J := ⟨⟨i, le_rfl⟩⟩
  have : IsDirected J (· ≤ ·) := ⟨fun a b => by
    obtain ⟨c, hac, hbc⟩ := directed_of (· ≤ ·) a.1 b.1
    exact ⟨⟨c, a.2.trans hac⟩, hac, hbc⟩⟩
  let algK : ∀ j : J, Algebra (G i) (G j.1) := fun j => (φ i j.1 j.2).toAlgebra
  let algR : Algebra (G i) R := (g i).toAlgebra
  let algGR : ∀ j : J, Algebra (G j.1) R := fun j => (g j.1).toAlgebra
  have hST : ∀ j : J, IsScalarTower (G i) (G j.1) R := fun j =>
    IsScalarTower.of_algebraMap_eq (fun r => (IsDirectLimit.compatibility (f := fun i j h => ⇑(φ i
      j h))
      (g := fun i => ⇑(g i)) i j.1 j.2 r).symm)
  let f' : ∀ j k : J, j ≤ k → G j.1 →ₐ[G i] G k.1 := fun j k h =>
    { toRingHom := φ j.1 k.1 h
      commutes' := fun r => DirectedSystem.map_map (f := fun i j h => ⇑(φ i j h)) j.2 h r }
  have hDS : DirectedSystem (fun j : J => G j.1) (fun j k h => ⇑(f' j k h)) :=
    ⟨fun j x => DirectedSystem.map_self (f := fun i j h => ⇑(φ i j h)) x,
     fun k j l hlj hjk x => DirectedSystem.map_map (f := fun i j h => ⇑(φ i j h)) hlj hjk x⟩
  have hR' : IsDirectLimit (fun j k h => ⇑(f' j k h)) (fun j : J => ⇑(algebraMap (G j.1) R)) := by
    refine ⟨fun x => ?_, fun j k x y hxy => ?_, fun j k h x => ?_⟩
    · obtain ⟨i', y, hy⟩ := hR.surj x
      obtain ⟨k, hik, hi'k⟩ := directed_of (· ≤ ·) i i'
      exact ⟨⟨k, hik⟩, φ i' k hi'k y, by rw [← hy]; exact hR.compatibility i' k hi'k y⟩
    · obtain ⟨l, hjl, hkl, e⟩ := hR.inj j.1 k.1 x y hxy
      exact ⟨⟨l, j.2.trans hjl⟩, hjl, hkl, e⟩
    · exact hR.compatibility j.1 k.1 h x
  let instK : ∀ V : X.Opens, Algebra (G i) Γ(X, V) := fun V =>
    Scheme.TwoAffineOpenCover.algebraOfHom fX V
  let instKR : ∀ W : (Limits.pullback fX (Spec.map (CommRingCat.ofHom (algebraMap (G i) R)))).Opens,
      Algebra (G i) Γ(Limits.pullback fX (Spec.map (CommRingCat.ofHom (algebraMap (G i) R))), W) :=
        fun W =>
    Scheme.TwoAffineOpenCover.algebraOfHom
      (Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (algebraMap (G i) R))) ≫ fX) W
  obtain ⟨εR, hεaff, hε1, hε1', hε2⟩ :=
    AlgebraicGeometry.exists_algEquiv_sections_pullback_fst_preimage_tensor_of_isAffineOpen (G i)
      fX R
  have hDL : ∀ V : X.Opens, ∃ _ : DirectedSystem (fun j : J => G j.1 ⊗[G i] Γ(X, V))
      (fun j k h => ⇑(Algebra.TensorProduct.map (f' j k h) (AlgHom.id (G i) Γ(X, V)))),
      IsDirectLimit (fun j k h => ⇑(Algebra.TensorProduct.map (f' j k h) (AlgHom.id (G i) Γ(X, V))))
        (fun j : J => ⇑(Algebra.TensorProduct.map (IsScalarTower.toAlgHom (G i) (G j.1) R)
          (AlgHom.id (G i) Γ(X, V)))) := fun V =>
    Algebra.TensorProduct.isDirectLimit_map_of_isDirectLimit (G i) (fun j : J => G j.1) f' R hR'
      Γ(X, V)
  choose hDSv hDLv using hDL
  let γR : ∀ (V : X.Opens) (hV : IsAffineOpen V),
      Γ(Limits.pullback fX (Spec.map (CommRingCat.ofHom (algebraMap (G i) R))),
        (Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (algebraMap (G i) R)))) ⁻¹ᵁ V) ≃ₐ[G i]
      R ⊗[G i] Γ(X, V) := fun V hV => (εR V hV).trans (Algebra.TensorProduct.comm (G i) Γ(X, V) R)
  have γR1 : ∀ (V : X.Opens) (hV : IsAffineOpen V) (s : Γ(X, V)),
      γR V hV ((Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (algebraMap (G i) R)))).app V
        s) =
        (1 : R) ⊗ₜ[G i] s := by
    intro V hV s
    change Algebra.TensorProduct.comm (G i) _ R (εR V hV _) = _
    erw [hε1 V hV s]
    exact Algebra.TensorProduct.comm_tmul _ _ _
  have γR2 : ∀ (V V' : X.Opens) (hV : IsAffineOpen V) (hV' : IsAffineOpen V') (hle : V' ≤ V)
      (s : Γ(Limits.pullback fX (Spec.map (CommRingCat.ofHom (algebraMap (G i) R))),
        (Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (algebraMap (G i) R)))) ⁻¹ᵁ V)),
      Algebra.TensorProduct.map (AlgHom.id (G i) R) (Scheme.TwoAffineOpenCover.restrictAlgHom fX
        hle) (γR V hV s) =
        γR V' hV' ((Limits.pullback fX (Spec.map (CommRingCat.ofHom (algebraMap (G i)
          R)))).presheaf.map
          (homOfLE ((Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (algebraMap (G i)
            R)))).preimage_mono
            hle)).op s) := by
    intro V V' hV hV' hle s
    change Algebra.TensorProduct.map _ _ (Algebra.TensorProduct.comm (G i) _ R (εR V hV s)) =
      Algebra.TensorProduct.comm (G i) _ R (εR V' hV' _)
    rw [← hε2 V V' hV hV' hle s]
    exact (Algebra.TensorProduct.comm_comp_map_apply _ _ _).symm
  obtain ⟨S, hSfin, hSeq⟩ := (isCompact_iff_finite_and_eq_biUnion_affineOpens (U := W)).1 hW
  have : Finite ↥S := hSfin.to_subtype
  have hSle : ∀ V : ↥S, ((V : X.affineOpens) : X.Opens) ≤ W := fun V => by
    rw [hSeq]; exact le_iSup₂ (f := fun (i : X.affineOpens) (_ : i ∈ S) => (i : X.Opens)) V.1 V.2
  have sA := fun V : ↥S => (hDLv ((V : X.affineOpens) : X.Opens)).surj
    (γR _ V.1.2 ((Limits.pullback fX (Spec.map (CommRingCat.ofHom (algebraMap (G i)
      R)))).presheaf.map (homOfLE ((Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (algebraMap
      (G i) R)))).preimage_mono (hSle V))).op s))
  choose jV zV hzV using sA
  obtain ⟨j₀, hj₀, -⟩ := exists_ge₂ jV jV
  let instK0 : ∀ W' : (Limits.pullback fX (Spec.map (CommRingCat.ofHom (algebraMap (G i) (G
    j₀.1))))).Opens, Algebra (G i) Γ((Limits.pullback fX (Spec.map (CommRingCat.ofHom (algebraMap
    (G i) (G j₀.1))))), W') := fun W' =>
    Scheme.TwoAffineOpenCover.algebraOfHom ((Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom
      (algebraMap (G i) (G j₀.1))))) ≫ fX) W'
  obtain ⟨ε0, -, hε01, hε01', -⟩ :=
    AlgebraicGeometry.exists_algEquiv_sections_pullback_fst_preimage_tensor_of_isAffineOpen (G i)
      fX (G j₀.1)
  have ecomp0 : (g j₀.1).comp (φ i j₀.1 j₀.2) = g i := RingHom.ext fun x => hR.compatibility i j₀.1
    j₀.2 x
  let c₀ : (Limits.pullback fX (Spec.map (CommRingCat.ofHom (algebraMap (G i) R)))) ⟶
    (Limits.pullback fX (Spec.map (CommRingCat.ofHom (algebraMap (G i) (G j₀.1))))) :=
    Limits.pullback.lift (Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (algebraMap (G i)
      R))))
      (Limits.pullback.snd fX (Spec.map (CommRingCat.ofHom (algebraMap (G i) R))) ≫ Spec.map
        (CommRingCat.ofHom (g j₀.1)))
      (by
        rw [Limits.pullback.condition, Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
        exact congrArg (fun r : G i →+* R => Limits.pullback.snd fX
          (Spec.map (CommRingCat.ofHom (algebraMap (G i) R))) ≫ Spec.map (CommRingCat.ofHom r))
            ecomp0.symm)
  have hc₀₁ : c₀ ≫ (Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (algebraMap (G i) (G
    j₀.1))))) = (Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (algebraMap (G i) R)))) :=
    Limits.pullback.lift_fst _ _ _
  have hc₀₂ : c₀ ≫ Limits.pullback.snd fX (Spec.map (CommRingCat.ofHom (algebraMap (G i) (G
    j₀.1)))) =
      Limits.pullback.snd fX (Spec.map (CommRingCat.ofHom (algebraMap (G i) R))) ≫ Spec.map
        (CommRingCat.ofHom (g j₀.1)) :=
    Limits.pullback.lift_snd _ _ _
  have N0 := nat_gamma (G i) fX (G j₀.1) R (IsScalarTower.toAlgHom (G i) (G j₀.1) R) c₀ hc₀₁ hc₀₂
    ε0 hε01 hε01' εR hε1 hε1'
  have huniq : ∀ c : (Limits.pullback fX (Spec.map (CommRingCat.ofHom (algebraMap (G i) R)))) ⟶
    (Limits.pullback fX (Spec.map (CommRingCat.ofHom (algebraMap (G i) (G j₀.1))))), c ≫
    (Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (algebraMap (G i) (G j₀.1))))) =
    (Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (algebraMap (G i) R)))) →
      c ≫ Limits.pullback.snd fX (Spec.map (CommRingCat.ofHom (algebraMap (G i) (G j₀.1)))) =
        Limits.pullback.snd fX (Spec.map (CommRingCat.ofHom (algebraMap (G i) R))) ≫
          Spec.map (CommRingCat.ofHom (g j₀.1)) → c = c₀ := fun c h1 h2 =>
    Limits.pullback.hom_ext (h1.trans hc₀₁.symm) (h2.trans hc₀₂.symm)
  let tV : ∀ V : ↥S, Γ((Limits.pullback fX (Spec.map (CommRingCat.ofHom (algebraMap (G i) (G
    j₀.1))))), (Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (algebraMap (G i) (G j₀.1)))))
    ⁻¹ᵁ ((V : X.affineOpens) : X.Opens)) := fun V =>
    ((ε0 _ V.1.2).trans (Algebra.TensorProduct.comm (G i) _ (G j₀.1))).symm
      (Algebra.TensorProduct.map (f' (jV V) j₀ (hj₀ V)) (AlgHom.id (G i) _) (zV V))
  have e₁ : ∀ V : ↥S, (Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (algebraMap (G i) R))))
    ⁻¹ᵁ ((V : X.affineOpens) : X.Opens) ≤ c₀ ⁻¹ᵁ ((Limits.pullback.fst fX (Spec.map
    (CommRingCat.ofHom (algebraMap (G i) (G j₀.1))))) ⁻¹ᵁ ((V : X.affineOpens) : X.Opens)) :=
    fun V => by rw [← Scheme.Hom.comp_preimage, hc₀₁]
  have htV : ∀ V : ↥S, c₀.appLE _ _ (e₁ V) (tV V) =
      (Limits.pullback fX (Spec.map (CommRingCat.ofHom (algebraMap (G i) R)))).presheaf.map
        (homOfLE ((Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (algebraMap (G i)
        R)))).preimage_mono (hSle V))).op s := by
    intro V
    apply ((εR _ V.1.2).trans (Algebra.TensorProduct.comm (G i) _ R)).injective
    rw [AlgEquiv.trans_apply]
    erw [N0 _ V.1.2 (tV V)]
    change Algebra.TensorProduct.map _ _ (((ε0 _ V.1.2).trans (Algebra.TensorProduct.comm (G i) _
      (G j₀.1))) (tV V)) = _
    rw [show ((ε0 _ V.1.2).trans (Algebra.TensorProduct.comm (G i) _ (G j₀.1))) (tV V) =
      Algebra.TensorProduct.map (f' (jV V) j₀ (hj₀ V)) (AlgHom.id (G i) _) (zV V) from
        AlgEquiv.apply_symm_apply _ _]
    rw [(hDLv _).compatibility (jV V) j₀ (hj₀ V) (zV V), hzV]
  have hWc : ∀ V V' : ↥S, IsCompact ((((V : X.affineOpens) : X.Opens) ⊓ ((V' : X.affineOpens) :
    X.Opens) : X.Opens) : Set X) :=
    fun V V' => QuasiSeparatedSpace.inter_isCompact _ _ (V : X.affineOpens).1.isOpen V.1.2.isCompact
      (V' : X.affineOpens).1.isOpen V'.1.2.isCompact
  have res_htV : ∀ (V : ↥S) (O : X.Opens) (hle : O ≤ ((V : X.affineOpens) : X.Opens))
      (e : (Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (algebraMap (G i) R)))) ⁻¹ᵁ O ≤ c₀
        ⁻¹ᵁ ((Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (algebraMap (G i) (G j₀.1)))))
        ⁻¹ᵁ O)),
      c₀.appLE _ _ e ((Limits.pullback fX (Spec.map (CommRingCat.ofHom (algebraMap (G i) (G
        j₀.1))))).presheaf.map (homOfLE ((Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom
        (algebraMap (G i) (G j₀.1))))).preimage_mono hle)).op (tV V)) =
        (Limits.pullback fX (Spec.map (CommRingCat.ofHom (algebraMap (G i) R)))).presheaf.map
          (homOfLE ((Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (algebraMap (G i)
          R)))).preimage_mono ((hle.trans (hSle V))))).op s := by
    intro V O hle e
    rw [← CategoryTheory.comp_apply, Scheme.Hom.map_appLE]
    have := congrArg ((Limits.pullback fX (Spec.map (CommRingCat.ofHom (algebraMap (G i)
      R)))).presheaf.map (homOfLE ((Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (algebraMap
      (G i) R)))).preimage_mono hle)).op) (htV V)
    rw [← CategoryTheory.comp_apply, Scheme.Hom.appLE_map, res_res] at this
    exact this
  have sB : ∀ V V' : ↥S, ∃ (j' : ι) (hjj' : j₀.1 ≤ j'),
      ∀ (c : Limits.pullback fX (Spec.map (CommRingCat.ofHom (φ i j' (j₀.2.trans hjj')))) ⟶
        (Limits.pullback fX (Spec.map (CommRingCat.ofHom (algebraMap (G i) (G j₀.1)))))),
        c ≫ (Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (algebraMap (G i) (G j₀.1))))) =
          Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (φ i j' (j₀.2.trans hjj')))) →
        c ≫ Limits.pullback.snd fX (Spec.map (CommRingCat.ofHom (algebraMap (G i) (G j₀.1)))) =
          Limits.pullback.snd fX (Spec.map (CommRingCat.ofHom (φ i j' (j₀.2.trans hjj')))) ≫
            Spec.map (CommRingCat.ofHom (φ j₀.1 j' hjj')) →
        c.app ((Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (algebraMap (G i) (G j₀.1)))))
          ⁻¹ᵁ (((V : X.affineOpens) : X.Opens) ⊓ ((V' : X.affineOpens) : X.Opens)))
            ((Limits.pullback fX (Spec.map (CommRingCat.ofHom (algebraMap (G i) (G
              j₀.1))))).presheaf.map (homOfLE ((Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom
              (algebraMap (G i) (G j₀.1))))).preimage_mono inf_le_left)).op (tV V)) =
          c.app ((Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (algebraMap (G i) (G
            j₀.1))))) ⁻¹ᵁ (((V : X.affineOpens) : X.Opens) ⊓ ((V' : X.affineOpens) : X.Opens)))
            ((Limits.pullback fX (Spec.map (CommRingCat.ofHom (algebraMap (G i) (G
              j₀.1))))).presheaf.map (homOfLE ((Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom
              (algebraMap (G i) (G j₀.1))))).preimage_mono inf_le_right)).op (tV V')) := by
    intro V V'
    apply AlgebraicGeometry.Scheme.exists_app_eq_app_of_isCompact_of_isDirectLimit φ g hR i fX _
      (hWc V V') j₀.1 j₀.2
    intro c hc1 hc2
    obtain rfl := huniq c hc1 hc2
    have e : (Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (algebraMap (G i) R)))) ⁻¹ᵁ (((V
      : X.affineOpens) : X.Opens) ⊓ ((V' : X.affineOpens) : X.Opens)) ≤
        c₀ ⁻¹ᵁ ((Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (algebraMap (G i) (G j₀.1)))))
          ⁻¹ᵁ (((V : X.affineOpens) : X.Opens) ⊓ ((V' : X.affineOpens) : X.Opens))) := by
      rw [← Scheme.Hom.comp_preimage, hc₀₁]
    have hE : (Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (algebraMap (G i) R)))) ⁻¹ᵁ (((V
      : X.affineOpens) : X.Opens) ⊓ ((V' : X.affineOpens) : X.Opens)) =
        c₀ ⁻¹ᵁ ((Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (algebraMap (G i) (G j₀.1)))))
          ⁻¹ᵁ (((V : X.affineOpens) : X.Opens) ⊓ ((V' : X.affineOpens) : X.Opens))) := by
      rw [← Scheme.Hom.comp_preimage, hc₀₁]
    refine res_injective_of_eq hE ?_
    have kapp : ∀ x, (Limits.pullback fX (Spec.map (CommRingCat.ofHom (algebraMap (G i)
      R)))).presheaf.map (homOfLE hE.le).op (c₀.app _ x) = c₀.appLE _ _ e x := fun x => by
      rw [← CategoryTheory.comp_apply, Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_map]
    rw [kapp, kapp, res_htV V _ inf_le_left e, res_htV V' _ inf_le_right e]
  choose jB hjB hB using sB
  obtain ⟨m₁, hm₁, -⟩ := exists_ge₂ (fun p : ↥S × ↥S => (⟨jB p.1 p.2, j₀.2.trans (hjB p.1 p.2)⟩ :
    J))
    (fun p : ↥S × ↥S => (⟨jB p.1 p.2, j₀.2.trans (hjB p.1 p.2)⟩ : J))
  obtain ⟨js, h0s, hm₁s⟩ := directed_of (· ≤ ·) j₀ m₁
  have ecomps : (φ j₀.1 js.1 h0s).comp (φ i j₀.1 j₀.2) = algebraMap (G i) (G js.1) :=
    RingHom.ext fun x => DirectedSystem.map_map (f := fun i j h => ⇑(φ i j h)) j₀.2 h0s x
  let cs : (Limits.pullback fX (Spec.map (CommRingCat.ofHom (algebraMap (G i) (G js.1))))) ⟶
    (Limits.pullback fX (Spec.map (CommRingCat.ofHom (algebraMap (G i) (G j₀.1))))) :=
    Limits.pullback.lift (Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (algebraMap (G i) (G
      js.1)))))
      (Limits.pullback.snd fX (Spec.map (CommRingCat.ofHom (algebraMap (G i) (G js.1)))) ≫
        Spec.map (CommRingCat.ofHom (φ j₀.1 js.1 h0s)))
      (by
        rw [Limits.pullback.condition, Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
        exact congrArg (fun r : G i →+* G js.1 => Limits.pullback.snd fX
          (Spec.map (CommRingCat.ofHom (algebraMap (G i) (G js.1)))) ≫ Spec.map (CommRingCat.ofHom
            r)) ecomps.symm)
  have hcs₁ : cs ≫ (Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (algebraMap (G i) (G
    j₀.1))))) = (Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (algebraMap (G i) (G js.1)))))
    := Limits.pullback.lift_fst _ _ _
  have hcs₂ : cs ≫ Limits.pullback.snd fX (Spec.map (CommRingCat.ofHom (algebraMap (G i) (G
    j₀.1)))) =
      Limits.pullback.snd fX (Spec.map (CommRingCat.ofHom (algebraMap (G i) (G js.1)))) ≫
        Spec.map (CommRingCat.ofHom (φ j₀.1 js.1 h0s)) := Limits.pullback.lift_snd _ _ _
  have hagree : ∀ V V' : ↥S,
      cs.app ((Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (algebraMap (G i) (G j₀.1)))))
        ⁻¹ᵁ (((V : X.affineOpens) : X.Opens) ⊓ ((V' : X.affineOpens) : X.Opens)))
          ((Limits.pullback fX (Spec.map (CommRingCat.ofHom (algebraMap (G i) (G
            j₀.1))))).presheaf.map (homOfLE ((Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom
            (algebraMap (G i) (G j₀.1))))).preimage_mono inf_le_left)).op (tV V)) =
        cs.app ((Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (algebraMap (G i) (G j₀.1)))))
          ⁻¹ᵁ (((V : X.affineOpens) : X.Opens) ⊓ ((V' : X.affineOpens) : X.Opens)))
          ((Limits.pullback fX (Spec.map (CommRingCat.ofHom (algebraMap (G i) (G
            j₀.1))))).presheaf.map (homOfLE ((Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom
            (algebraMap (G i) (G j₀.1))))).preimage_mono inf_le_right)).op (tV V')) := by
    intro V V'
    have hBs : jB V V' ≤ js.1 := (hm₁ ⟨V, V'⟩).trans hm₁s
    have ec1 : (φ (jB V V') js.1 hBs).comp (φ i (jB V V') (j₀.2.trans (hjB V V'))) = algebraMap (G
      i) (G js.1) :=
      RingHom.ext fun x => DirectedSystem.map_map (f := fun i j h => ⇑(φ i j h)) (j₀.2.trans (hjB V
        V')) hBs x
    have ec2 : (φ j₀.1 (jB V V') (hjB V V')).comp (φ i j₀.1 j₀.2) = φ i (jB V V') (j₀.2.trans (hjB
      V V')) :=
      RingHom.ext fun x => DirectedSystem.map_map (f := fun i j h => ⇑(φ i j h)) j₀.2 (hjB V V') x
    have ec3 : (φ (jB V V') js.1 hBs).comp (φ j₀.1 (jB V V') (hjB V V')) = φ j₀.1 js.1 h0s :=
      RingHom.ext fun x => DirectedSystem.map_map (f := fun i j h => ⇑(φ i j h)) (hjB V V') hBs x
    let d : (Limits.pullback fX (Spec.map (CommRingCat.ofHom (algebraMap (G i) (G js.1))))) ⟶
      Limits.pullback fX (Spec.map (CommRingCat.ofHom (φ i (jB V V') (j₀.2.trans (hjB V V'))))) :=
      Limits.pullback.lift (Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (algebraMap (G i)
        (G js.1)))))
        (Limits.pullback.snd fX (Spec.map (CommRingCat.ofHom (algebraMap (G i) (G js.1)))) ≫
          Spec.map (CommRingCat.ofHom (φ (jB V V') js.1 hBs)))
        (by
          rw [Limits.pullback.condition, Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
          exact congrArg (fun r : G i →+* G js.1 => Limits.pullback.snd fX
            (Spec.map (CommRingCat.ofHom (algebraMap (G i) (G js.1)))) ≫ Spec.map
              (CommRingCat.ofHom r)) ec1.symm)
    let c' : Limits.pullback fX (Spec.map (CommRingCat.ofHom (φ i (jB V V') (j₀.2.trans (hjB V
      V'))))) ⟶ (Limits.pullback fX (Spec.map (CommRingCat.ofHom (algebraMap (G i) (G j₀.1))))) :=
      Limits.pullback.lift (Limits.pullback.fst fX _)
        (Limits.pullback.snd fX _ ≫ Spec.map (CommRingCat.ofHom (φ j₀.1 (jB V V') (hjB V V'))))
        (by
          rw [Limits.pullback.condition, Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
          exact congrArg (fun r : G i →+* G (jB V V') => Limits.pullback.snd fX
            (Spec.map (CommRingCat.ofHom (φ i (jB V V') (j₀.2.trans (hjB V V'))))) ≫
              Spec.map (CommRingCat.ofHom r)) ec2.symm)
    have hcomp : d ≫ c' = cs := by
      apply Limits.pullback.hom_ext
      · rw [Category.assoc, Limits.pullback.lift_fst, Limits.pullback.lift_fst, hcs₁]
      · rw [Category.assoc, Limits.pullback.lift_snd, ← Category.assoc, Limits.pullback.lift_snd,
          hcs₂,
          Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ec3]
    have hBc := hB V V' c' (Limits.pullback.lift_fst _ _ _) (Limits.pullback.lift_snd _ _ _)
    rw [← hcomp, Scheme.Hom.comp_app]
    exact congrArg (fun y => d.app _ y) hBc
  have eV : ∀ V : ↥S, (Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (algebraMap (G i) (G
    js.1))))) ⁻¹ᵁ ((V : X.affineOpens) : X.Opens) ≤ cs ⁻¹ᵁ ((Limits.pullback.fst fX (Spec.map
    (CommRingCat.ofHom (algebraMap (G i) (G j₀.1))))) ⁻¹ᵁ ((V : X.affineOpens) : X.Opens)) :=
    fun V => by rw [← Scheme.Hom.comp_preimage, hcs₁]
  obtain ⟨τ, hτ⟩ : ∃ τ : ∀ V : ↥S, Γ((Limits.pullback fX (Spec.map (CommRingCat.ofHom (algebraMap
    (G i) (G js.1))))), (Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (algebraMap (G i) (G
    js.1))))) ⁻¹ᵁ ((V : X.affineOpens) : X.Opens)),
      ∀ V, τ V = cs.appLE _ _ (eV V) (tV V) := ⟨_, fun V => rfl⟩
  have e'' : ∀ V V' : ↥S, (Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (algebraMap (G i) (G
    js.1))))) ⁻¹ᵁ ((V : X.affineOpens) : X.Opens) ⊓ (Limits.pullback.fst fX (Spec.map
    (CommRingCat.ofHom (algebraMap (G i) (G js.1))))) ⁻¹ᵁ ((V' : X.affineOpens) : X.Opens) ≤
      cs ⁻¹ᵁ ((Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (algebraMap (G i) (G j₀.1)))))
        ⁻¹ᵁ (((V : X.affineOpens) : X.Opens) ⊓ ((V' : X.affineOpens) : X.Opens))) := fun V V' => by
    rw [← Scheme.Hom.comp_preimage, hcs₁]; exact le_rfl
  have kA : ∀ (V V' : ↥S) y, cs.appLE _ _ (e'' V V') y =
      (Limits.pullback fX (Spec.map (CommRingCat.ofHom (algebraMap (G i) (G js.1))))).presheaf.map
        (homOfLE (e'' V V')).op (cs.app _ y) := fun V V' y => by
    rw [← CategoryTheory.comp_apply, Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_map]
  have compat : TopCat.Presheaf.IsCompatible (Limits.pullback fX (Spec.map (CommRingCat.ofHom
    (algebraMap (G i) (G js.1))))).sheaf.obj
      (fun V : ↥S => (Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (algebraMap (G i) (G
        js.1))))) ⁻¹ᵁ ((V : X.affineOpens) : X.Opens)) τ := by
    intro V V'
    change (Limits.pullback fX (Spec.map (CommRingCat.ofHom (algebraMap (G i) (G
      js.1))))).presheaf.map (homOfLE inf_le_left).op (τ V) = (Limits.pullback fX (Spec.map
      (CommRingCat.ofHom (algebraMap (G i) (G js.1))))).presheaf.map (homOfLE inf_le_right).op (τ
      V')
    rw [hτ, hτ, ← CategoryTheory.comp_apply, Scheme.Hom.appLE_map, ← CategoryTheory.comp_apply,
      Scheme.Hom.appLE_map]
    have kL : cs.appLE ((Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (algebraMap (G i) (G
      j₀.1))))) ⁻¹ᵁ ((V : X.affineOpens) : X.Opens)) _
        ((inf_le_left : (Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (algebraMap (G i) (G
          js.1))))) ⁻¹ᵁ ((V : X.affineOpens) : X.Opens) ⊓ (Limits.pullback.fst fX (Spec.map
          (CommRingCat.ofHom (algebraMap (G i) (G js.1))))) ⁻¹ᵁ ((V' : X.affineOpens) : X.Opens) ≤
          _).trans
          (eV V)) (tV V) =
        cs.appLE _ _ (e'' V V') ((Limits.pullback fX (Spec.map (CommRingCat.ofHom (algebraMap (G i)
          (G j₀.1))))).presheaf.map (homOfLE ((Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom
          (algebraMap (G i) (G j₀.1))))).preimage_mono inf_le_left)).op (tV V)) := by
      rw [← CategoryTheory.comp_apply, Scheme.Hom.map_appLE]
    have kR : cs.appLE ((Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (algebraMap (G i) (G
      j₀.1))))) ⁻¹ᵁ ((V' : X.affineOpens) : X.Opens)) _
        ((inf_le_right : (Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (algebraMap (G i) (G
          js.1))))) ⁻¹ᵁ ((V : X.affineOpens) : X.Opens) ⊓ (Limits.pullback.fst fX (Spec.map
          (CommRingCat.ofHom (algebraMap (G i) (G js.1))))) ⁻¹ᵁ ((V' : X.affineOpens) : X.Opens) ≤
          _).trans
          (eV V')) (tV V') =
        cs.appLE _ _ (e'' V V') ((Limits.pullback fX (Spec.map (CommRingCat.ofHom (algebraMap (G i)
          (G j₀.1))))).presheaf.map (homOfLE ((Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom
          (algebraMap (G i) (G j₀.1))))).preimage_mono inf_le_right)).op (tV V')) := by
      rw [← CategoryTheory.comp_apply, Scheme.Hom.map_appLE]
    erw [kL, kR]
    rw [kA, kA, hagree]
  have hcovs : (Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (algebraMap (G i) (G js.1)))))
    ⁻¹ᵁ W ≤ ⨆ V : ↥S, (Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (algebraMap (G i) (G
    js.1))))) ⁻¹ᵁ ((V : X.affineOpens) : X.Opens) := by
    intro x hx
    have hx' : (Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (algebraMap (G i) (G js.1)))))
      x ∈ (⨆ V ∈ S, (V : X.Opens)) := by rw [← hSeq]; exact hx
    obtain ⟨V, hV⟩ := Opens.mem_iSup.1 hx'
    obtain ⟨hVS, hxV⟩ := Opens.mem_iSup.1 hV
    exact Opens.mem_iSup.2 ⟨⟨V, hVS⟩, hxV⟩
  obtain ⟨t, ht, -⟩ := TopCat.Sheaf.existsUnique_gluing' (Limits.pullback fX (Spec.map
    (CommRingCat.ofHom (algebraMap (G i) (G js.1))))).sheaf
    (fun V : ↥S => (Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (algebraMap (G i) (G
      js.1))))) ⁻¹ᵁ ((V : X.affineOpens) : X.Opens)) ((Limits.pullback.fst fX (Spec.map
      (CommRingCat.ofHom (algebraMap (G i) (G js.1))))) ⁻¹ᵁ W)
    (fun V => homOfLE ((Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (algebraMap (G i) (G
      js.1))))).preimage_mono (hSle V))) hcovs τ compat
  let YS : Scheme.{u} := Limits.pullback fX (Spec.map (CommRingCat.ofHom (φ i js.1 js.2)))
  let YR : Scheme.{u} := Limits.pullback fX (Spec.map (CommRingCat.ofHom (g i)))
  let pS : YS ⟶ X := Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (φ i js.1 js.2)))
  let pR : YR ⟶ X := Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (g i)))
  let ts : Γ(YS, pS ⁻¹ᵁ W) := t
  refine ⟨js.1, js.2, ts, fun c hc1 hc2 e => ?_⟩
  have ecompR : (g js.1).comp (φ j₀.1 js.1 h0s) = g j₀.1 := RingHom.ext fun x => hR.compatibility
    j₀.1 js.1 h0s x
  have hccs : c ≫ cs = c₀ := by
    apply huniq
    · rw [Category.assoc, hcs₁]; exact hc1
    · rw [Category.assoc, hcs₂, ← Category.assoc]
      erw [hc2]
      rw [Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ecompR]
  have k1map : c.app (pS ⁻¹ᵁ W) ≫ YR.presheaf.map (eqToHom e).op =
      c.appLE (pS ⁻¹ᵁ W) (pR ⁻¹ᵁ W) e.le := by
    rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_map]
  have k1 := congrArg
    (fun f : Γ(YS, pS ⁻¹ᵁ W) ⟶ Γ(YR, pR ⁻¹ᵁ W) => f.hom ts) k1map
  refine k1.trans ?_
  have hcovR : pR ⁻¹ᵁ W ≤ ⨆ V : ↥S, pR ⁻¹ᵁ ((V : X.affineOpens) : X.Opens) := by
    intro x hx
    have hx' : pR x ∈ (⨆ V ∈ S, (V : X.Opens)) := by rw [← hSeq]; exact hx
    obtain ⟨V, hV⟩ := Opens.mem_iSup.1 hx'
    obtain ⟨hVS, hxV⟩ := Opens.mem_iSup.1 hV
    exact Opens.mem_iSup.2 ⟨⟨V, hVS⟩, hxV⟩
  apply TopCat.Sheaf.eq_of_locally_eq' YR.sheaf
    (fun V : ↥S => pR ⁻¹ᵁ ((V : X.affineOpens) : X.Opens)) (pR ⁻¹ᵁ W)
    (fun V => homOfLE (pR.preimage_mono (hSle V))) hcovR
  intro V
  have eV' : pR ⁻¹ᵁ ((V : X.affineOpens) : X.Opens) ≤
      c ⁻¹ᵁ (pS ⁻¹ᵁ ((V : X.affineOpens) : X.Opens)) := by
    rw [← Scheme.Hom.comp_preimage, hc1]
  have hmap :
      c.appLE (pS ⁻¹ᵁ W) (pR ⁻¹ᵁ W) e.le ≫
          YR.presheaf.map (homOfLE (pR.preimage_mono (hSle V))).op =
        YS.presheaf.map (homOfLE (pS.preimage_mono (hSle V))).op ≫
          c.appLE (pS ⁻¹ᵁ ((V : X.affineOpens) : X.Opens))
            (pR ⁻¹ᵁ ((V : X.affineOpens) : X.Opens)) eV' := by
    rw [Scheme.Hom.appLE_map, Scheme.Hom.map_appLE]
  have hmapt := congrArg
    (fun f : Γ(YS, pS ⁻¹ᵁ W) ⟶ Γ(YR, pR ⁻¹ᵁ ((V : X.affineOpens) : X.Opens)) => f.hom ts) hmap
  refine hmapt.trans ?_
  have hrestrict : YS.presheaf.map (homOfLE (pS.preimage_mono (hSle V))).op ts = τ V := ht V
  refine (congrArg
    (fun z : Γ(YS, pS ⁻¹ᵁ ((V : X.affineOpens) : X.Opens)) =>
      (c.appLE (pS ⁻¹ᵁ ((V : X.affineOpens) : X.Opens))
        (pR ⁻¹ᵁ ((V : X.affineOpens) : X.Opens)) eV').hom z)
    (hrestrict.trans (hτ V))).trans ?_
  exact (appLE_appLE_of_comp_eq c cs c₀ hccs _ _ _ (eV V) eV' (e₁ V) (tV V)).trans (htV V)

end
end AlgebraicCurves.Geometry.Schemes.Proofs.Scheme_exists_app_eq_of_isCompact_of_isDirectLimit
end ProofImplementation

attribute [-instance] TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module
  TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing
  TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module
  TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower
  TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing
  TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module
  TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup
  TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower
  CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup
  CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup
  CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite
  CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free
attribute [-simp] AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq
  AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec
  AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1
  AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq
  TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq
  TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec
  TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec
  TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec
  CoherentBaseChange.TwoTermComplex.mk.injEq
