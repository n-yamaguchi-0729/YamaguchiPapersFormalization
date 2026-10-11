/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_Module_FaithfullyFlat_exists_submodule_isBaseChange_of_cocycle.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Foundations.Algebra.Algebra_DescentCofaces
import Nyll.SchemeTheory.RingTheory.Descent.InvertibleModule

/-!
# Effective descent of modules along a faithfully flat algebra

The equalizer of the descent maps is the descended submodule. Tensor calculations
identify its base change and verify the descent square.
-/

section ProofImplementation

namespace AlgebraicCurves.Foundations.Algebra.Proofs.FaithfullyFlatDescent

open TensorProduct CategoryTheory Algebra.DescentCofaces

universe u

namespace S17C1

section HelperE

open scoped ChangeOfRings

variable {R S T : Type u} [CommRing R] [CommRing S] [CommRing T] (f : R →+* S) (g : S →+* T)
  (M : ModuleCat.{u} R)

theorem esComp_inv_one_tmul_tmul (x : S) (m : M) :
    (ModuleCat.extendScalarsComp f g).inv.app M
      ((1 : T) ⊗ₜ[S, g] ((x ⊗ₜ[R, f] m : (ModuleCat.extendScalars f).obj M)) :
        (ModuleCat.extendScalars g).obj ((ModuleCat.extendScalars f).obj M)) =
      ((g x) ⊗ₜ[R, g.comp f] m : (ModuleCat.extendScalars (g.comp f)).obj M) := by
  have hx : (x ⊗ₜ[R, f] m : (ModuleCat.extendScalars f).obj M) =
      SMul.smul (M := S) (α := (ModuleCat.extendScalars f).obj M) x
        ((1 : S) ⊗ₜ[R, f] m) := by
    exact ((ModuleCat.ExtendScalars.smul_tmul f (M := M) x 1 m).trans
      (congrArg (fun z : S => z ⊗ₜ[R, f] m) (mul_one x))).symm
  have h1 : ((1 : T) ⊗ₜ[S, g] ((x ⊗ₜ[R, f] m : (ModuleCat.extendScalars f).obj M)) :
        (ModuleCat.extendScalars g).obj ((ModuleCat.extendScalars f).obj M)) =
      SMul.smul (M := T)
        (α := (ModuleCat.extendScalars g).obj ((ModuleCat.extendScalars f).obj M)) (g x)
        ((1 : T) ⊗ₜ[S, g] ((1 : S) ⊗ₜ[R, f] m : (ModuleCat.extendScalars f).obj M) :
        (ModuleCat.extendScalars g).obj ((ModuleCat.extendScalars f).obj M)) := by
    let Tg : ModuleCat S :=
      (ModuleCat.restrictScalars g).obj (ModuleCat.of T T)
    let m₀ : (ModuleCat.extendScalars f).obj M := (1 : S) ⊗ₜ[R, f] m
    have hmul : (x • (show Tg from (1 : T)) : Tg) = (show Tg from g x) := by
      change g x * 1 = g x
      exact mul_one (g x)
    have hbalance :
        ((1 : T) ⊗ₜ[S, g]
          SMul.smul (M := S) (α := (ModuleCat.extendScalars f).obj M) x m₀ :
          (ModuleCat.extendScalars g).obj ((ModuleCat.extendScalars f).obj M)) =
        (g x) ⊗ₜ[S, g] m₀ :=
      ((TensorProduct.tmul_smul (R := S) x (show Tg from (1 : T)) m₀).trans
        (TensorProduct.smul_tmul' (R := S) x (show Tg from (1 : T)) m₀)).trans
          (congrArg (fun z : Tg => z ⊗ₜ[S] m₀) hmul)
    have hscalar := ((ModuleCat.ExtendScalars.smul_tmul g
      (M := (ModuleCat.extendScalars f).obj M) (g x) 1 m₀).trans
        (congrArg (fun z : T => z ⊗ₜ[S, g] m₀) (mul_one (g x)))).symm
    exact (congrArg
      (fun z : (ModuleCat.extendScalars f).obj M => (1 : T) ⊗ₜ[S, g] z) hx).trans
        (hbalance.trans hscalar)
  rw [h1]
  have hmap := ((ModuleCat.extendScalarsComp f g).inv.app M).hom.map_smul (g x)
    ((1 : T) ⊗ₜ[S, g] ((1 : S) ⊗ₜ[R, f] m))
  refine hmap.trans ?_
  erw [← ModuleCat.extendScalarsComp_hom_app_one_tmul f g M m]
  change (g x) • (((ModuleCat.extendScalarsComp f g).hom.app M ≫ (ModuleCat.extendScalarsComp f
    g).inv.app M) _) = _
  rw [Iso.hom_inv_id_app]
  change SMul.smul (M := T) (α := (ModuleCat.extendScalars (g.comp f)).obj M) (g x)
    ((1 : T) ⊗ₜ[R, g.comp f] m) = _
  exact (ModuleCat.ExtendScalars.smul_tmul (g.comp f) (M := M) (g x) 1 m).trans
    (congrArg (fun z : T => z ⊗ₜ[R, g.comp f] m) (mul_one (g x)))

theorem esComp_hom_one_tmul (m : M) :
    (ModuleCat.extendScalarsComp f g).hom.app M ((1 : T) ⊗ₜ[R, g.comp f] m :
      (ModuleCat.extendScalars (g.comp f)).obj M) =
      ((1 : T) ⊗ₜ[S, g] ((1 : S) ⊗ₜ[R, f] m : (ModuleCat.extendScalars f).obj M) :
        (ModuleCat.extendScalars g).obj ((ModuleCat.extendScalars f).obj M)) :=
  ModuleCat.extendScalarsComp_hom_app_one_tmul f g M m

theorem es_map_one_tmul {M₁ M₂ : ModuleCat.{u} S} (φ : M₁ ⟶ M₂) (e : M₁) :
    (ModuleCat.extendScalars g).map φ ((1 : T) ⊗ₜ[S, g] e : (ModuleCat.extendScalars g).obj M₁) =
      ((1 : T) ⊗ₜ[S, g] φ e : (ModuleCat.extendScalars g).obj M₂) :=
  ModuleCat.ExtendScalars.map_tmul g φ 1 e

theorem esComp_hom_tmul (s : T) (m : M) :
    (ModuleCat.extendScalarsComp f g).hom.app M ((s ⊗ₜ[R, g.comp f] m : (ModuleCat.extendScalars
      (g.comp f)).obj M)) =
      SMul.smul (M := T)
        (α := (ModuleCat.extendScalars g).obj ((ModuleCat.extendScalars f).obj M)) s
        ((1 : T) ⊗ₜ[S, g] ((1 : S) ⊗ₜ[R, f] m : (ModuleCat.extendScalars f).obj M) :
        (ModuleCat.extendScalars g).obj ((ModuleCat.extendScalars f).obj M)) := by
  have hs : (s ⊗ₜ[R, g.comp f] m : (ModuleCat.extendScalars (g.comp f)).obj M) =
      SMul.smul (M := T) (α := (ModuleCat.extendScalars (g.comp f)).obj M) s
        ((1 : T) ⊗ₜ[R, g.comp f] m) := by
    exact ((ModuleCat.ExtendScalars.smul_tmul (g.comp f) (M := M) s 1 m).trans
      (congrArg (fun z : T => z ⊗ₜ[R, g.comp f] m) (mul_one s))).symm
  rw [hs]
  have hmap := ((ModuleCat.extendScalarsComp f g).hom.app M).hom.map_smul s
    ((1 : T) ⊗ₜ[R, g.comp f] m)
  refine hmap.trans ?_
  erw [ModuleCat.extendScalarsComp_hom_app_one_tmul f g M m]
  rfl

theorem eqToHom_extendScalars_tmul {f f' : R →+* S} (h : f = f') (s : S) (m : M) :
    eqToHom (congrArg (fun f : R →+* S => (ModuleCat.extendScalars f).obj M) h)
      (s ⊗ₜ[R, f] m : (ModuleCat.extendScalars f).obj M) = (s ⊗ₜ[R, f'] m :
        (ModuleCat.extendScalars f').obj M) := by
  subst h
  rfl

theorem es_one_tmul_smul (r : R) (m : M) :
    ((1 : S) ⊗ₜ[R, f] (r • m) : (ModuleCat.extendScalars f).obj M) =
      SMul.smul (M := S) (α := (ModuleCat.extendScalars f).obj M) (f r)
        ((1 : S) ⊗ₜ[R, f] m) := by
  let Sf : ModuleCat R := (ModuleCat.restrictScalars f).obj (ModuleCat.of S S)
  have hm : (r • (show Sf from (1 : S)) : Sf) = (show Sf from f r) := by
    change f r * 1 = f r
    exact mul_one (f r)
  have hb := ((TensorProduct.tmul_smul (R := R) r (show Sf from (1 : S)) m).trans
    (TensorProduct.smul_tmul' (R := R) r (show Sf from (1 : S)) m)).trans
      (congrArg (fun z : Sf => z ⊗ₜ[R] m) hm)
  have hs := (ModuleCat.ExtendScalars.smul_tmul f (M := M) (f r) 1 m).trans
    (congrArg (fun z : S => z ⊗ₜ[R, f] m) (mul_one (f r)))
  exact hb.trans hs.symm

end HelperE

section Transport

open scoped ChangeOfRings

variable {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]

theorem compareScalarExtensions_one_tmul_tmul
    (f : R →+* S) (g₁ g₂ : S →+* T) (h : g₁.comp f = g₂.comp f)
    (M : ModuleCat.{u} R) (x : S) (m : M) :
    compareScalarExtensions f g₁ g₂ h M
      ((1 : T) ⊗ₜ[S, g₁] (x ⊗ₜ[R, f] m : (ModuleCat.extendScalars f).obj M)) =
      ((g₁ x) ⊗ₜ[S, g₂] ((1 : S) ⊗ₜ[R, f] m : (ModuleCat.extendScalars f).obj M) :
        (ModuleCat.extendScalars g₂).obj ((ModuleCat.extendScalars f).obj M)) := by
  change (ModuleCat.extendScalarsComp f g₂).hom.app M
    (eqToHom (congrArg (fun φ : R →+* T => (ModuleCat.extendScalars φ).obj M) h)
      ((ModuleCat.extendScalarsComp f g₁).inv.app M _)) = _
  let C := eqToHom (congrArg
    (fun φ : R →+* T => (ModuleCat.extendScalars φ).obj M) h)
  let H := (ModuleCat.extendScalarsComp f g₂).hom.app M
  refine (congrArg (fun z : (ModuleCat.extendScalars (g₁.comp f)).obj M => H (C z))
    (esComp_inv_one_tmul_tmul f g₁ M x m)).trans ?_
  refine (congrArg H (eqToHom_extendScalars_tmul (M := M) h (g₁ x) m)).trans ?_
  refine (esComp_hom_tmul f g₂ M (g₁ x) m).trans ?_
  exact (ModuleCat.ExtendScalars.smul_tmul g₂
    (M := (ModuleCat.extendScalars f).obj M) (g₁ x) 1 _).trans
      (congrArg (fun z : T => (z ⊗ₜ[S, g₂]
        ((1 : S) ⊗ₜ[R, f] m : (ModuleCat.extendScalars f).obj M) :
          (ModuleCat.extendScalars g₂).obj ((ModuleCat.extendScalars f).obj M)))
            (mul_one (g₁ x)))


theorem comparison_square (f : R →+* S) (g₁ g₂ : S →+* T)
    (h : g₁.comp f = g₂.comp f) (P : ModuleCat.{u} R) (Q : ModuleCat.{u} S)
    (θ : (ModuleCat.extendScalars f).obj P ⟶ Q)
    (φ : (ModuleCat.extendScalars g₁).obj Q ⟶ (ModuleCat.extendScalars g₂).obj Q)
    (hunit : ∀ m : P,
      φ ((1 : T) ⊗ₜ[S, g₁] θ ((1 : S) ⊗ₜ[R, f] m)) =
        ((1 : T) ⊗ₜ[S, g₂] θ ((1 : S) ⊗ₜ[R, f] m) :
          (ModuleCat.extendScalars g₂).obj Q)) :
    (ModuleCat.extendScalars g₁).map θ ≫ φ =
      compareScalarExtensions f g₁ g₂ h P ≫ (ModuleCat.extendScalars g₂).map θ := by
  let E := (ModuleCat.extendScalars f).obj P
  let L := (ModuleCat.extendScalars g₁).map θ ≫ φ
  let K := compareScalarExtensions f g₁ g₂ h P ≫ (ModuleCat.extendScalars g₂).map θ
  apply ModuleCat.ExtendScalars.hom_ext
  intro e
  induction e using TensorProduct.inductionOn with
  | add x y hx hy =>
    have ht := TensorProduct.tmul_add (R := S) (N := E)
      (show (ModuleCat.restrictScalars g₁).obj (ModuleCat.of T T) from (1 : T)) x y
    exact (congrArg L ht).trans ((L.hom.map_add _ _).trans
      ((congrArg₂ (· + ·) hx hy).trans ((K.hom.map_add _ _).symm.trans (congrArg K ht.symm))))
  | tmul x m =>
    have hθ : θ (x ⊗ₜ[R, f] m) =
        SMul.smul (M := S) (α := Q) (show S from x) (θ ((1 : S) ⊗ₜ[R, f] m)) := by
      have hx := (ModuleCat.ExtendScalars.smul_tmul f (M := P) x 1 m).trans
        (congrArg (fun z : S => (z ⊗ₜ[R, f] m : E)) (mul_one (show S from x)))
      exact (congrArg θ hx.symm).trans (θ.hom.map_smul x _)
    have hl : L ((1 : T) ⊗ₜ[S, g₁] (x ⊗ₜ[R, f] m : E)) =
        SMul.smul (M := T) (α := (ModuleCat.extendScalars g₂).obj Q) (g₁ x)
          (φ ((1 : T) ⊗ₜ[S, g₁] θ ((1 : S) ⊗ₜ[R, f] m))) := by
      refine (congrArg φ (ModuleCat.ExtendScalars.map_tmul g₁ θ 1
        (x ⊗ₜ[R, f] m : E))).trans ?_
      refine (congrArg (fun z : Q => φ ((1 : T) ⊗ₜ[S, g₁] z)) hθ).trans ?_
      refine (congrArg φ (es_one_tmul_smul g₁ Q x
        (θ ((1 : S) ⊗ₜ[R, f] m)))).trans ?_
      exact φ.hom.map_smul (g₁ x) _
    have hr : K ((1 : T) ⊗ₜ[S, g₁] (x ⊗ₜ[R, f] m : E)) =
        SMul.smul (M := T) (α := (ModuleCat.extendScalars g₂).obj Q) (g₁ x)
          ((1 : T) ⊗ₜ[S, g₂] θ ((1 : S) ⊗ₜ[R, f] m)) := by
      refine (congrArg ((ModuleCat.extendScalars g₂).map θ)
        (compareScalarExtensions_one_tmul_tmul f g₁ g₂ h P x m)).trans ?_
      refine (ModuleCat.ExtendScalars.map_tmul g₂ θ (g₁ x)
        ((1 : S) ⊗ₜ[R, f] m)).trans ?_
      exact ((ModuleCat.ExtendScalars.smul_tmul g₂ (M := Q) (g₁ x) 1
        (θ ((1 : S) ⊗ₜ[R, f] m))).trans
          (congrArg (fun z : T => (z ⊗ₜ[S, g₂] θ ((1 : S) ⊗ₜ[R, f] m) :
            (ModuleCat.extendScalars g₂).obj Q)) (mul_one (g₁ x)))).symm
    exact hl.trans ((congrArg
      (fun z : (ModuleCat.extendScalars g₂).obj Q => (g₁ x) • z) (hunit m)).trans hr.symm)

end Transport

section Dictionary

open ChangeOfRings

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
  (N : Type u) [AddCommGroup N] [Module B N] [Module A N] [IsScalarTower A B N]

/-- The given module bundled over the extension ring. -/
noncomputable abbrev Nc : ModuleCat.{u} B := ModuleCat.of B N

/-- The double tensor ring with scalars restricted along the first coface. -/
noncomputable abbrev X₁ (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] :=
  ↑((ModuleCat.restrictScalars (i₁ A B).hom).obj (ModuleCat.of (R₂ A B) (R₂ A B)))
/-- The double tensor ring with scalars restricted along the second coface. -/
noncomputable abbrev X₂ (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] :=
  ↑((ModuleCat.restrictScalars (i₂ A B).hom).obj (ModuleCat.of (R₂ A B) (R₂ A B)))
/-- Extend the given module along the first coface. -/
noncomputable abbrev E₁ := (ModuleCat.extendScalars (i₁ A B).hom).obj (Nc N)
/-- Extend the given module along the second coface. -/
noncomputable abbrev E₂ := (ModuleCat.extendScalars (i₂ A B).hom).obj (Nc N)

theorem X₁_smul_def (b : B) (x : B ⊗[A] B) :
    (b • (show X₁ A B from x) : X₁ A B) = (show X₁ A B from (b ⊗ₜ[A] (1 : B)) * x) := rfl
theorem X₂_smul_def (b : B) (x : B ⊗[A] B) :
    (b • (show X₂ A B from x) : X₂ A B) = (show X₂ A B from ((1 : B) ⊗ₜ[A] b) * x) := rfl

/-- Act on the module by the first tensor factor and retain the second factor. -/
noncomputable def k₁ : B ⊗[A] B →ₗ[A] N →ₗ[A] N ⊗[A] B :=
  TensorProduct.lift (LinearMap.mk₂ A
    (fun (b₁ b₂ : B) => (TensorProduct.mk A N B).flip b₂ ∘ₗ DistribSMul.toLinearMap A N b₁)
    (fun _ _ _ => by ext; simp [add_smul])
    (fun _ _ _ => by ext; simp [smul_tmul'])
    (fun _ _ _ => by ext; simp)
    (fun _ _ _ => by ext; simp))

theorem k₁_tmul (b₁ b₂ : B) (n : N) : k₁ (A := A) N (b₁ ⊗ₜ b₂) n = (b₁ • n) ⊗ₜ b₂ := rfl

/-- The balanced linear map induced by the first-factor action. -/
noncomputable def u₁ : X₁ A B ⊗[B] N →ₗ[B] N ⊗[A] B :=
  TensorProduct.lift (LinearMap.mk₂' B B (fun (x : X₁ A B) (n : N) => k₁ (A := A) N x n)
    (fun x y n => by
      exact congrArg (fun g : N →ₗ[A] N ⊗[A] B => g n) (map_add (k₁ (A := A) N) x y))
    (fun b x n => by
      change k₁ (A := A) N ((b ⊗ₜ[A] (1 : B)) * (show B ⊗[A] B from x)) n = b • k₁ (A := A) N x n
      induction x using TensorProduct.inductionOn with
      | add x y hx hy => simp only [mul_add, map_add, LinearMap.add_apply, hx, hy, smul_add]
      | tmul b₁ b₂ =>
        rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, k₁_tmul, k₁_tmul, mul_smul,
          TensorProduct.smul_tmul'])
    (fun x n n' => by
      change k₁ (A := A) N x (n + n') = k₁ (A := A) N x n + k₁ (A := A) N x n'
      rw [map_add])
    (fun b x n => by
      change k₁ (A := A) N (show B ⊗[A] B from x) (b • n) = b • k₁ (A := A) N x n
      induction x using TensorProduct.inductionOn with
      | add x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy, smul_add]
      | tmul b₁ b₂ => rw [k₁_tmul, k₁_tmul, smul_comm, TensorProduct.smul_tmul']))

theorem u₁_tmul (b₁ b₂ : B) (n : N) :
    u₁ (A := A) N ((show X₁ A B from b₁ ⊗ₜ[A] b₂) ⊗ₜ[B] n) = (b₁ • n) ⊗ₜ b₂ := by
  exact k₁_tmul (A := A) N b₁ b₂ n

/-- Act on the module by the second tensor factor and retain the first factor. -/
noncomputable def k₂ : B ⊗[A] B →ₗ[A] N →ₗ[A] N ⊗[A] B :=
  k₁ (A := A) N ∘ₗ (TensorProduct.comm A B B).toLinearMap

theorem k₂_tmul (b₁ b₂ : B) (n : N) : k₂ (A := A) N (b₁ ⊗ₜ b₂) n = (b₂ • n) ⊗ₜ b₁ := rfl

/-- The balanced linear map induced by the second-factor action. -/
noncomputable def u₂ : X₂ A B ⊗[B] N →ₗ[B] N ⊗[A] B :=
  TensorProduct.lift (LinearMap.mk₂' B B (fun (x : X₂ A B) (n : N) => k₂ (A := A) N x n)
    (fun x y n => by
      exact congrArg (fun g : N →ₗ[A] N ⊗[A] B => g n) (map_add (k₂ (A := A) N) x y))
    (fun b x n => by
      change k₂ (A := A) N (((1 : B) ⊗ₜ[A] b) * (show B ⊗[A] B from x)) n = b • k₂ (A := A) N x n
      induction x using TensorProduct.inductionOn with
      | add x y hx hy => simp only [mul_add, map_add, LinearMap.add_apply, hx, hy, smul_add]
      | tmul b₁ b₂ =>
        rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, k₂_tmul, k₂_tmul, mul_smul,
          TensorProduct.smul_tmul'])
    (fun x n n' => by
      change k₂ (A := A) N x (n + n') = k₂ (A := A) N x n + k₂ (A := A) N x n'
      rw [map_add])
    (fun b x n => by
      change k₂ (A := A) N (show B ⊗[A] B from x) (b • n) = b • k₂ (A := A) N x n
      induction x using TensorProduct.inductionOn with
      | add x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy, smul_add]
      | tmul b₁ b₂ => rw [k₂_tmul, k₂_tmul, smul_comm, TensorProduct.smul_tmul']))

theorem u₂_tmul (b₁ b₂ : B) (n : N) :
    u₂ (A := A) N ((show X₂ A B from b₁ ⊗ₜ[A] b₂) ⊗ₜ[B] n) = (b₂ • n) ⊗ₜ b₁ := by
  exact k₂_tmul (A := A) N b₁ b₂ n

/-- Insert a unit tensor factor to invert the second-factor comparison. -/
noncomputable def v₂ : N ⊗[A] B →+ X₂ A B ⊗[B] N :=
  TensorProduct.liftAddHom
    { toFun := fun n =>
        { toFun := fun b => ((show X₂ A B from b ⊗ₜ[A] (1 : B)) ⊗ₜ[B] n : X₂ A B ⊗[B] N)
          map_zero' := (congrArg (fun z : X₂ A B => z ⊗ₜ[B] n)
            (TensorProduct.zero_tmul (R := A) B (1 : B))).trans (TensorProduct.zero_tmul (R := B)
              (X₂ A B) n)
          map_add' := fun b b' =>
            (congrArg (fun z : X₂ A B => z ⊗ₜ[B] n)
              (TensorProduct.add_tmul b b' (1 : B))).trans
                (TensorProduct.add_tmul (show X₂ A B from b ⊗ₜ[A] (1 : B))
                  (show X₂ A B from b' ⊗ₜ[A] (1 : B)) n) }
      map_zero' := by ext b; exact TensorProduct.tmul_zero _ _
      map_add' := fun n n' => by ext b; exact TensorProduct.tmul_add _ n n' }
    (fun a n b => by
      change ((show X₂ A B from b ⊗ₜ[A] (1 : B)) ⊗ₜ[B] (a • n) : X₂ A B ⊗[B] N) =
        ((show X₂ A B from (a • b) ⊗ₜ[A] (1 : B)) ⊗ₜ[B] n : X₂ A B ⊗[B] N)
      rw [← IsScalarTower.algebraMap_smul B a n, TensorProduct.tmul_smul, TensorProduct.smul_tmul']
      congr 1
      change ((1 : B) ⊗ₜ[A] algebraMap A B a) * (b ⊗ₜ[A] (1 : B)) = (a • b) ⊗ₜ[A] (1 : B)
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one, Algebra.algebraMap_eq_smul_one,
        TensorProduct.tmul_smul, TensorProduct.smul_tmul'])

theorem v₂_tmul (n : N) (b : B) :
      v₂ (A := A) N (n ⊗ₜ b) = (((show X₂ A B from b ⊗ₜ[A] (1 : B)) ⊗ₜ[B] n : X₂ A B ⊗[B] N)) := rfl

theorem v₂_u₂ (e : X₂ A B ⊗[B] N) : v₂ (A := A) N (u₂ (A := A) N e) = e := by
  induction e using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul x n =>
    revert n
    refine TensorProduct.inductionOn (motive := fun x : B ⊗[A] B => ∀ n : N,
      v₂ (A := A) N (u₂ (A := A) N ((show X₂ A B from x) ⊗ₜ[B] n : X₂ A B ⊗[B] N)) = ((show X₂ A B
        from x) ⊗ₜ[B] n : X₂ A B ⊗[B] N)) x ?_ ?_
    · intro b₁ b₂ n
      erw [u₂_tmul]
      rw [v₂_tmul, TensorProduct.tmul_smul, TensorProduct.smul_tmul']
      congr 1
      change ((1 : B) ⊗ₜ[A] b₂) * (b₁ ⊗ₜ[A] (1 : B)) = b₁ ⊗ₜ[A] b₂
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
    · intro x y hx hy n
      rw [show ((show X₂ A B from x + y) ⊗ₜ[B] n : X₂ A B ⊗[B] N) =
        ((show X₂ A B from x) ⊗ₜ[B] n : X₂ A B ⊗[B] N) + ((show X₂ A B from y) ⊗ₜ[B] n : X₂ A B
          ⊗[B] N) from TensorProduct.add_tmul _ _ n]
      simp only [map_add, hx, hy]

theorem u₂_injective : Function.Injective (u₂ (A := A) (B := B) N) :=
  Function.LeftInverse.injective (v₂_u₂ (A := A) N)

/-- The triple tensor ring with scalars restricted to its third factor. -/
noncomputable abbrev X₃ (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] :=
  ↑((ModuleCat.restrictScalars (i₂ A B ≫ c₂₃ A B).hom).obj (ModuleCat.of (R₃ A B) (R₃ A B)))
/-- Extend the given module to the triple tensor ring through its third factor. -/
noncomputable abbrev F₃ := (ModuleCat.extendScalars (i₂ A B ≫ c₂₃ A B).hom).obj (Nc N)

theorem j₃_apply (b : B) : (i₂ A B ≫ c₂₃ A B).hom b = 1 ⊗ₜ (1 ⊗ₜ b) := rfl

/-- Evaluate the scalar action on a tensor product with the module. -/
noncomputable def act : B ⊗[A] N →ₗ[A] N :=
  TensorProduct.lift (LinearMap.mk₂ A (fun (b : B) (n : N) => b • n)
    (fun (b b' : B) (n : N) => add_smul b b' n) (fun (a : A) (b : B) (n : N) => smul_assoc a b n)
    (fun (b : B) (n n' : N) => smul_add b n n') (fun (a : A) (b : B) (n : N) => smul_comm b a n))

theorem act_tmul (b : B) (n : N) : act (A := A) N (b ⊗ₜ n) = b • n := rfl

/-- Move the module factor past the first two scalars and evaluate the third scalar. -/
noncomputable def K₃ : (B ⊗[A] (B ⊗[A] B)) ⊗[A] N →ₗ[A] N ⊗[A] (B ⊗[A] B) :=
  (act (A := A) N).rTensor (B ⊗[A] B) ∘ₗ
    (TensorProduct.comm A (B ⊗[A] B) (B ⊗[A] N)).toLinearMap ∘ₗ
    (TensorProduct.assoc A B B (B ⊗[A] N)).symm.toLinearMap ∘ₗ
    (TensorProduct.assoc A B B N).toLinearMap.lTensor B ∘ₗ
    (TensorProduct.assoc A B (B ⊗[A] B) N).toLinearMap

theorem K₃_tmul (b₁ b₂ b₃ : B) (n : N) :
    K₃ (A := A) N ((b₁ ⊗ₜ (b₂ ⊗ₜ b₃)) ⊗ₜ n) = (b₃ • n) ⊗ₜ (b₁ ⊗ₜ b₂) := by
  simp [K₃, act_tmul]

/-- The curried form of the triple-tensor comparison. -/
noncomputable def k₃ : B ⊗[A] (B ⊗[A] B) →ₗ[A] N →ₗ[A] N ⊗[A] (B ⊗[A] B) :=
  TensorProduct.curry (K₃ (A := A) N)

theorem k₃_tmul (b₁ b₂ b₃ : B) (n : N) :
    k₃ (A := A) N (b₁ ⊗ₜ (b₂ ⊗ₜ b₃)) n = (b₃ • n) ⊗ₜ (b₁ ⊗ₜ b₂) :=
  K₃_tmul (A := A) N b₁ b₂ b₃ n

/-- The balanced triple-tensor comparison through the third-factor action. -/
noncomputable def u₃ : X₃ A B ⊗[B] N →ₗ[B] N ⊗[A] (B ⊗[A] B) :=
  TensorProduct.lift (LinearMap.mk₂' B B (fun (y : X₃ A B) (n : N) => k₃ (A := A) N y n)
    (fun x y n => by
      exact congrArg (fun g : N →ₗ[A] N ⊗[A] (B ⊗[A] B) => g n) (map_add (k₃ (A := A) N) x y))
    (fun b y n => by
      change k₃ (A := A) N (((1 : B) ⊗ₜ[A] ((1 : B) ⊗ₜ[A] b)) * (show B ⊗[A] (B ⊗[A] B) from y)) n =
        b • k₃ (A := A) N y n
      induction y using TensorProduct.inductionOn with
      | add x y hx hy => simp only [mul_add, map_add, LinearMap.add_apply, hx, hy, smul_add]
      | tmul b₁ z =>
        induction z using TensorProduct.inductionOn with
        | add x y hx hy =>
            simp only [tmul_add, mul_add, map_add, LinearMap.add_apply, hx, hy, smul_add]
        | tmul b₂ b₃ =>
          rw [Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, one_mul,
            one_mul,
            k₃_tmul, k₃_tmul, mul_smul, TensorProduct.smul_tmul'])
    (fun y n n' => by
      change k₃ (A := A) N y (n + n') = k₃ (A := A) N y n + k₃ (A := A) N y n'
      rw [map_add])
    (fun b y n => by
      change k₃ (A := A) N (show B ⊗[A] (B ⊗[A] B) from y) (b • n) = b • k₃ (A := A) N y n
      induction y using TensorProduct.inductionOn with
      | add x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy, smul_add]
      | tmul b₁ z =>
        induction z using TensorProduct.inductionOn with
        | add x y hx hy => simp only [tmul_add, map_add, LinearMap.add_apply, hx, hy, smul_add]
        | tmul b₂ b₃ => rw [k₃_tmul, k₃_tmul, smul_comm, TensorProduct.smul_tmul']))

theorem u₃_tmul (b₁ b₂ b₃ : B) (n : N) :
    u₃ (A := A) N ((show X₃ A B from b₁ ⊗ₜ[A] (b₂ ⊗ₜ[A] b₃)) ⊗ₜ[B] n) = (b₃ • n) ⊗ₜ (b₁ ⊗ₜ b₂) := by
  exact k₃_tmul (A := A) N b₁ b₂ b₃ n

/-- Restrict scalars on the triple tensor ring along the chosen composite coface. -/
noncomputable abbrev Xc (c : R₂ A B ⟶ R₃ A B) :=
  ↑((ModuleCat.restrictScalars (i₂ A B ≫ c).hom).obj (ModuleCat.of (R₃ A B) (R₃ A B)))
/-- Extend the given module along the chosen composite coface. -/
noncomputable abbrev Fc (c : R₂ A B ⟶ R₃ A B) := (ModuleCat.extendScalars (i₂ A B ≫ c).hom).obj (Nc
  N)

/-- Apply a coface to the ring factor of a balanced tensor. -/
noncomputable def push (c : R₂ A B ⟶ R₃ A B) : X₂ A B ⊗[B] N →ₗ[B] Xc c ⊗[B] N :=
  TensorProduct.lift (LinearMap.mk₂' B B
    (fun (x : X₂ A B) (n : N) => ((show Xc c from c.hom x) ⊗ₜ[B] n : Xc c ⊗[B] N))
    (fun (x y : X₂ A B) (n : N) => by
      dsimp only
      erw [map_add]
      exact TensorProduct.add_tmul _ _ _)
    (fun (b : B) (x : X₂ A B) (n : N) => by
      have hm : (show Xc c from c.hom (b • x)) = b • (show Xc c from c.hom x) :=
        map_mul c.hom ((i₂ A B).hom b) x
      exact (congrArg (fun z : Xc c => z ⊗ₜ[B] n) hm).trans
        (TensorProduct.smul_tmul' b (show Xc c from c.hom x) n).symm)
    (fun (x : X₂ A B) (n n' : N) => TensorProduct.tmul_add _ _ _)
    (fun (b : B) (x : X₂ A B) (n : N) =>
      TensorProduct.tmul_smul b (show Xc c from c.hom x) n))

omit [Module A N] [IsScalarTower A B N] in
theorem push_tmul (c : R₂ A B ⟶ R₃ A B) (x : B ⊗[A] B) (n : N) :
    push (A := A) N c ((show X₂ A B from x) ⊗ₜ[B] n : X₂ A B ⊗[B] N) =
      ((show Xc c from c.hom x) ⊗ₜ[B] n : Xc c ⊗[B] N) := by
  exact TensorProduct.lift.tmul (show X₂ A B from x) n

omit [Module A N] [IsScalarTower A B N] in
theorem esc_inv_one_tmul (c : R₂ A B ⟶ R₃ A B) (e : E₂ (A := A) N) :
    (ModuleCat.extendScalarsComp (i₂ A B).hom c.hom).inv.app (Nc N)
      ((1 : R₃ A B) ⊗ₜ[R₂ A B, c.hom] e :
        (ModuleCat.extendScalars c.hom).obj (E₂ (A := A) N)) = push (A := A) N c e := by
  induction e using TensorProduct.inductionOn with
  | add x y hx hy =>
    let H := (ModuleCat.extendScalarsComp (i₂ A B).hom c.hom).inv.app (Nc N)
    have ht := TensorProduct.tmul_add (R := R₂ A B) (N := E₂ (A := A) N)
      (show (ModuleCat.restrictScalars c.hom).obj (ModuleCat.of (R₃ A B) (R₃ A B))
        from (1 : R₃ A B)) x y
    exact (congrArg H ht).trans ((H.hom.map_add _ _).trans
      ((congrArg₂ (· + ·) hx hy).trans (map_add (push (A := A) N c) x y).symm))
  | tmul x n =>
    exact (esComp_inv_one_tmul_tmul (i₂ A B).hom c.hom (Nc N) x n).trans
      (push_tmul (A := A) N c x n).symm

omit [Module A N] [IsScalarTower A B N] in
theorem T_one_tmul (c : R₂ A B ⟶ R₃ A B) (φ' : E₁ (A := A) N ⟶ E₂ (A := A) N) (n : N) :
    T (Nc N) c φ' ((1 : R₃ A B) ⊗ₜ[B,(i₁ A B ≫ c).hom] n :
        (ModuleCat.extendScalars (i₁ A B ≫ c).hom).obj (Nc N)) =
      push (A := A) N c (φ' ((1 : R₂ A B) ⊗ₜ[B,(i₁ A B).hom] n : E₁ (A := A) N)) := by
  change (ModuleCat.extendScalarsComp (i₂ A B).hom c.hom).inv.app (Nc N)
    ((ModuleCat.extendScalars c.hom).map φ'
      ((ModuleCat.extendScalarsComp (i₁ A B).hom c.hom).hom.app (Nc N) _)) = _
  erw [esComp_hom_one_tmul (i₁ A B).hom c.hom (Nc N) n]
  erw [es_map_one_tmul c.hom φ']
  exact esc_inv_one_tmul (A := A) N c _

/-- Insert one in the second tensor factor. -/
noncomputable def ins₁ : B →ₗ[A] B ⊗[A] B := (TensorProduct.mk A B B).flip 1
/-- Insert one in the first tensor factor. -/
noncomputable def ins₂ : B →ₗ[A] B ⊗[A] B := TensorProduct.mk A B B 1

theorem ins₁_apply (b : B) : ins₁ (A := A) (B := B) b = b ⊗ₜ 1 := rfl
theorem ins₂_apply (b : B) : ins₂ (A := A) (B := B) b = 1 ⊗ₜ b := rfl

/-- Reassociate the tensor product and exchange the two ring factors. -/
noncomputable def σ : (N ⊗[A] B) ⊗[A] B ≃ₗ[A] N ⊗[A] (B ⊗[A] B) :=
  TensorProduct.assoc A N B B ≪≫ₗ LinearEquiv.lTensor N (TensorProduct.comm A B B)

omit [Module B N] [IsScalarTower A B N] in
theorem σ_tmul (m : N) (β' β : B) : σ (A := A) N ((m ⊗ₜ β') ⊗ₜ β) = m ⊗ₜ (β ⊗ₜ β') := rfl

theorem u₃_push₁₃ (e : E₂ (A := A) N) :
    u₃ (A := A) N (push (A := A) N (c₁₃ A B) e) = (ins₁ (A := A) (B := B)).lTensor N (u₂ (A := A) N
      e) := by
  induction e using TensorProduct.inductionOn with
  | add x y hx hy =>
    simp only [map_add]
    exact (map_add (u₃ (A := A) N) _ _).trans (congrArg₂ (· + ·) hx hy)
  | tmul x n =>
    revert n
    refine TensorProduct.inductionOn (motive := fun x : B ⊗[A] B => ∀ n : N,
      u₃ (A := A) N (push (A := A) N (c₁₃ A B) (x ⊗ₜ[B] n : X₂ A B ⊗[B] N)) =
        (ins₁ (A := A) (B := B)).lTensor N (u₂ (A := A) N (x ⊗ₜ[B] n : X₂ A B ⊗[B] N))) x ?_ ?_
    · intro b₁ b₂ n
      rw [push_tmul, c₁₃_tmul]
      erw [u₃_tmul]
      try rfl
    · intro x y hx hy n
      rw [show ((x + y : B ⊗[A] B) ⊗ₜ[B] n : X₂ A B ⊗[B] N) =
        (x ⊗ₜ[B] n : X₂ A B ⊗[B] N) + (y ⊗ₜ[B] n : X₂ A B ⊗[B] N) from TensorProduct.add_tmul _ _ n]
      simp only [map_add]
      exact (map_add (u₃ (A := A) N) _ _).trans (congrArg₂ (· + ·) (hx n) (hy n))

theorem u₃_push₂₃ (e : E₂ (A := A) N) :
    u₃ (A := A) N (push (A := A) N (c₂₃ A B) e) = (ins₂ (A := A) (B := B)).lTensor N (u₂ (A := A) N
      e) := by
  induction e using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul x n =>
    revert n
    refine TensorProduct.inductionOn (motive := fun x : B ⊗[A] B => ∀ n : N,
      u₃ (A := A) N (push (A := A) N (c₂₃ A B) (x ⊗ₜ[B] n : X₂ A B ⊗[B] N)) =
        (ins₂ (A := A) (B := B)).lTensor N (u₂ (A := A) N (x ⊗ₜ[B] n : X₂ A B ⊗[B] N))) x ?_ ?_
    · intro b₁ b₂ n
      rw [push_tmul, c₂₃_tmul]
      erw [u₃_tmul]
      try rfl
    · intro x y hx hy n
      rw [show ((x + y : B ⊗[A] B) ⊗ₜ[B] n : X₂ A B ⊗[B] N) =
        (x ⊗ₜ[B] n : X₂ A B ⊗[B] N) + (y ⊗ₜ[B] n : X₂ A B ⊗[B] N) from TensorProduct.add_tmul _ _ n]
      simp only [map_add, hx, hy]

theorem u₃_c₁₂_mul_tmul (x : B ⊗[A] B) (y : B ⊗[A] (B ⊗[A] B)) (n : N) :
    u₃ (A := A) N ((((c₁₂ A B).hom x) * y) ⊗ₜ[B] n : X₃ A B ⊗[B] N) =
      (LinearMap.mulLeft A x).lTensor N (u₃ (A := A) N (y ⊗ₜ[B] n : X₃ A B ⊗[B] N)) := by
  induction x using TensorProduct.inductionOn with
  | add x x' hx hx' =>
    rw [map_add, add_mul, show (((c₁₂ A B).hom x * y + (c₁₂ A B).hom x' * y : B ⊗[A] (B ⊗[A] B))
      ⊗ₜ[B] n :
      X₃ A B ⊗[B] N) = (((c₁₂ A B).hom x * y) ⊗ₜ[B] n : X₃ A B ⊗[B] N) +
        (((c₁₂ A B).hom x' * y) ⊗ₜ[B] n : X₃ A B ⊗[B] N) from TensorProduct.add_tmul _ _ n,
      map_add, hx, hx']
    rw [show LinearMap.mulLeft A (x + x') = LinearMap.mulLeft A x + LinearMap.mulLeft A x' from by
      ext; simp [add_mul], LinearMap.lTensor_add, LinearMap.add_apply]
  | tmul a₁ a₂ =>
    revert n
    refine TensorProduct.inductionOn (motive := fun y : B ⊗[A] (B ⊗[A] B) => ∀ n : N,
      u₃ (A := A) N ((((c₁₂ A B).hom (a₁ ⊗ₜ a₂)) * y) ⊗ₜ[B] n : X₃ A B ⊗[B] N) =
        (LinearMap.mulLeft A (a₁ ⊗ₜ[A] a₂)).lTensor N (u₃ (A := A) N (y ⊗ₜ[B] n : X₃ A B ⊗[B] N))) y
      ?_ ?_
    · intro b₁ z n
      revert n
      refine TensorProduct.inductionOn (motive := fun z : B ⊗[A] B => ∀ n : N,
        u₃ (A := A) N ((((c₁₂ A B).hom (a₁ ⊗ₜ a₂)) * (b₁ ⊗ₜ[A] z)) ⊗ₜ[B] n : X₃ A B ⊗[B] N) =
          (LinearMap.mulLeft A (a₁ ⊗ₜ[A] a₂)).lTensor N
            (u₃ (A := A) N ((b₁ ⊗ₜ[A] z) ⊗ₜ[B] n : X₃ A B ⊗[B] N))) z ?_ ?_
      · intro b₂ b₃ n
        rw [c₁₂_tmul, Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul,
          one_mul]
        erw [u₃_tmul, u₃_tmul]
        rw [LinearMap.lTensor_tmul, LinearMap.mulLeft_apply, Algebra.TensorProduct.tmul_mul_tmul]
      · intro z z' hz hz' n
        rw [TensorProduct.tmul_add, mul_add,
          show ((((c₁₂ A B).hom (a₁ ⊗ₜ a₂)) * (b₁ ⊗ₜ[A] z) + ((c₁₂ A B).hom (a₁ ⊗ₜ a₂)) * (b₁ ⊗ₜ[A]
            z') :
              B ⊗[A] (B ⊗[A] B)) ⊗ₜ[B] n : X₃ A B ⊗[B] N) =
            ((((c₁₂ A B).hom (a₁ ⊗ₜ a₂)) * (b₁ ⊗ₜ[A] z)) ⊗ₜ[B] n : X₃ A B ⊗[B] N) +
            ((((c₁₂ A B).hom (a₁ ⊗ₜ a₂)) * (b₁ ⊗ₜ[A] z')) ⊗ₜ[B] n : X₃ A B ⊗[B] N)
            from TensorProduct.add_tmul _ _ n,
          show (((b₁ ⊗ₜ[A] z + b₁ ⊗ₜ[A] z' : B ⊗[A] (B ⊗[A] B)) ⊗ₜ[B] n : X₃ A B ⊗[B] N)) =
            ((b₁ ⊗ₜ[A] z) ⊗ₜ[B] n : X₃ A B ⊗[B] N) + ((b₁ ⊗ₜ[A] z') ⊗ₜ[B] n : X₃ A B ⊗[B] N)
            from TensorProduct.add_tmul _ _ n]
        simp only [map_add, hz, hz']
    · intro y y' hy hy' n
      rw [mul_add, show ((((c₁₂ A B).hom (a₁ ⊗ₜ a₂)) * y + ((c₁₂ A B).hom (a₁ ⊗ₜ a₂)) * y' :
          B ⊗[A] (B ⊗[A] B)) ⊗ₜ[B] n : X₃ A B ⊗[B] N) =
        ((((c₁₂ A B).hom (a₁ ⊗ₜ a₂)) * y) ⊗ₜ[B] n : X₃ A B ⊗[B] N) +
          ((((c₁₂ A B).hom (a₁ ⊗ₜ a₂)) * y') ⊗ₜ[B] n : X₃ A B ⊗[B] N) from TensorProduct.add_tmul _
            _ n,
        show (((y + y' : B ⊗[A] (B ⊗[A] B)) ⊗ₜ[B] n : X₃ A B ⊗[B] N)) =
          (y ⊗ₜ[B] n : X₃ A B ⊗[B] N) + (y' ⊗ₜ[B] n : X₃ A B ⊗[B] N) from TensorProduct.add_tmul _
            _ n]
      simp only [map_add, hy, hy']

theorem u₃_c₁₂_smul (x : B ⊗[A] B) (f : X₃ A B ⊗[B] N) :
    u₃ (A := A) N (SMul.smul (M := R₃ A B) (α := F₃ (A := A) N) ((c₁₂ A B).hom x) f) =
      (LinearMap.mulLeft A x).lTensor N (u₃ (A := A) N f) := by
  induction f using TensorProduct.inductionOn with
  | add f g hf hg =>
    have hs := smul_add ((c₁₂ A B).hom x) (show F₃ (A := A) N from f)
      (show F₃ (A := A) N from g)
    exact (congrArg (u₃ (A := A) N) hs).trans ((map_add (u₃ (A := A) N) _ _).trans
      ((congrArg₂ (· + ·) hf hg).trans
        ((map_add (LinearMap.lTensor N (LinearMap.mulLeft A x)) _ _).symm.trans
          (congrArg (LinearMap.lTensor N (LinearMap.mulLeft A x))
            (map_add (u₃ (A := A) N) f g).symm))))
  | tmul y n =>
    exact (congrArg (u₃ (A := A) N)
      (ModuleCat.ExtendScalars.smul_tmul (i₂ A B ≫ c₂₃ A B).hom
        (M := Nc N) ((c₁₂ A B).hom x) y n)).trans
          (u₃_c₁₂_mul_tmul (A := A) N x y n)

end Dictionary

section Core

open ChangeOfRings

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
  (N : Type u) [AddCommGroup N] [Module B N] [Module A N] [IsScalarTower A B N]
  (φ' : E₁ (A := A) (B := B) N ⟶ E₂ (A := A) (B := B) N)

/-- Apply the descent morphism to a unit tensor. -/
noncomputable def δ (n : N) : E₂ (A := A) (B := B) N := φ' ((1 : R₂ A B) ⊗ₜ[B,(i₁ A B).hom] n : E₁
  (A := A) (B := B) N)

omit [Module A N] [IsScalarTower A B N] in
theorem δ_add (n n' : N) : δ N φ' (n + n') = δ N φ' n + δ N φ' n' := by
  exact (congrArg φ' (TensorProduct.tmul_add (show X₁ A B from (1 : R₂ A B))
    (show Nc N from n) (show Nc N from n'))).trans (φ'.hom.map_add _ _)

omit [Module A N] [IsScalarTower A B N] in
theorem one_tmul_smul_E₁ (b : B) (n : N) :
    ((1 : R₂ A B) ⊗ₜ[B,(i₁ A B).hom] (b • n) : E₁ (A := A) (B := B) N) =
      SMul.smul (M := R₂ A B) (α := E₁ (A := A) (B := B) N)
        ((i₁ A B).hom b) ((1 : R₂ A B) ⊗ₜ[B,(i₁ A B).hom] n) := by
  exact es_one_tmul_smul (i₁ A B).hom (Nc N) b n

omit [Module A N] [IsScalarTower A B N] in
theorem one_tmul_smul_E₂ (b : B) (n : N) :
    ((1 : R₂ A B) ⊗ₜ[B,(i₂ A B).hom] (b • n) : E₂ (A := A) (B := B) N) =
      SMul.smul (M := R₂ A B) (α := E₂ (A := A) (B := B) N)
        ((i₂ A B).hom b) ((1 : R₂ A B) ⊗ₜ[B,(i₂ A B).hom] n) := by
  exact es_one_tmul_smul (i₂ A B).hom (Nc N) b n

omit [Module A N] [IsScalarTower A B N] in
theorem δ_smul (b : B) (n : N) : δ N φ' (b • n) = ((i₁ A B).hom b) • δ N φ' n := by
  exact (congrArg φ' (one_tmul_smul_E₁ (A := A) N b n)).trans
    (φ'.hom.map_smul ((i₁ A B).hom b) _)

theorem u₂_i₁_smul (b : B) (e : E₂ (A := A) (B := B) N) :
    u₂ (A := A) N (SMul.smul (M := R₂ A B) (α := E₂ (A := A) (B := B) N) ((i₁ A B).hom b) e) =
      (LinearMap.mulLeft A b).lTensor N (u₂ (A := A) N e) := by
  induction e using TensorProduct.inductionOn with
  | add x y hx hy =>
    have hs := smul_add (A := E₂ (A := A) (B := B) N) ((i₁ A B).hom b) (show E₂ (A := A) N from x)
      (show E₂ (A := A) N from y)
    exact (congrArg (u₂ (A := A) N) hs).trans ((map_add (u₂ (A := A) N) _ _).trans
      ((congrArg₂ (· + ·) hx hy).trans
        ((map_add (LinearMap.lTensor N (LinearMap.mulLeft A b)) _ _).symm.trans
          (congrArg (LinearMap.lTensor N (LinearMap.mulLeft A b))
            (map_add (u₂ (A := A) N) x y).symm))))
  | tmul x n =>
    revert n
    refine TensorProduct.inductionOn (motive := fun x : B ⊗[A] B => ∀ n : N,
      u₂ (A := A) N (SMul.smul (M := R₂ A B) (α := E₂ (A := A) (B := B) N) ((i₁ A B).hom b) ((x
        ⊗ₜ[B] n : X₂ A B ⊗[B] N) : E₂ (A := A) (B := B) N)) =
        (LinearMap.mulLeft A b).lTensor N (u₂ (A := A) N (x ⊗ₜ[B] n : X₂ A B ⊗[B] N))) x ?_ ?_
    · intro b₁ b₂ n
      rw [show (SMul.smul (M := R₂ A B) (α := E₂ (A := A) (B := B) N) ((i₁ A B).hom b) (((b₁ ⊗ₜ[A]
        b₂) ⊗ₜ[B] n : X₂ A B ⊗[B] N) : E₂ (A := A) (B := B)
        N)) =
          ((((i₁ A B).hom b) * (b₁ ⊗ₜ[A] b₂)) ⊗ₜ[B] n : X₂ A B ⊗[B] N) from
            ModuleCat.ExtendScalars.smul_tmul (i₂ A B).hom (M := Nc N)
              ((i₁ A B).hom b) (b₁ ⊗ₜ[A] b₂) n,
        i₁_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
      erw [u₂_tmul]
      try rfl
    · intro x y hx hy n
      rw [show ((x + y : B ⊗[A] B) ⊗ₜ[B] n : X₂ A B ⊗[B] N) =
          (x ⊗ₜ[B] n : X₂ A B ⊗[B] N) + (y ⊗ₜ[B] n : X₂ A B ⊗[B] N) from TensorProduct.add_tmul _ _
            n]
      simp only [map_add]
      have hs := smul_add (A := E₂ (A := A) (B := B) N) ((i₁ A B).hom b)
        (x ⊗ₜ[B,(i₂ A B).hom] (show Nc N from n) : E₂ (A := A) N)
        (y ⊗ₜ[B,(i₂ A B).hom] (show Nc N from n) : E₂ (A := A) N)
      exact (congrArg (u₂ (A := A) N) hs).trans
        ((map_add (u₂ (A := A) N) _ _).trans (congrArg₂ (· + ·) (hx n) (hy n)))

theorem u₂_one_tmul (n : N) : u₂ (A := A) N ((1 : B ⊗[A] B) ⊗ₜ[B] n : X₂ A B ⊗[B] N) = n ⊗ₜ 1 := by
  rw [Algebra.TensorProduct.one_def]
  erw [u₂_tmul]
  rw [one_smul]

theorem u₁_one_tmul (n : N) : u₁ (A := A) N ((1 : B ⊗[A] B) ⊗ₜ[B] n : X₁ A B ⊗[B] N) = n ⊗ₜ 1 := by
  rw [Algebra.TensorProduct.one_def]
  erw [u₁_tmul]
  rw [one_smul]

omit [Module B N] [IsScalarTower A B N] in
theorem lTensor_mulLeft_algebraMap (a : A) (z : N ⊗[A] B) :
    (LinearMap.mulLeft A (algebraMap A B a)).lTensor N z = a • z := by
  induction z using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, smul_add, hx, hy]
  | tmul m β =>
      rw [LinearMap.lTensor_tmul, LinearMap.mulLeft_apply, ← Algebra.smul_def,
        TensorProduct.tmul_smul]

/-- Express the descent coaction in the module-first tensor product. -/
noncomputable def δ₂ : N →ₗ[A] N ⊗[A] B where
  toFun n := u₂ (A := A) N (δ N φ' n)
  map_add' n n' := (congrArg (u₂ (A := A) N) (δ_add N φ' n n')).trans
    (map_add (u₂ (A := A) N) _ _)
  map_smul' a n := by
    rw [RingHom.id_apply, ← IsScalarTower.algebraMap_smul B a n]
    exact (congrArg (u₂ (A := A) N) (δ_smul N φ' (algebraMap A B a) n)).trans
      ((u₂_i₁_smul (A := A) N (algebraMap A B a) (δ N φ' n)).trans
        (lTensor_mulLeft_algebraMap (A := A) N a _))

theorem δ₂_apply (n : N) : δ₂ N φ' n = u₂ (A := A) N (δ N φ' n) := rfl

/-- The unit-insertion map in the module-first tensor product. -/
noncomputable def ι₂ : N →ₗ[A] N ⊗[A] B := (TensorProduct.mk A N B).flip 1

omit [Module B N] [IsScalarTower A B N] in
theorem ι₂_apply (n : N) : ι₂ (A := A) (B := B) N n = n ⊗ₜ 1 := rfl

/-- The equalizer submodule fixed by the descent coaction. -/
noncomputable def Msub : Submodule A N where
  carrier := {n | δ N φ' n = ((1 : R₂ A B) ⊗ₜ[B,(i₂ A B).hom] n : E₂ (A := A) (B := B) N)}
  add_mem' {n n'} hn hn' := by
    change δ N φ' (n + n') = _
    exact (δ_add N φ' n n').trans ((congrArg₂ (· + ·) hn hn').trans
      (TensorProduct.tmul_add (show X₂ A B from (1 : R₂ A B))
        (show Nc N from n) (show Nc N from n')).symm)
  zero_mem' := by
    change δ N φ' 0 = _
    exact ((congrArg φ' (TensorProduct.tmul_zero (R := B) (Nc N) (show X₁ A B from (1 : R₂ A
      B)))).trans
      (map_zero φ'.hom)).trans
        (TensorProduct.tmul_zero (R := B) (Nc N) (show X₂ A B from (1 : R₂ A B))).symm
  smul_mem' a n hn := by
    change δ N φ' (a • n) = ((1 : R₂ A B) ⊗ₜ[B,(i₂ A B).hom] (a • n) : E₂ (A := A) (B := B) N)
    rw [← IsScalarTower.algebraMap_smul B a n, δ_smul, hn, one_tmul_smul_E₂]
    congr 1
    exact congrArg (fun f : CommRingCat.of A ⟶ R₂ A B => f.hom a) (algebraMap_i₁_eq_i₂ A B)

theorem mem_Msub_iff (n : N) :
    n ∈ Msub N φ' ↔ φ' ((1 : R₂ A B) ⊗ₜ[B,(i₁ A B).hom] n : E₁ (A := A) (B := B) N) = ((1 : R₂ A
      B) ⊗ₜ[B,(i₂ A B).hom] n : E₂ (A := A) (B := B) N) :=
  Iff.rfl

theorem δ₂_of_mem {m : N} (hm : m ∈ Msub N φ') : δ₂ N φ' m = m ⊗ₜ 1 := by
  exact (congrArg (u₂ (A := A) N) hm).trans (u₂_one_tmul (A := A) N m)

theorem δ₂_smul_of_mem {m : N} (hm : m ∈ Msub N φ') (b : B) : δ₂ N φ' (b • m) = m ⊗ₜ b := by
  refine (congrArg (u₂ (A := A) N) (δ_smul N φ' b m)).trans ?_
  refine (u₂_i₁_smul (A := A) N b (δ N φ' m)).trans ?_
  refine (congrArg ((LinearMap.mulLeft A b).lTensor N) (δ₂_of_mem N φ' hm)).trans ?_
  rw [LinearMap.lTensor_tmul, LinearMap.mulLeft_apply, mul_one]

omit [Module B N] [IsScalarTower A B N] in
theorem aux₁ (b₁ b₂ : B) (z : N ⊗[A] B) :
    (LinearMap.mulLeft A (b₁ ⊗ₜ[A] b₂) ∘ₗ ins₂ (A := A) (B := B)).lTensor N z =
      σ (A := A) N (((LinearMap.mulLeft A b₂).lTensor N z) ⊗ₜ b₁) := by
  induction z using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, TensorProduct.add_tmul, hx, hy]
  | tmul m β =>
    rw [LinearMap.lTensor_tmul, LinearMap.lTensor_tmul, LinearMap.comp_apply, ins₂_apply,
      LinearMap.mulLeft_apply, LinearMap.mulLeft_apply, Algebra.TensorProduct.tmul_mul_tmul,
        mul_one, σ_tmul]

omit [Module B N] [IsScalarTower A B N] in
theorem aux₂ (z : N ⊗[A] B) :
    (ins₁ (A := A) (B := B)).lTensor N z = σ (A := A) N ((ι₂ (A := A) (B := B) N).rTensor B z) := by
  induction z using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul m β => rw [LinearMap.lTensor_tmul, LinearMap.rTensor_tmul, ins₁_apply, ι₂_apply, σ_tmul]

omit [Module A N] [IsScalarTower A B N] in
theorem T_tmul (c : R₂ A B ⟶ R₃ A B) (y : B ⊗[A] (B ⊗[A] B)) (n : N) :
    T (Nc N) c φ'
      (y ⊗ₜ[B,(i₁ A B ≫ c).hom] n : (ModuleCat.extendScalars (i₁ A B ≫ c).hom).obj (Nc N)) =
      SMul.smul (M := R₃ A B) (α := Fc (A := A) N c) y
        (push (A := A) N c (φ' ((1 : R₂ A B) ⊗ₜ[B,(i₁ A B).hom] n))) := by
  have hy := (ModuleCat.ExtendScalars.smul_tmul (i₁ A B ≫ c).hom (M := Nc N) y 1 n).trans
    (congrArg (fun z : R₃ A B => z ⊗ₜ[B,(i₁ A B ≫ c).hom] (show Nc N from n)) (mul_one y))
  exact (congrArg (T (Nc N) c φ') hy.symm).trans
    (((T (Nc N) c φ').hom.map_smul y _).trans
      (congrArg (fun z : Fc (A := A) N c => y • z) (T_one_tmul N c φ' n)))

theorem u₃_T₂₃_push₁₂ (e : E₂ (A := A) (B := B) N) :
    u₃ (A := A) N (T (Nc N) (c₂₃ A B) φ' (push (A := A) N (c₁₂ A B) e)) =
      σ (A := A) N ((δ₂ N φ').rTensor B (u₂ (A := A) N e)) := by
  induction e using TensorProduct.inductionOn with
  | add x y hx hy =>
    simp only [map_add]
    exact (congrArg (u₃ (A := A) N) ((T (Nc N) (c₂₃ A B) φ').hom.map_add _ _)).trans
      ((map_add (u₃ (A := A) N) _ _).trans (congrArg₂ (· + ·) hx hy))
  | tmul x n =>
    revert n
    refine TensorProduct.inductionOn (motive := fun x : B ⊗[A] B => ∀ n : N,
      u₃ (A := A) N (T (Nc N) (c₂₃ A B) φ' (push (A := A) N (c₁₂ A B) (x ⊗ₜ[B] n : X₂ A B ⊗[B] N)))
        =
        σ (A := A) N ((δ₂ N φ').rTensor B (u₂ (A := A) N (x ⊗ₜ[B] n : X₂ A B ⊗[B] N)))) x ?_ ?_
    · intro b₁ b₂ n
      rw [push_tmul]
      erw [T_tmul N φ' (c₂₃ A B) ((c₁₂ A B).hom (b₁ ⊗ₜ[A] b₂)) n]
      erw [u₃_c₁₂_smul (A := A) N (b₁ ⊗ₜ[A] b₂)]
      rw [u₃_push₂₃]
      erw [u₂_tmul]
      rw [LinearMap.rTensor_tmul, show δ₂ N φ' (b₂ • n) = (LinearMap.mulLeft A b₂).lTensor N (δ₂ N
        φ' n) from by
          exact (congrArg (u₂ (A := A) N) (δ_smul N φ' b₂ n)).trans
            (u₂_i₁_smul (A := A) N b₂ (δ N φ' n)), ← aux₁, LinearMap.lTensor_comp,
            LinearMap.comp_apply]
      rfl
    · intro x y hx hy n
      rw [show ((x + y : B ⊗[A] B) ⊗ₜ[B] n : X₂ A B ⊗[B] N) =
          (x ⊗ₜ[B] n : X₂ A B ⊗[B] N) + (y ⊗ₜ[B] n : X₂ A B ⊗[B] N) from TensorProduct.add_tmul _ _
            n]
      simp only [map_add]
      exact (congrArg (u₃ (A := A) N) ((T (Nc N) (c₂₃ A B) φ').hom.map_add _ _)).trans
        ((map_add (u₃ (A := A) N) _ _).trans (congrArg₂ (· + ·) (hx n) (hy n)))

theorem u₃_push₁₃' (e : E₂ (A := A) (B := B) N) :
    u₃ (A := A) N (push (A := A) N (c₁₃ A B) e) = σ (A := A) N ((ι₂ (A := A) (B := B) N).rTensor B
      (u₂ (A := A) N e)) := by
  rw [u₃_push₁₃, aux₂]

theorem coassoc (hcoc : Cocycle (Nc N) φ') (n : N) :
    (δ₂ N φ').rTensor B (δ₂ N φ' n) = (ι₂ (A := A) (B := B) N).rTensor B (δ₂ N φ' n) := by
  apply (σ (A := A) (B := B) N).injective
  rw [δ₂_apply, ← u₃_T₂₃_push₁₂, ← u₃_push₁₃']
  unfold δ
  rw [← T_one_tmul N (c₁₂ A B) φ' n, ← T_one_tmul N (c₁₃ A B) φ' n]
  exact congrArg (fun f :
    (ModuleCat.extendScalars (i₁ A B ≫ c₁₂ A B).hom).obj (Nc N) ⟶
      (ModuleCat.extendScalars (i₂ A B ≫ c₂₃ A B).hom).obj (Nc N) =>
        u₃ (A := A) N (f ((1 : R₃ A B) ⊗ₜ[B,(i₁ A B ≫ c₁₂ A B).hom] n))) hcoc

omit [Module B N] [IsScalarTower A B N] in
theorem tmul_one_injective [Module.FaithfullyFlat A B] :
    Function.Injective (fun n : N => n ⊗ₜ[A] (1 : B)) := by
  let g : N →ₗ[A] N ⊗[A] B := (TensorProduct.mk A N B).flip 1
  have hg : ⇑g = fun n : N => n ⊗ₜ[A] (1 : B) := rfl
  rw [← hg]
  let r : B ⊗[A] (N ⊗[A] B) →ₗ[A] B ⊗[A] N :=
    (LinearMap.mul' A B).rTensor N ∘ₗ (TensorProduct.assoc A B B N).symm.toLinearMap ∘ₗ
      (TensorProduct.comm A N B).toLinearMap.lTensor B
  have hr : ∀ z, r (g.lTensor B z) = z := by
    intro z
    induction z using TensorProduct.inductionOn with
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul b n => simp [r, g]
  have hinj : Function.Injective (g.lTensor B) := Function.LeftInverse.injective hr
  exact (Module.FaithfullyFlat.lTensor_injective_iff_injective A B g).mp hinj

omit [Module B N] [IsScalarTower A B N] in
theorem lTensor_comm_comp (f : N →ₗ[A] N ⊗[A] B) (z : N ⊗[A] B) :
    ((TensorProduct.comm A N B).toLinearMap ∘ₗ f).lTensor B (TensorProduct.comm A N B z) =
      (TensorProduct.comm A N B).toLinearMap.lTensor B
        (TensorProduct.comm A (N ⊗[A] B) B (f.rTensor B z)) := by
  induction z using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul m β => simp [LinearMap.lTensor_tmul, LinearMap.rTensor_tmul]

/-- Express the descent coaction in the ring-first tensor product. -/
noncomputable abbrev δt : N →ₗ[A] B ⊗[A] N := (TensorProduct.comm A N B).toLinearMap ∘ₗ δ₂ N φ'
/-- The unit-insertion map in the ring-first tensor product. -/
noncomputable abbrev ιt : N →ₗ[A] B ⊗[A] N := (TensorProduct.comm A N B).toLinearMap ∘ₗ ι₂ (A := A)
  (B := B) N

omit [Module B N] [IsScalarTower A B N] in
theorem ιt_apply (n : N) : ιt (A := A) (B := B) N n = (1 : B) ⊗ₜ n := rfl

theorem Msub_eq : Msub N φ' = LinearMap.eqLocus (δt N φ') (ιt (A := A) (B := B) N) := by
  ext n
  rw [mem_Msub_iff, LinearMap.mem_eqLocus]
  change _ ↔ TensorProduct.comm A N B (u₂ (A := A) N (δ N φ' n)) =
    TensorProduct.comm A N B (ι₂ (A := A) (B := B) N n)
  constructor
  · intro h
    exact congrArg (TensorProduct.comm A N B)
      ((congrArg (u₂ (A := A) N) h).trans (u₂_one_tmul (A := A) N n))
  · intro h
    exact u₂_injective (A := A) N
      (((TensorProduct.comm A N B).injective h).trans (u₂_one_tmul (A := A) N n).symm)

theorem lTensor_δt_δt (hcoc : Cocycle (Nc N) φ') (n : N) :
    (δt N φ').lTensor B (δt N φ' n) = (ιt (A := A) (B := B) N).lTensor B (δt N φ' n) := by
  change (δt N φ').lTensor B (TensorProduct.comm A N B (δ₂ N φ' n)) =
    (ιt (A := A) (B := B) N).lTensor B (TensorProduct.comm A N B (δ₂ N φ' n))
  rw [lTensor_comm_comp, lTensor_comm_comp, coassoc N φ' hcoc n]

theorem δt_smul_of_mem {m : N} (hm : m ∈ Msub N φ') (b : B) : δt N φ' (b • m) = b ⊗ₜ m := by
  change TensorProduct.comm A N B (δ₂ N φ' (b • m)) = _
  rw [δ₂_smul_of_mem N φ' hm, TensorProduct.comm_tmul]

theorem δ_injective [Module.FaithfullyFlat A B] (hφ : Function.Injective φ') : Function.Injective
  (δ N φ') := by
  intro n n' h
  have h' := congrArg (u₁ (A := A) N) (hφ h)
  exact tmul_one_injective (A := A) (B := B) N
    ((u₁_one_tmul (A := A) N n).symm.trans (h'.trans (u₁_one_tmul (A := A) N n')))

theorem δt_injective [Module.FaithfullyFlat A B] (hφ : Function.Injective φ') :
    Function.Injective (δt N φ') :=
  (TensorProduct.comm A N B).injective.comp ((u₂_injective (A := A) N).comp (δ_injective N φ' hφ))

theorem liftBaseChange_bijective [Module.FaithfullyFlat A B] (hφ : Function.Injective φ')
    (hcoc : Cocycle (Nc N) φ') :
    Function.Bijective ((Msub N φ').subtype.liftBaseChange B) := by
  have hM := Msub_eq N φ'
  let M := Msub N φ'
  let θ : B ⊗[A] M →ₗ[B] N := M.subtype.liftBaseChange B
  let κ : B ⊗[A] M →ₗ[A] B ⊗[A] N := M.subtype.lTensor B
  have hδθ : ∀ y, δt N φ' (θ y) = κ y := by
    intro y
    induction y using TensorProduct.inductionOn with
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul b m =>
      simp only [θ, κ, LinearMap.liftBaseChange_tmul, LinearMap.lTensor_tmul,
        Submodule.subtype_apply]
      exact δt_smul_of_mem N φ' m.2 b
  have hκ : Function.Injective κ :=
    Module.Flat.lTensor_preserves_injective_linearMap _ M.injective_subtype
  have hδ : Function.Injective (δt N φ') := δt_injective N φ' hφ
  change Function.Bijective θ
  constructor
  · intro y₁ y₂ h
    apply hκ
    rw [← hδθ, ← hδθ, h]
  · intro n
    have hmem : δt N φ' n ∈ LinearMap.eqLocus (TensorProduct.AlgebraTensorModule.lTensor A B (δt N
      φ'))
        (TensorProduct.AlgebraTensorModule.lTensor A B (ιt (A := A) (B := B) N)) := by
      change TensorProduct.AlgebraTensorModule.lTensor A B (δt N φ') (δt N φ' n) =
        TensorProduct.AlgebraTensorModule.lTensor A B (ιt (A := A) (B := B) N) (δt N φ' n)
      have := lTensor_δt_δt N φ' hcoc n
      convert this using 1 <;> rfl
    rw [Module.Flat.eqLocus_lTensor_eq, ← hM] at hmem
    obtain ⟨y, hy⟩ := hmem
    refine ⟨y, hδ ?_⟩
    rw [hδθ]
    convert hy using 1
    rfl

theorem isBaseChange_Msub [Module.FaithfullyFlat A B] (hφ : Function.Injective φ')
    (hcoc : Cocycle (Nc N) φ') :
    IsBaseChange B (Msub N φ').subtype := by
  refine IsBaseChange.of_equiv
    (LinearEquiv.ofBijective _ (liftBaseChange_bijective N φ' hφ hcoc)) fun m => ?_
  change (Msub N φ').subtype.liftBaseChange B ((1 : B) ⊗ₜ[A] m) = (m : N)
  erw [LinearMap.liftBaseChange_tmul]
  simp

/-- The extension ring with its original base-ring action via restriction of scalars. -/
noncomputable abbrev XB (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] :=
  ↑((ModuleCat.restrictScalars (algebraMap A B)).obj (ModuleCat.of B B))

/-- Identify the restricted scalar carrier with the original algebra. -/
noncomputable def idXB (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] : XB A B ≃ₗ[A] B where
  toFun x := (x : B)
  invFun b := b
  map_add' _ _ := rfl
  map_smul' a x := by
    change algebraMap A B a * (show B from x) = a • (show B from x)
    exact (Algebra.smul_def a (show B from x)).symm
  left_inv _ := rfl
  right_inv _ := rfl

variable (M : Submodule A N)

/-- The scalar extension of the candidate descended submodule. -/
noncomputable abbrev EM := (ModuleCat.extendScalars (algebraMap A B)).obj (ModuleCat.of A M)

/-- The submodule inclusion as a morphism into the restricted module. -/
noncomputable def incl :
    ModuleCat.of A M ⟶ (ModuleCat.restrictScalars (algebraMap A B)).obj (Nc N) :=
  ModuleCat.ofHom (Y := (ModuleCat.restrictScalars (algebraMap A B)).obj (Nc N))
    { toFun := fun m => (m : N)
      map_add' := fun _ _ => rfl
      map_smul' := fun a m => by
        change ((a • m : M) : N) = (algebraMap A B a) • (m : N)
        rw [Submodule.coe_smul, algebraMap_smul] }

/-- The scalar-extended submodule inclusion obtained from the extension-restriction adjunction. -/
noncomputable def θh : EM (A := A) (B := B) N M ⟶ Nc N :=
  ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars (algebraMap A B) (incl N M)

theorem θh_tmul (b : B) (m : M) :
    θh N M ((b ⊗ₜ[A, algebraMap A B] m : EM (A := A) (B := B) N M)) = b • (m : N) := by
  rfl

theorem θh_eq (z : EM (A := A) (B := B) N M) :
    θh N M z = M.subtype.liftBaseChange B (TensorProduct.congr (idXB A B) (LinearEquiv.refl A M) z)
      := by
  induction z using TensorProduct.inductionOn with
  | add x y hx hy =>
    exact ((θh N M).hom.map_add x y).trans ((congrArg₂ (· + ·) hx hy).trans
      ((map_add (M.subtype.liftBaseChange B) _ _).symm.trans
        (congrArg (M.subtype.liftBaseChange B)
          (map_add (TensorProduct.congr (idXB A B) (LinearEquiv.refl A M)) x y).symm)))
  | tmul x m =>
    rw [TensorProduct.congr_tmul, LinearEquiv.refl_apply, LinearMap.liftBaseChange_tmul]
    erw [θh_tmul]
    rfl

theorem θh_bijective [Module.FaithfullyFlat A B] (hφ : Function.Injective φ')
    (hcoc : Cocycle (Nc N) φ') :
    Function.Bijective (θh (B := B) N (Msub N φ')) := by
  have h := (liftBaseChange_bijective N φ' hφ hcoc).comp
    (TensorProduct.congr (idXB A B) (LinearEquiv.refl A (Msub (B := B) N φ')) :
      XB A B ⊗[A] (Msub (B := B) N φ') ≃ₗ[A] B ⊗[A] (Msub (B := B) N φ')).bijective
  have e : (θh (B := B) N (Msub N φ') : EM N (Msub N φ') → Nc N) =
      (Msub N φ').subtype.liftBaseChange B ∘
        (TensorProduct.congr (idXB A B) (LinearEquiv.refl A (Msub (B := B) N φ')) :
          XB A B ⊗[A] (Msub (B := B) N φ') ≃ₗ[A] B ⊗[A] (Msub (B := B) N φ')) :=
    funext fun z => θh_eq (B := B) N (Msub N φ') z
  rw [e]
  exact h

theorem isIso_θh [Module.FaithfullyFlat A B] (hφ : Function.Injective φ')
    (hcoc : Cocycle (Nc N) φ') :
    IsIso (θh (B := B) N (Msub N φ')) := by
  have : IsIso ((forget (ModuleCat.{u} B)).map (θh (B := B) N (Msub N φ'))) :=
    (isIso_iff_bijective _).mpr (θh_bijective N φ' hφ hcoc)
  exact isIso_of_reflects_iso _ (forget (ModuleCat.{u} B))

theorem square (hM : ∀ m ∈ M,
    δ N φ' m = ((1 : R₂ A B) ⊗ₜ[B,(i₂ A B).hom] m : E₂ (A := A) (B := B) N)) :
    (ModuleCat.extendScalars (i₁ A B).hom).map (θh N M) ≫ φ' =
      canonical A B (ModuleCat.of A M) ≫ (ModuleCat.extendScalars (i₂ A B).hom).map (θh N M) := by
  apply comparison_square (algebraMap A B) (i₁ A B).hom (i₂ A B).hom
    (i₁_comp_algebraMap_eq A B) (ModuleCat.of A M) (Nc N) (θh N M) φ'
  intro m
  have ht : θh N M ((1 : B) ⊗ₜ[A, algebraMap A B] m : EM (A := A) (B := B) N M) =
      (m : N) := (θh_tmul N M 1 m).trans (one_smul B (m : N))
  exact (congrArg (fun z : Nc N => φ' ((1 : R₂ A B) ⊗ₜ[B,(i₁ A B).hom] z)) ht).trans
    ((hM m m.2).trans
      (congrArg (fun z : Nc N => ((1 : R₂ A B) ⊗ₜ[B,(i₂ A B).hom] z : E₂ (A := A) N))
        ht.symm))

end Core

end S17C1

open S17C1 in
theorem _root_.Module.FaithfullyFlat.exists_submodule_isBaseChange_of_cocycle
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] [Module.FaithfullyFlat A B]
    (N : Type u) [AddCommGroup N] [Module B N] [Module A N] [IsScalarTower A B N]
    (φ' : (ModuleCat.extendScalars (i₁ A B).hom).obj (ModuleCat.of B N) ≅
      (ModuleCat.extendScalars (i₂ A B).hom).obj (ModuleCat.of B N))
    (hcocycle : Cocycle (ModuleCat.of B N) φ'.hom) :
    ∃ M : Submodule A N,
      (∀ n : N, n ∈ M ↔
        φ'.hom (((1 : B ⊗[A] B) ⊗ₜ[B] n : (ModuleCat.extendScalars (i₁ A B).hom).obj (ModuleCat.of
          B N))) =
          ((1 : B ⊗[A] B) ⊗ₜ[B] n : (ModuleCat.extendScalars (i₂ A B).hom).obj (ModuleCat.of B N)))
            ∧
      IsBaseChange B M.subtype ∧
      (∃ θ : (ModuleCat.extendScalars (algebraMap A B)).obj (ModuleCat.of A M) ≅ ModuleCat.of B N,
        (∀ (b : B) (m : M),
          θ.hom ((b ⊗ₜ[A] m : (ModuleCat.extendScalars (algebraMap A B)).obj (ModuleCat.of A M))) =
            b • (m : N)) ∧
        (ModuleCat.extendScalars (i₁ A B).hom).map θ.hom ≫ φ'.hom =
          canonical A B (ModuleCat.of A M) ≫ (ModuleCat.extendScalars (i₂ A B).hom).map θ.hom) ∧
      (Module.Invertible B N → Module.Invertible A M) := by
  have hφ : Function.Injective φ'.hom := by
    intro x y h
    have := congrArg φ'.inv h
    simpa using this
  have := isIso_θh N φ'.hom hφ hcocycle
  refine ⟨Msub N φ'.hom, mem_Msub_iff N φ'.hom, isBaseChange_Msub N φ'.hom hφ hcocycle,
    ⟨asIso (θh (B := B) N (Msub N φ'.hom)), fun b m => θh_tmul N (Msub N φ'.hom) b m,
      square N φ'.hom (Msub N φ'.hom) fun m hm => hm⟩, fun _ => ?_⟩
  have : Module.Invertible B (B ⊗[A] (Msub N φ'.hom)) :=
    Module.Invertible.congr (isBaseChange_Msub N φ'.hom hφ hcocycle).equiv.symm
  exact Module.Invertible.of_invertible_tensorProduct_of_faithfullyFlat (R := A) B (M := Msub N
    φ'.hom)
end AlgebraicCurves.Foundations.Algebra.Proofs.FaithfullyFlatDescent
end ProofImplementation
