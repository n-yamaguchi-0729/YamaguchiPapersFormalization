/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_ProjSpace_exists_hom_twist_val_eq_mul_and_injective_of_cocycle.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.Algebra.GroupWithZero.NonZeroDivisors
import Mathlib.Algebra.Module.Submodule.Ker
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Scheme
import Mathlib.RingTheory.Localization.Defs
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Topology.Sheaves.CommRingCat
import Mathlib.Topology.Sheaves.Stalks
import Mathlib.Tactic.Ring
import Nyll.SchemeTheory.ProjectiveSpace.Basic
import Nyll.SchemeTheory.ProjectiveSpace.Cover
import Nyll.AlgebraicCurves.Geometry.Projective.ProjTwistDatum
import Nyll.SchemeTheory.Cohomology.Sheaves.OModulePresheafHom

/-!
# Proj Space exists hom twist val eq mul and injective of cocycle
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Projective.Proofs
namespace ProjSpace_exists_hom_twist_val_eq_mul_and_injective_of_cocycle

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

namespace P2mTwistMulSol


open _root_.AlgebraicGeometry.ProjSpace
open _root_.AlgebraicGeometry.OModulePresheaf


theorem eq_zero_of_restrict_mul_eq_zero {X : Scheme.{u}} {U : X.Opens} (hU : IsAffineOpen U) (t :
  Γ(X, U))
    (ht : ∀ y : Γ(X, U), t * y = 0 → y = 0) {V : X.Opens} (hV : V ≤ U) (g : Γ(X, V))
    (hg : (X.presheaf.map (homOfLE hV).op).hom t * g = 0) : g = 0 := by
  refine TopCat.Presheaf.section_ext X.sheaf V g 0 fun x hx => ?_
  rw [map_zero]
  let := X.presheaf.algebra_section_stalk (⟨x, hV hx⟩ : U)
  have hloc := hU.isLocalization_stalk ⟨x, hV hx⟩
  have htn : t ∈ nonZeroDivisors Γ(X, U) := by
    rw [mem_nonZeroDivisors_iff]
    exact ⟨fun y hy => ht y hy, fun y hy => ht y (by rw [mul_comm]; exact hy)⟩
  have hmem := IsLocalization.nonZeroDivisors_le_comap ((hU.primeIdealOf ⟨x, hV
    hx⟩).asIdeal.primeCompl)
    (X.presheaf.stalk x) htn
  rw [Submonoid.mem_comap, mem_nonZeroDivisors_iff] at hmem
  refine hmem.1 _ ?_
  have h2 := congrArg (fun s => (X.presheaf.germ V x hx).hom s) hg
  simp only [map_mul, map_zero] at h2
  rw [TopCat.Presheaf.germ_res_apply X.presheaf (homOfLE hV) x hx] at h2
  exact h2

section Mul

variable {A : Type u} [CommRing A] {N : ℕ} {Z : Scheme.{u}}
  (π : Z ⟶ Spec (.of A)) (ι : Z ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) A))

/--
The compatibility condition for local sections whose transition factor is the `e`th power of the
frame unit.
-/
def Cocycle (e : ℕ) (t : ∀ i : Fin (N + 1), Γ(Z, pullbackChart ι i)) : Prop :=
  ∀ i j : Fin (N + 1),
    restrictFun (inf_le_left : pullbackChart ι i ⊓ pullbackChart ι j ≤ pullbackChart ι i) (t i)
      = restrictFun (inf_le_left : pullbackChart ι i ⊓ pullbackChart ι j ≤ pullbackChart ι i)
        (frameUnit ι i j) ^ e
        * restrictFun (inf_le_right : pullbackChart ι i ⊓ pullbackChart ι j ≤ pullbackChart ι j) (t
          j)

/-- Componentwise multiplication of a twisted section by the given local sections. -/
noncomputable def mulVal (t : ∀ i : Fin (N + 1), Γ(Z, pullbackChart ι i)) (d : ℕ) (U : Z.Opens) (g
  : twistObj π ι d U) : ∀ i : Fin (N + 1), Γ(Z, U ⊓ pullbackChart ι i) :=
  fun i => restrictFun (inf_le_right : U ⊓ pullbackChart ι i ≤ pullbackChart ι i) (t i) * g.val i

theorem mulVal_compat (e : ℕ) (t : ∀ i : Fin (N + 1), Γ(Z, pullbackChart ι i)) (htc : Cocycle ι e t)
    (d : ℕ) (U : Z.Opens) (g : twistObj π ι d U) :
    TwistCompat ι (d + e) U (mulVal π ι t d U g) := by
  intro i j
  have hg := g.compat i j
  have ht := congrArg (restrictFun (inf_le_inf_right (pullbackChart ι j)
    (inf_le_right : U ⊓ pullbackChart ι i ≤ pullbackChart ι i))) (htc i j)
  simp only [map_mul, map_pow, restrictFun_restrictFun] at ht
  simp only [mulVal, map_mul, restrictFun_restrictFun]
  rw [hg, pow_add]
  have e1 : restrictFun ((inf_le_left : (U ⊓ pullbackChart ι i) ⊓ pullbackChart ι j ≤ U ⊓
    pullbackChart ι i).trans
      (inf_le_right : U ⊓ pullbackChart ι i ≤ pullbackChart ι i)) (t i)
      = restrictFun ((inf_le_inf_right (pullbackChart ι j)
          (inf_le_right : U ⊓ pullbackChart ι i ≤ pullbackChart ι i)).trans inf_le_left) (t i) :=
            rfl
  have e2 : restrictFun ((le_inf (le_trans inf_le_left inf_le_left) inf_le_right :
        (U ⊓ pullbackChart ι i) ⊓ pullbackChart ι j ≤ U ⊓ pullbackChart ι j).trans
      (inf_le_right : U ⊓ pullbackChart ι j ≤ pullbackChart ι j)) (t j)
      = restrictFun ((inf_le_inf_right (pullbackChart ι j)
          (inf_le_right : U ⊓ pullbackChart ι i ≤ pullbackChart ι i)).trans inf_le_right) (t j) :=
            rfl
  have e3 : restrictFun ((inf_le_inf_right (pullbackChart ι j)
          (inf_le_right : U ⊓ pullbackChart ι i ≤ pullbackChart ι i)).trans inf_le_left) (frameUnit
            ι i j)
      = restrictFun (le_trans inf_le_left inf_le_right :
          (U ⊓ pullbackChart ι i) ⊓ pullbackChart ι j ≤ pullbackChart ι i) (frameUnit ι i j) := rfl
  rw [e1, ht, e3, e2]
  ring

/--
The morphism of twisted presheaves induced by local sections satisfying the transition cocycle
condition.
-/
noncomputable def mulHom (e : ℕ) (t : ∀ i : Fin (N + 1), Γ(Z, pullbackChart ι i)) (htc : Cocycle ι
  e t) (d : ℕ) :
    Hom (twist π ι d) (twist π ι (d + e)) where
  app U :=
    { toFun := fun g => ⟨mulVal π ι t d U g, mulVal_compat π ι e t htc d U g⟩
      map_add' := fun g g' => twistObj.ext (funext fun i => by
        change restrictFun _ (t i) * (g.val i + g'.val i) = restrictFun _ (t i) * g.val i +
          restrictFun _ (t i) * g'.val i
        rw [mul_add])
      map_smul' := fun r g => twistObj.ext (funext fun i => by
        let := Scheme.TwoAffineOpenCover.algebraOfHom π U
        change restrictFun (inf_le_right : U ⊓ pullbackChart ι i ≤ pullbackChart ι i) (t i)
            * (restrictFun (inf_le_left : U ⊓ pullbackChart ι i ≤ U) (algebraMap A (Γ(Z, U) : Type
              u) r) * g.val i)
          = restrictFun (inf_le_left : U ⊓ pullbackChart ι i ≤ U) (algebraMap A (Γ(Z, U) : Type u)
            r)
            * (restrictFun (inf_le_right : U ⊓ pullbackChart ι i ≤ pullbackChart ι i) (t i) * g.val
              i)
        ring) }
  app_smul U a g := twistObj.ext (funext fun i => by
    change restrictFun (inf_le_right : U ⊓ pullbackChart ι i ≤ pullbackChart ι i) (t i)
        * (restrictFun (inf_le_left : U ⊓ pullbackChart ι i ≤ U) a * g.val i)
      = restrictFun (inf_le_left : U ⊓ pullbackChart ι i ≤ U) a
        * (restrictFun (inf_le_right : U ⊓ pullbackChart ι i ≤ pullbackChart ι i) (t i) * g.val i)
    ring)
  naturality {U U'} h := LinearMap.ext fun g => twistObj.ext (funext fun i => by
    change restrictFun _ (t i) * ((twist π ι d).res h g).val i
      = ((twist π ι (d + e)).res h ⟨mulVal π ι t d U' g, mulVal_compat π ι e t htc d U' g⟩).val i
    rw [twist_res_val (π := π) (φ := ι) (m := d) h g i,
      twist_res_val (π := π) (φ := ι) (m := d + e) h
        ⟨mulVal π ι t d U' g, mulVal_compat π ι e t htc d U' g⟩ i]
    change restrictFun _ (t i) * restrictFun _ (g.val i) = restrictFun _ (restrictFun _ (t i) *
      g.val i)
    rw [map_mul, restrictFun_restrictFun])

theorem mulHom_val (e : ℕ) (t : ∀ i : Fin (N + 1), Γ(Z, pullbackChart ι i)) (htc : Cocycle ι e t)
    (d : ℕ) (U : Z.Opens) (g : (twist π ι d).obj U) (i : Fin (N + 1)) :
    ((mulHom π ι e t htc d).app U g).val i
      = restrictFun (inf_le_right : U ⊓ pullbackChart ι i ≤ pullbackChart ι i) (t i) * g.val i :=
        rfl

theorem mulHom_injective [IsAffineHom ι] (e : ℕ) (t : ∀ i : Fin (N + 1), Γ(Z, pullbackChart ι i))
    (htc : Cocycle ι e t) (hnz : ∀ (i : Fin (N + 1)) (y : Γ(Z, pullbackChart ι i)), t i * y = 0 → y
      = 0)
    (d : ℕ) (U : Z.Opens) : Function.Injective ((mulHom π ι e t htc d).app U) := by
  have haff : ∀ i : Fin (N + 1), IsAffineOpen (pullbackChart ι i) := fun i =>
    isAffineOpen_pullbackChart ι i
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro g hg
  rw [LinearMap.mem_ker] at hg
  refine twistObj.ext (funext fun i => ?_)
  have h := congrArg (fun s : twistObj π ι (d + e) U => s.val i) hg
  simp only [mulHom_val] at h
  exact eq_zero_of_restrict_mul_eq_zero (haff i) (t i) (hnz i) inf_le_right (g.val i) h

end Mul

end P2mTwistMulSol

theorem _root_.AlgebraicGeometry.ProjSpace.exists_hom_twist_val_eq_mul_and_injective_of_cocycle
    {A : Type u} [CommRing A] {N : ℕ} {Z : Scheme.{u}}
    (π : Z ⟶ Spec (.of A)) (ι : Z ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) A))
      [IsAffineHom ι]
    (e : ℕ) (t : ∀ i : Fin (N + 1), Γ(Z, ProjSpace.pullbackChart ι i))
    (htc : ∀ i j : Fin (N + 1),
      ProjSpace.restrictFun (inf_le_left : ProjSpace.pullbackChart ι i ⊓ ProjSpace.pullbackChart ι
        j ≤ _) (t i)
        = ProjSpace.restrictFun (inf_le_left : ProjSpace.pullbackChart ι i ⊓
          ProjSpace.pullbackChart ι j ≤ _)
            (ProjSpace.frameUnit ι i j) ^ e
          * ProjSpace.restrictFun (inf_le_right : ProjSpace.pullbackChart ι i ⊓
            ProjSpace.pullbackChart ι j ≤ _) (t j))
    (hnz : ∀ (i : Fin (N + 1)) (y : Γ(Z, ProjSpace.pullbackChart ι i)), t i * y = 0 → y = 0) (d :
      ℕ) :
    ∃ μ : OModulePresheaf.Hom (ProjSpace.twist π ι d) (ProjSpace.twist π ι (d + e)),
      (∀ (U : Z.Opens) (g : (ProjSpace.twist π ι d).obj U) (i : Fin (N + 1)),
        (μ.app U g).val i
          = ProjSpace.restrictFun (inf_le_right : U ⊓ ProjSpace.pullbackChart ι i ≤ _) (t i) *
            g.val i) ∧
      (∀ U : Z.Opens, Function.Injective (μ.app U)) :=
  ⟨P2mTwistMulSol.mulHom π ι e t htc d, fun U g i => P2mTwistMulSol.mulHom_val π ι e t htc d U g i,
    P2mTwistMulSol.mulHom_injective π ι e t htc hnz d⟩
end ProjSpace_exists_hom_twist_val_eq_mul_and_injective_of_cocycle
end AlgebraicCurves.Geometry.Projective.Proofs
end ProofImplementation
