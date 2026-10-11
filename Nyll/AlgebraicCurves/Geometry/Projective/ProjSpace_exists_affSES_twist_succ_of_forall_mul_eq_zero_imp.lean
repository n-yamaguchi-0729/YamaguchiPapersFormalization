/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_ProjSpace_exists_affSES_twist_succ_of_forall_mul_eq_zero_imp.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.Algebra.Module.Submodule.Ker
import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization
import Mathlib.RingTheory.Ideal.Span
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Nyll.SchemeTheory.ProjectiveSpace.Basic
import Nyll.SchemeTheory.ProjectiveSpace.Cover
import Nyll.AlgebraicCurves.Geometry.Projective.ProjTwistDatum
import Nyll.AlgebraicCurves.Hilbert.Functor.Basic
import Nyll.AlgebraicCurves.Foundations.Algebra.Nat_MacaulayPow
import Nyll.SchemeTheory.Cohomology.Sheaves.OModulePresheafHom
import Nyll.SchemeTheory.Cohomology.Sheaves.OModulePresheafConstructions
import Nyll.AlgebraicCurves.Geometry.Projective.ProjSpace_exists_hom_twist_val_eq_mul_and_injective_of_cocycle
import Nyll.AlgebraicCurves.Geometry.Projective.ProjSpace_exists_linearEquiv_H0_HSucc_coker_twist_of_ker_eq_sup
import Nyll.AlgebraicCurves.Geometry.Projective.ProjSpace_exists_linearMap_homogeneousSubmodule_twistObj_top_val_eq

/-!
# Proj Space exists aff SES twist succ of forall mul eq zero imp
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Projective.Proofs
namespace ProjSpace_exists_affSES_twist_succ_of_forall_mul_eq_zero_imp

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MvPolynomial
  AlgebraicGeometry.HilbertFunctor

attribute [local instance] MvPolynomial.gradedAlgebra

namespace P2mRM1Reduce

open AlgebraicGeometry.ProjSpace

theorem restrictFun_injective_of_le_le {X : Scheme.{0}} {W W' : X.Opens} (h : W ≤ W') (h' : W' ≤ W)
  {x y : Γ(X, W')}
    (hxy : restrictFun h x = restrictFun h y) : x = y := by
  have e : W = W' := le_antisymm h h'
  subst e
  rwa [restrictFun_refl, restrictFun_refl] at hxy

end P2mRM1Reduce

theorem _root_.AlgebraicGeometry.ProjSpace.exists_affSES_twist_succ_of_forall_mul_eq_zero_imp
    (n : ℕ) (k : Type) [CommRing k]
    (Zk : Scheme.{0}) (ιk : Zk ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k))
      [IsClosedImmersion ιk]
    (ℓ : MvPolynomial (Fin (n + 1)) k) (hℓ : ℓ.IsHomogeneous 1)
    (hnzd : ∀ (i : Fin (n + 1)) (t : Γ(Zk, ιk ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule
      (Fin (n + 1)) k) (MvPolynomial.X i))),
      (ιk.app (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) (MvPolynomial.X
        i))
        (Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) (MvPolynomial.X i)
          (HomogeneousLocalization.mk
            { deg := 1
              num := ⟨ℓ, (MvPolynomial.mem_homogeneousSubmodule 1 ℓ).mpr hℓ⟩
              den := ⟨MvPolynomial.X i ^ 1, (MvPolynomial.mem_homogeneousSubmodule 1 _).mpr
                (MvPolynomial.isHomogeneous_X_pow i 1)⟩
              den_mem := ⟨1, rfl⟩ }))) * t = 0 → t = 0)
    (𝓘ℓ : (Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k)).IdealSheafData)
    (h𝓘ℓ : (∀ i : Fin (n + 1),
        𝓘ℓ.ideal ⟨Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k)
          (MvPolynomial.X i),
          Proj.isAffineOpen_basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k)
            (MvPolynomial.X i) (ProjSpace.X_mem_one k n i) one_pos⟩ =
        Ideal.span { s | ∃ (d : ℕ) (G : MvPolynomial (Fin (n + 1)) k) (hG : G.IsHomogeneous d),
          G ∈ Ideal.span {ℓ} ∧
          s = Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k)
            (MvPolynomial.X i)
              (HomogeneousLocalization.mk
                { deg := d
                  num := ⟨G, (MvPolynomial.mem_homogeneousSubmodule d G).mpr hG⟩
                  den := ⟨MvPolynomial.X i ^ d, (MvPolynomial.mem_homogeneousSubmodule d _).mpr
                    (MvPolynomial.isHomogeneous_X_pow i d)⟩
                  den_mem := ⟨d, rfl⟩ }) }))
    (Z' : Scheme.{0}) (ι' : Z' ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k))
      [IsClosedImmersion ι']
    (hker : ι'.ker = ιk.ker ⊔ 𝓘ℓ) (d : ℕ) :
    ∃ (F₃ : OModulePresheaf (ιk ≫ ProjSpace.π k n))
      (S : OModulePresheaf.AffSES (ProjSpace.twist (ιk ≫ ProjSpace.π k n) ιk d)
        (ProjSpace.twist (ιk ≫ ProjSpace.π k n) ιk (d + 1)) F₃)
      (e₀ : F₃.H0 (ProjSpace.stdCoverPullback ιk) ≃ₗ[k]
        (ProjSpace.twist (ι' ≫ ProjSpace.π k n) ι' (d + 1)).H0 (ProjSpace.stdCoverPullback ι'))
      (_e : ∀ i : ℕ, F₃.HSucc (ProjSpace.stdCoverPullback ιk) i ≃ₗ[k]
        (ProjSpace.twist (ι' ≫ ProjSpace.π k n) ι' (d + 1)).HSucc (ProjSpace.stdCoverPullback ι')
          i),
      ∀ (c : (ProjSpace.twist (ιk ≫ ProjSpace.π k n) ιk (d + 1)).cochain
        (ProjSpace.stdCoverPullback ιk) 0)
        (hc : c ∈ (ProjSpace.twist (ιk ≫ ProjSpace.π k n) ιk (d + 1)).H0
          (ProjSpace.stdCoverPullback ιk))
        (G : MvPolynomial (Fin (n + 1)) k) (hG : G.IsHomogeneous (d + 1)),
          (∀ (s : (ProjSpace.stdCoverPullback ιk).Idx 0) (i : Fin (n + 1)),
            (c s).val i =
              ProjSpace.restrictFun
                (inf_le_right : (ProjSpace.stdCoverPullback ιk).inter s ⊓ ProjSpace.pullbackChart
                  ιk i ≤
                  ProjSpace.pullbackChart ιk i)
                (ιk.app (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k)
                  (MvPolynomial.X i))
              (Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k)
                (MvPolynomial.X i)
                (HomogeneousLocalization.mk
                  { deg := d + 1
                    num := ⟨G, (MvPolynomial.mem_homogeneousSubmodule (d + 1) G).mpr hG⟩
                    den := ⟨MvPolynomial.X i ^ (d + 1), (MvPolynomial.mem_homogeneousSubmodule (d +
                      1) _).mpr
                      (MvPolynomial.isHomogeneous_X_pow i (d + 1))⟩
                    den_mem := ⟨d + 1, rfl⟩ })))) →
          ∀ (s : (ProjSpace.stdCoverPullback ι').Idx 0) (i : Fin (n + 1)),
            ((e₀ (S.proj.H0Map (ProjSpace.stdCoverPullback ιk) ⟨c, hc⟩)).1 s).val i =
              ProjSpace.restrictFun
                (inf_le_right : (ProjSpace.stdCoverPullback ι').inter s ⊓ ProjSpace.pullbackChart
                  ι' i ≤
                  ProjSpace.pullbackChart ι' i)
                (ι'.app (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k)
                  (MvPolynomial.X i))
              (Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k)
                (MvPolynomial.X i)
                (HomogeneousLocalization.mk
                  { deg := d + 1
                    num := ⟨G, (MvPolynomial.mem_homogeneousSubmodule (d + 1) G).mpr hG⟩
                    den := ⟨MvPolynomial.X i ^ (d + 1), (MvPolynomial.mem_homogeneousSubmodule (d +
                      1) _).mpr
                      (MvPolynomial.isHomogeneous_X_pow i (d + 1))⟩
                    den_mem := ⟨d + 1, rfl⟩ }))) := by
  set t : ∀ i : Fin (n + 1), Γ(Zk, ProjSpace.pullbackChart ιk i) := fun i => ((ιk.app
    (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) (MvPolynomial.X i)))
            (Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) (MvPolynomial.X
              i)
              (HomogeneousLocalization.mk
                { deg := 1
                  num := ⟨ℓ, (MvPolynomial.mem_homogeneousSubmodule 1 ℓ).mpr hℓ⟩
                  den := ⟨MvPolynomial.X i ^ 1, (MvPolynomial.mem_homogeneousSubmodule 1 _).mpr
                    (MvPolynomial.isHomogeneous_X_pow i 1)⟩
                  den_mem := ⟨1, rfl⟩ }))) with ht
  have htc : ∀ i j : Fin (n + 1),
      ProjSpace.restrictFun (inf_le_left : ProjSpace.pullbackChart ιk i ⊓ ProjSpace.pullbackChart
        ιk j ≤ _) (t i)
        = ProjSpace.restrictFun (inf_le_left : ProjSpace.pullbackChart ιk i ⊓
          ProjSpace.pullbackChart ιk j ≤ _)
            (ProjSpace.frameUnit ιk i j) ^ 1
          * ProjSpace.restrictFun (inf_le_right : ProjSpace.pullbackChart ιk i ⊓
            ProjSpace.pullbackChart ιk j ≤ _) (t j) := by
    obtain ⟨θ, hθ, -⟩ :=
      AlgebraicGeometry.ProjSpace.exists_linearMap_homogeneousSubmodule_twistObj_top_val_eq ιk 1
    intro i j
    have hc := (θ ⟨ℓ, (MvPolynomial.mem_homogeneousSubmodule 1 ℓ).mpr hℓ⟩).compat i j
    have hθi : (θ ⟨ℓ, (MvPolynomial.mem_homogeneousSubmodule 1 ℓ).mpr hℓ⟩).val i =
        ProjSpace.restrictFun
          (inf_le_right : ⊤ ⊓ ProjSpace.pullbackChart ιk i ≤ ProjSpace.pullbackChart ιk i) (t i) :=
      hθ ℓ hℓ i
    have hθj : (θ ⟨ℓ, (MvPolynomial.mem_homogeneousSubmodule 1 ℓ).mpr hℓ⟩).val j =
        ProjSpace.restrictFun
          (inf_le_right : ⊤ ⊓ ProjSpace.pullbackChart ιk j ≤ ProjSpace.pullbackChart ιk j) (t j) :=
      hθ ℓ hℓ j
    have hle : (⊤ ⊓ ProjSpace.pullbackChart ιk i) ⊓ ProjSpace.pullbackChart ιk j
        ≤ ProjSpace.pullbackChart ιk i ⊓ ProjSpace.pullbackChart ιk j :=
      inf_le_inf_right _ inf_le_right
    have hge : ProjSpace.pullbackChart ιk i ⊓ ProjSpace.pullbackChart ιk j
        ≤ (⊤ ⊓ ProjSpace.pullbackChart ιk i) ⊓ ProjSpace.pullbackChart ιk j :=
      inf_le_inf_right _ (le_inf le_top le_rfl)
    apply P2mRM1Reduce.restrictFun_injective_of_le_le hle hge
    rw [map_mul, map_pow, ProjSpace.restrictFun_restrictFun, ProjSpace.restrictFun_restrictFun,
      ProjSpace.restrictFun_restrictFun]
    let O : Zk.Opens := (⊤ ⊓ ProjSpace.pullbackChart ιk i) ⊓ ProjSpace.pullbackChart ιk j
    have hi : ProjSpace.restrictFun
        (inf_le_left : O ≤ ⊤ ⊓ ProjSpace.pullbackChart ιk i)
        ((θ ⟨ℓ, (MvPolynomial.mem_homogeneousSubmodule 1 ℓ).mpr hℓ⟩).val i) =
        ProjSpace.restrictFun (hle.trans inf_le_left) (t i) :=
      (congrArg (ProjSpace.restrictFun
        (inf_le_left : O ≤ ⊤ ⊓ ProjSpace.pullbackChart ιk i)) hθi).trans
        (ProjSpace.restrictFun_restrictFun
          (inf_le_left : O ≤ ⊤ ⊓ ProjSpace.pullbackChart ιk i)
          (inf_le_right : ⊤ ⊓ ProjSpace.pullbackChart ιk i ≤ ProjSpace.pullbackChart ιk i) (t i))
    have hj : ProjSpace.restrictFun
        (le_inf (inf_le_left.trans inf_le_left) inf_le_right : O ≤ ⊤ ⊓ ProjSpace.pullbackChart ιk j)
        ((θ ⟨ℓ, (MvPolynomial.mem_homogeneousSubmodule 1 ℓ).mpr hℓ⟩).val j) =
        ProjSpace.restrictFun (hle.trans inf_le_right) (t j) :=
      (congrArg (ProjSpace.restrictFun
        (le_inf (inf_le_left.trans inf_le_left) inf_le_right : O ≤ ⊤ ⊓ ProjSpace.pullbackChart ιk
          j)) hθj).trans
        (ProjSpace.restrictFun_restrictFun
          (le_inf (inf_le_left.trans inf_le_left) inf_le_right : O ≤ ⊤ ⊓ ProjSpace.pullbackChart ιk
            j)
          (inf_le_right : ⊤ ⊓ ProjSpace.pullbackChart ιk j ≤ ProjSpace.pullbackChart ιk j) (t j))
    exact hi.symm.trans (hc.trans (congrArg
      (fun z : Γ(Zk, O) => ProjSpace.restrictFun (hle.trans inf_le_left)
        (ProjSpace.frameUnit ιk i j) ^ 1 * z) hj))
  obtain ⟨μ, hμ, hμi⟩ :=
    AlgebraicGeometry.ProjSpace.exists_hom_twist_val_eq_mul_and_injective_of_cocycle
    (ιk ≫ ProjSpace.π k n) ιk 1 t htc (fun i y h => hnzd i y h) d
  obtain ⟨e₀, e, he⟩ :=
    AlgebraicGeometry.ProjSpace.exists_linearEquiv_H0_HSucc_coker_twist_of_ker_eq_sup
    n k Zk ιk ℓ hℓ 𝓘ℓ h𝓘ℓ Z' ι' hker d htc μ hμ
  refine ⟨OModulePresheaf.coker μ,
    { inc := μ.toAffHom
      proj := (OModulePresheaf.imCokerSES μ).proj.toAffHom
      injective := fun U => hμi U.1
      surjective := fun U => (OModulePresheaf.imCokerSES μ).surjective U.1
      exact := fun U => ?_ }, e₀, e, he⟩
  change LinearMap.range (μ.app U.1) = LinearMap.ker ((LinearMap.range (μ.app U.1)).mkQ)
  rw [Submodule.ker_mkQ]
end ProjSpace_exists_affSES_twist_succ_of_forall_mul_eq_zero_imp
end AlgebraicCurves.Geometry.Projective.Proofs
end ProofImplementation

attribute [-instance] AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero
attribute [-simp] AlgebraicGeometry.OModulePresheaf.prod_obj
  AlgebraicGeometry.OModulePresheaf.restrOpen_obj
  AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq
  AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj
  AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app
  AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj
  AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec
  AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U
  AlgebraicGeometry.OModulePresheaf.sndHom_app
