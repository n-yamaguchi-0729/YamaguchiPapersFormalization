/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Nyll.EtaleFundamentalGroups.FiniteEtale.FiniteField.RecoveredStageRecovery
import Nyll.EtaleFundamentalGroups.FiniteEtale.FiniteField.ConstantFieldRebase
import Nyll.EtaleFundamentalGroups.FiniteEtale.FiniteField.FiniteTowerModel

/-!
# Global Model

Actual recovered local models glue to a finite-stage model that recovers
the original finite étale cover as an object of the finite étale category.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite AlgebraicGeometry
namespace EtaleFundamentalGroups

/-- Actual recovered local models glue to a finite-stage model that recovers
the original finite étale cover as an object of the finite étale category. -/
theorem exists_finiteIntermediateField_model_of_recovered_local_models
    (k L : Type u) [Field k] [Field L] [Algebra k L] [Algebra.IsAlgebraic k L]
    (S : Scheme.{u}) [QuasiSeparatedSpace S] (f : S ⟶ Spec (CommRingCat.of k))
    (𝒰 : S.OpenCover.{u}) [Finite 𝒰.I₀] [∀ i : 𝒰.I₀, IsAffine (𝒰.X i)]
    (M : ∀ i : 𝒰.I₀, Over (𝒰.X i)) [∀ i : 𝒰.I₀, IsFiniteEtale (M i).hom]
    (Z : FiniteEtale (Limits.pullback (Spec.map (CommRingCat.ofHom (algebraMap k L))) f))
    (e : ∀ i : 𝒰.I₀,
      (Over.pullback (pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap k L)))
        (𝒰.f i ≫ f))).obj (M i) ≅
      (Over.pullback ((constantFieldOpenCover k L S f 𝒰).f i)).obj
        ((FiniteEtale.forget _).obj Z)) :
    ∃ s : Finset L, FiniteDimensional k (IntermediateField.adjoin k (s : Set L)) ∧
      ∃ N : FiniteEtale (Limits.pullback (Spec.map (CommRingCat.ofHom
        (algebraMap k (IntermediateField.adjoin k (s : Set L))))) f),
        Nonempty ((FiniteEtale.pullback
          ((constantFieldInverseLimitCone k L S f).π.app (op s))).obj N ≅ Z) := by
  let ZO := (FiniteEtale.forget _).obj Z
  obtain ⟨s, hfin, g, hg, q, hq, hqU⟩ :=
    exists_finiteIntermediateField_recovered_glueData k L S f 𝒰 M ZO e
  let : IsFiniteEtale q := hq
  let N := FiniteEtale.mk q
  obtain ⟨eO⟩ := nonempty_recoveredFiniteStageGlueData_over_iso k L S f 𝒰 M ZO e s g
    (fun ij ↦ (hg ij).1) (fun ij ↦ (hg ij).2.1) (fun ij ↦ (hg ij).2.2) q hqU
  refine ⟨s, hfin, N, ?_⟩
  exact ⟨(FiniteEtale.forget _).preimageIso eO⟩

end EtaleFundamentalGroups

namespace AlgebraicGeometry
open EtaleFundamentalGroups

/-- Every finite étale cover of a qcqs scheme after an algebraic constant
extension descends to an actual finite intermediate field. The conclusion
includes recovery along the literal coefficient-inclusion pullback. -/
theorem FiniteEtale.exists_finiteIntermediateField_scheme_model
    (k L : Type u) [Field k] [Field L] [Algebra k L] [Algebra.IsAlgebraic k L]
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    (f : X ⟶ Spec (CommRingCat.of k))
    (Z : FiniteEtale (Limits.pullback (Spec.map (CommRingCat.ofHom (algebraMap k L))) f)) :
    ∃ H : IntermediateField k L, FiniteDimensional k H ∧
      ∃ N : FiniteEtale (Limits.pullback (Spec.map (CommRingCat.ofHom (algebraMap k H))) f),
        Nonempty ((FiniteEtale.pullback
          (pullback.map (Spec.map (CommRingCat.ofHom (algebraMap k L))) f
            (Spec.map (CommRingCat.ofHom (algebraMap k H))) f
            (Spec.map (CommRingCat.ofHom H.val.toRingHom)) (𝟙 X) (𝟙 _)
            (by rw [Category.comp_id, ← Spec.map_comp]; rfl)
            (by rw [Category.comp_id, Category.id_comp]))).obj N ≅ Z) := by
  let 𝒰 := X.affineCover.finiteSubcover
  obtain ⟨F, hF, M, hrec⟩ := exists_finiteIntermediateField_rebased_local_models k L X f Z
  let : FiniteDimensional k F := hF
  let φF := Spec.map (CommRingCat.ofHom (algebraMap k F))
  let ψF := Spec.map (CommRingCat.ofHom F.val.toRingHom)
  let XF : Scheme.{u} := Limits.pullback φF f
  let fF : XF ⟶ Spec (CommRingCat.of F) := pullback.fst φF f
  let 𝒰F : XF.OpenCover := constantFieldOpenCover k F X f 𝒰
  let : Fintype 𝒰F.I₀ := by
    change Fintype 𝒰.I₀
    exact inferInstanceAs (Fintype X.affineCover.finiteSubcover.I₀)
  let : ∀ i : 𝒰.I₀, IsAffine (𝒰.X i) := fun i ↦ inferInstanceAs (IsAffine (Spec _))
  let : ∀ i : 𝒰F.I₀, IsAffine (𝒰F.X i) := by
    intro i
    let i₀ : 𝒰.I₀ := i
    let : IsAffine (𝒰.X i₀) := inferInstanceAs (IsAffine (Spec _))
    exact constantFieldOpenCover_isAffine k F X f 𝒰 i₀
  let : IsAffineHom (pullback.snd φF f) :=
    MorphismProperty.pullback_snd
      (P := (show MorphismProperty Scheme.{u} from @IsAffineHom)) φF f inferInstance
  let : QuasiSeparatedSpace XF := quasiSeparatedSpace_of_quasiSeparated (pullback.snd φF f)
  let MF (i : 𝒰F.I₀) : Over (𝒰F.X i) := (FiniteEtale.forget _).obj (M i)
  let : ∀ i : 𝒰F.I₀, IsFiniteEtale (MF i).hom := fun i ↦
    inferInstanceAs (IsFiniteEtale (M i).hom)
  let ZF : FiniteEtale (Limits.pullback ψF fF) :=
    (FiniteEtale.pullback (constantFieldTowerIso k L F X f).hom).obj Z
  let eF (i : 𝒰F.I₀) :
      (Over.pullback (pullback.snd ψF (𝒰F.f i ≫ fF))).obj (MF i) ≅
        (Over.pullback ((constantFieldOpenCover F L XF fF 𝒰F).f i)).obj
          ((FiniteEtale.forget _).obj ZF) :=
    (FiniteEtale.forget _).mapIso (hrec i).some
  obtain ⟨s, hs, N, hN⟩ :=
    exists_finiteIntermediateField_model_of_recovered_local_models F L XF fF 𝒰F MF ZF eF
  let E := IntermediateField.adjoin F (s : Set L)
  let : FiniteDimensional F E := hs
  have hE : FiniteDimensional k (E.restrictScalars k) := FiniteDimensional.trans k F E
  have hN' : Nonempty ((FiniteEtale.pullback
      (finiteIntermediateTowerProjection k L F E X f)).obj N ≅ ZF) := by
    rw [finiteIntermediateTowerProjection_eq_cone]
    exact hN
  refine ⟨E.restrictScalars k, hE,
    (FiniteEtale.pullback (finiteIntermediateTowerIso k L F E X f).inv).obj N, ?_⟩
  exact ⟨finiteIntermediateTowerModelRecoveryIso k L F E X f N Z hN'.some⟩

end AlgebraicGeometry
