/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Algebra.Algebra.Pi
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Nyll.AlgebraicCurves.Foundations.CategoryTheory.CategoryTheory_MorphismProperty_widePullback_base
import Nyll.AlgebraicCurves.Geometry.Schemes.isIntegral_of_smooth_of_preconnectedSpace
import Nyll.AlgebraicCurves.Geometry.Schemes.SmoothOfRelativeDimension_le_topologicalKrullDim
import Nyll.AlgebraicCurves.Hilbert.SymmetricPowerData
import Nyll.AlgebraicCurves.RelativeDivisors.RelEffCartierDiv_IsUniversal_geometricallyConnected
import Nyll.AlgebraicCurves.RelativeDivisors.UniversalSumKernel
import Nyll.JacobianVarieties.Albanese.FiniteSums

/-!
# Finite sums on universal effective divisors

Over any field, finite sums of the images of a smooth geometrically connected
pointed curve in a proper geometrically integral group scheme descend through
the actual universal effective-divisor map. Its finite flat kernel pair has
generic rank `r!`; the distinct permutation sections exhaust that rank, as
proved by linear independence of algebra characters. Flat base change preserves
scheme-theoretic dominance, so equality extends from this generic fibre to the
entire kernel pair and effective-epimorphism descent gives the required map.

The resulting equality for `SameDivisor` holds on arbitrary test schemes.
No permutation description of tuples over a nonreduced test scheme is asserted.
-/

noncomputable section

universe u v w

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open NeronModelInfra GoodReductionJacobian

namespace JacobianVarieties.Albanese

/-- A family of distinct rational characters of a finite algebra whose size
is its dimension identifies that algebra with the product of the ground field.
In particular no separability or reducedness hypothesis is needed. -/
private theorem bijective_pi_of_injective_characters
    (K : Type u) [Field K] (A : Type v) [CommRing A] [Algebra K A]
    [FiniteDimensional K A] {ι : Type w} [Fintype ι]
    (χ : ι → A →ₐ[K] K) (hχ : Function.Injective χ)
    (hrank : Fintype.card ι = Module.finrank K A) :
    Function.Bijective (AlgHom.pi χ) := by
  have hli : LinearIndependent K (fun i => (χ i).toLinearMap) :=
    (linearIndependent_algHom_toLinearMap K A K).comp χ hχ
  have hdim : Fintype.card ι = Module.finrank K (Module.Dual K A) := by
    rw [Subspace.dual_finrank_eq]
    exact hrank
  let b : Module.Basis ι K (Module.Dual K A) :=
    basisOfLinearIndependentOfCardEqFinrank' (fun i => (χ i).toLinearMap) hli hdim
  have hinj : Function.Injective (AlgHom.pi χ) := by
    intro x y hxy
    apply Module.eval_apply_injective K
    apply b.ext
    intro i
    rw [show b i = (χ i).toLinearMap from congrFun
      (coe_basisOfLinearIndependentOfCardEqFinrank' (fun j => (χ j).toLinearMap) hli hdim) i]
    exact congrFun hxy i
  refine ⟨hinj, ?_⟩
  apply (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (f := (AlgHom.pi χ).toLinearMap) ?_).mp hinj
  rw [Module.finrank_fintype_fun_eq_card]
  exact hrank.symm

/-- The corresponding rational sections cover the finite affine scheme as a
disjoint union. This supplies scheme morphism equality, including on nilpotents,
rather than just equality of topological points. -/
private theorem isIso_sigmaDesc_specMap_of_injective_characters
    (K A : Type u) [Field K] [CommRing A] [Algebra K A]
    [FiniteDimensional K A] {ι : Type u} [Fintype ι]
    (χ : ι → A →ₐ[K] K) (hχ : Function.Injective χ)
    (hrank : Fintype.card ι = Module.finrank K A) :
    IsIso (Sigma.desc fun i => Spec.map (CommRingCat.ofHom (χ i).toRingHom)) := by
  let e : A ≃ₐ[K] (ι → K) :=
    AlgEquiv.ofBijective (AlgHom.pi χ)
      (bijective_pi_of_injective_characters K A χ hχ hrank)
  have he : IsIso (Spec.map (CommRingCat.ofHom (AlgHom.pi χ).toRingHom)) := by
    change IsIso (Spec.map e.toRingEquiv.toCommRingCatIso.hom)
    infer_instance
  have hfac : (Sigma.desc fun i => Spec.map (CommRingCat.ofHom (χ i).toRingHom)) =
      sigmaSpec (fun _ : ι => CommRingCat.of K) ≫
        Spec.map (CommRingCat.ofHom (AlgHom.pi χ).toRingHom) := by
    apply Sigma.hom_ext
    intro i
    rw [Sigma.ι_comp_desc, ι_sigmaSpec_assoc, ← Spec.map_comp]
    rfl
  rw [hfac]
  infer_instance

/-- Distinct rational sections exhausting the finite rank give a genuine
decomposition of a finite scheme, without a reducedness assumption. -/
private theorem isIso_sigmaDesc_of_card_eq_finrank
    {K : Type u} [Field K] {Z : Scheme.{u}}
    (z : Z ⟶ Spec (CommRingCat.of K)) [IsFinite z]
    {ι : Type u} [Fintype ι] (a : ι → (Spec (CommRingCat.of K) ⟶ Z))
    (ha : ∀ i, a i ≫ z = 𝟙 _) (hinj : Function.Injective a)
    (t : Spec (CommRingCat.of K)) (hrank : Fintype.card ι = z.finrank t) :
    IsIso (Sigma.desc a) := by
  have : IsAffine Z := isAffine_of_isAffineHom z
  let φ : CommRingCat.of K ⟶ Γ(Z, ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ z.appTop
  have hφfin : φ.hom.Finite := z.finite_appTop.comp
    (RingHom.Finite.of_surjective _
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of K)).inv).2)
  let : Algebra K Γ(Z, ⊤) := φ.hom.toAlgebra
  have : Module.Finite K Γ(Z, ⊤) := hφfin
  have hφflat : φ.hom.Flat := inferInstanceAs (Module.Flat K Γ(Z, ⊤))
  have hfac : Z.isoSpec.hom ≫ Spec.map φ = z := by
    dsimp only [φ]
    rw [Spec.map_comp, ← Scheme.isoSpec_Spec_inv,
      Scheme.isoSpec_hom_naturality_assoc, Iso.hom_inv_id, Category.comp_id]
  let ψ (i : ι) : Γ(Z, ⊤) ⟶ CommRingCat.of K :=
    Spec.preimage (a i ≫ Z.isoSpec.hom)
  have hψ (i : ι) : φ ≫ ψ i = 𝟙 _ := by
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_id]
    change Spec.map (Spec.preimage (a i ≫ Z.isoSpec.hom)) ≫ Spec.map φ = _
    rw [Spec.map_preimage, Category.assoc, hfac, ha]
  let χ (i : ι) : Γ(Z, ⊤) →ₐ[K] K :=
    { (ψ i).hom with
      commutes' := fun x => ConcreteCategory.congr_hom (hψ i) x }
  have hχ : Function.Injective χ := by
    intro i j hij
    apply hinj
    apply (cancel_mono Z.isoSpec.hom).mp
    have hψij : ψ i = ψ j := by
      apply CommRingCat.hom_ext
      exact congrArg AlgHom.toRingHom hij
    calc a i ≫ Z.isoSpec.hom = Spec.map (ψ i) := (Spec.map_preimage _).symm
      _ = Spec.map (ψ j) := congrArg Spec.map hψij
      _ = a j ≫ Z.isoSpec.hom := Spec.map_preimage _
  have hdim : Fintype.card ι = Module.finrank K Γ(Z, ⊤) := by
    have : IsFinite (Spec.map φ) := (IsFinite.SpecMap_iff φ).mpr hφfin
    have : Flat (Spec.map φ) := Flat.SpecMap_iff.mpr hφflat
    rw [← hfac, Scheme.Hom.finrank_comp_left_of_isIso,
      Scheme.Hom.finrank_SpecMap_eq_finrank hφfin hφflat] at hrank
    change Fintype.card ι = Module.rankAtStalk (R := K) Γ(Z, ⊤) t at hrank
    rw [Module.rankAtStalk_eq_finrank_of_free] at hrank
    exact hrank
  have hsplit : IsIso
      (Sigma.desc fun i => Spec.map (CommRingCat.ofHom (χ i).toRingHom)) :=
    isIso_sigmaDesc_specMap_of_injective_characters K Γ(Z, ⊤) χ hχ hdim
  have heq : Sigma.desc a ≫ Z.isoSpec.hom =
      Sigma.desc fun i => Spec.map (CommRingCat.ofHom (χ i).toRingHom) := by
    apply Sigma.hom_ext
    intro i
    rw [Sigma.ι_comp_desc_assoc, Sigma.ι_comp_desc]
    exact (Spec.map_preimage _).symm
  have : IsIso (Sigma.desc a ≫ Z.isoSpec.hom) := heq ▸ hsplit
  exact IsIso.of_isIso_comp_right (Sigma.desc a) Z.isoSpec.hom

open AlgebraicCurves.RelativeDivisors.Proofs.RelEffCartierDiv_IsUniversal_geometricallyConnected in
private theorem integral_finFibrePow
    {K : Type u} [Field K] {C : Scheme.{u}}
    (c : C ⟶ Spec (CommRingCat.of K)) [Smooth c] [GeometricallyConnected c]
    (r : ℕ) : IsIntegral (finFibrePow c r) := by
  have : MorphismProperty.IsMultiplicative
      (@GeometricallyConnected ⊓ @UniversallyOpen : MorphismProperty Scheme.{u}) :=
    isMultiplicative_geometricallyConnected_inf_universallyOpen
  have : MorphismProperty.IsStableUnderBaseChange (@GeometricallyConnected :
      MorphismProperty Scheme.{u}) := by
    rw [GeometricallyConnected.eq_geometrically, geometrically_eq_universally]
    exact MorphismProperty.universally_isStableUnderBaseChange _
  have : MorphismProperty.IsStableUnderBaseChange (@UniversallyOpen :
      MorphismProperty Scheme.{u}) := by
    rw [UniversallyOpen.eq]
    exact MorphismProperty.universally_isStableUnderBaseChange _
  have : MorphismProperty.IsStableUnderBaseChange
      (@GeometricallyConnected ⊓ @UniversallyOpen : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.inf
  have : MorphismProperty.IsMultiplicative (@Smooth : MorphismProperty Scheme.{u}) :=
    { id_mem := fun X => inferInstance
      comp_mem := fun f g hf hg => by
        have : Smooth f := hf
        have : Smooth g := hg
        infer_instance }
  have hP : (@GeometricallyConnected ⊓ @UniversallyOpen : MorphismProperty Scheme.{u})
      (finFibrePow.toBase c r) :=
    MorphismProperty.widePullback_base
      (P := @GeometricallyConnected ⊓ @UniversallyOpen)
      (fun _ : Fin r => C) (fun _ => c) (fun _ => ⟨inferInstance, inferInstance⟩)
  have : GeometricallyConnected (finFibrePow.toBase c r) := hP.1
  have : Smooth (finFibrePow.toBase c r) :=
    MorphismProperty.widePullback_base (P := @Smooth)
      (fun _ : Fin r => C) (fun _ => c) (fun _ => inferInstance)
  have : ConnectedSpace (finFibrePow c r) :=
    GeometricallyConnected.connectedSpace (finFibrePow.toBase c r)
      (finFibrePow.toBase c r).isOpenMap
  exact isIntegral_of_smooth_of_preconnectedSpace (finFibrePow.toBase c r)

private theorem id_ne_basepoint_constant
    {K : Type u} [Field K] {C : Scheme.{u}}
    (c : C ⟶ Spec (CommRingCat.of K)) [SmoothOfRelativeDimension 1 c]
    (s : Spec (CommRingCat.of K) ⟶ C) : 𝟙 C ≠ c ≫ s := by
  intro heq
  have : Nonempty C := ⟨s (Classical.arbitrary _)⟩
  have : Subsingleton C := ⟨fun x y => by
    calc x = (c ≫ s) x := by rw [← heq]; rfl
      _ = (c ≫ s) y := by
        simp only [Scheme.Hom.comp_apply]
        exact congrArg s (Subsingleton.elim (c x) (c y))
      _ = y := by rw [← heq]; rfl⟩
  have hdim := SmoothOfRelativeDimension.le_topologicalKrullDim c 1
  exact (not_le_of_gt (zero_lt_one : (0 : WithBot ℕ∞) < 1))
    (hdim.trans (topologicalKrullDim_zero_of_discreteTopology C))

private theorem injective_finFibrePow_proj
    {K : Type u} [Field K] {C : Scheme.{u}}
    (c : C ⟶ Spec (CommRingCat.of K)) [SmoothOfRelativeDimension 1 c]
    (s : Spec (CommRingCat.of K) ⟶ C) (hs : s ≫ c = 𝟙 _) (r : ℕ) :
    Function.Injective (finFibrePow.proj c r) := by
  classical
  intro i j hij
  by_contra hne
  let a (k : Fin r) : C ⟶ C := if k = i then 𝟙 C else c ≫ s
  have ha (k : Fin r) : a k ≫ c = c := by
    dsimp only [a]
    split_ifs
    · exact Category.id_comp c
    · rw [Category.assoc, hs, Category.comp_id]
  let v : C ⟶ finFibrePow c r := WidePullback.lift c a ha
  have hi : v ≫ finFibrePow.proj c r i = 𝟙 C := by
    rw [WidePullback.lift_π]
    exact ite_eq_left rfl
  have hj : v ≫ finFibrePow.proj c r j = c ≫ s := by
    rw [WidePullback.lift_π]
    exact ite_eq_right (Ne.symm hne)
  apply id_ne_basepoint_constant c s
  exact hi.symm.trans ((congrArg (v ≫ ·) hij).trans hj)

private theorem injective_finFibrePow_permHom
    {K : Type u} [Field K] {C : Scheme.{u}}
    (c : C ⟶ Spec (CommRingCat.of K)) [SmoothOfRelativeDimension 1 c]
    (s : Spec (CommRingCat.of K) ⟶ C) (hs : s ≫ c = 𝟙 _) (r : ℕ) :
    Function.Injective (finFibrePow.permHom c r) := by
  intro σ τ hστ
  apply inv_injective
  apply Equiv.ext
  intro i
  apply injective_finFibrePow_proj c s hs r
  rw [← finFibrePow.permHom_proj, ← finFibrePow.permHom_proj, hστ]

/-- The finite-sum morphism descends to the actual universal effective-divisor
scheme. The same finite flat sum map retains its scheme-valued kernel criterion.
No reducedness assumption is imposed on schemes testing that criterion. -/
theorem exists_finiteSumMap_desc
    {K : Type u} [Field K] {C B Y : Scheme.{u}}
    (c : C ⟶ Spec (CommRingCat.of K)) [IsSeparated c]
    [SmoothOfRelativeDimension 1 c] [GeometricallyConnected c]
    (s : Spec (CommRingCat.of K) ⟶ C) (hs : s ≫ c = 𝟙 _)
    {b : B ⟶ Spec (CommRingCat.of K)} [IsProper b] [GeometricallyIntegral b]
    (G : RelativeGroupLaw K b) (q : SchemeHomOver c b)
    {r : ℕ} {y : Y ⟶ Spec (CommRingCat.of K)} {D : RelEffCartierDiv c r y}
    (hU : D.IsUniversal) :
    ∃ (σ : finFibrePow c r ⟶ Y) (hσ : σ ≫ y = finFibrePow.toBase c r)
      (sum : SchemeHomOver y b),
      D.I.comap (mapOnProdOver c σ hσ) = fibrePowOver.tautIdeal c r ∧
      IsFinite σ ∧ Flat σ ∧ Surjective σ ∧
      σ ≫ sum.1 = (G.finiteSumMap c q r).1 ∧
      ∀ {T : Scheme.{u}} (g : T ⟶ Spec (CommRingCat.of K))
        (v w : T ⟶ finFibrePow c r)
        (hv : v ≫ finFibrePow.toBase c r = g)
        (hw : w ≫ finFibrePow.toBase c r = g),
        v ≫ σ = w ≫ σ ↔
          SameDivisor c (fun i => v ≫ finFibrePow.proj c r i)
            (fun i => by rw [Category.assoc, finFibrePow.proj_comp, hv])
            (fun i => w ≫ finFibrePow.proj c r i)
            (fun i => by rw [Category.assoc, finFibrePow.proj_comp, hw]) := by
  classical
  have : Smooth c := SmoothOfRelativeDimension.smooth 1 c
  let X : Scheme.{u} := finFibrePow c r
  have : IsIntegral X := integral_finFibrePow c r
  have : IsSeparated (finFibrePow.toBase c r) :=
    MorphismProperty.widePullback_base (P := @IsSeparated)
      (fun _ : Fin r => C) (fun _ => c) (fun _ => inferInstance)
  obtain ⟨σ, hσ, hI, hfin, hflat, hlfp, hsurj, hrank, hkernel⟩ :=
    hU.exists_sumMap_with_sameDivisor_kernel
  let η : Spec (X.residueField (genericPoint X)) ⟶ X :=
    X.fromSpecResidueField (genericPoint X)
  have : QuasiCompact η :=
    ⟨fun U _ _ => (Set.toFinite (η ⁻¹' U)).isCompact⟩
  have : IsDominant η := ⟨by
    rw [denseRange_iff_closure_range]
    change closure (Set.range (X.fromSpecResidueField (genericPoint X))) = Set.univ
    rw [X.range_fromSpecResidueField]
    exact (genericPoint_spec X).def⟩
  have : IsSchemeTheoreticallyDominant η :=
    IsSchemeTheoreticallyDominant.of_isDominant η
  have hperm (τ : Equiv.Perm (Fin r)) : finFibrePow.permHom c r τ ≫ σ = σ := by
    have h := (hkernel (finFibrePow.toBase c r)
      (finFibrePow.permHom c r τ) (𝟙 X)
      (finFibrePow.permHom_toBase c r τ) (Category.id_comp _)).mpr
    refine (h ?_).trans (Category.id_comp σ)
    change prodKerGraph c _ _ = prodKerGraph c _ _
    simp only [finFibrePow.permHom_proj]
    exact prodKerGraph_comp_equiv c τ⁻¹ (finFibrePow.proj c r)
      (finFibrePow.proj_comp c r)
  let R : Scheme.{u} := pullback σ σ
  let p : R ⟶ X := pullback.fst σ σ
  have : IsFinite p := inferInstanceAs (IsFinite (pullback.fst σ σ))
  have : Flat p := inferInstanceAs (Flat (pullback.fst σ σ))
  let Z : Scheme.{u} := pullback p η
  let z : Z ⟶ Spec (X.residueField (genericPoint X)) := pullback.snd p η
  have : IsFinite z := inferInstanceAs (IsFinite (pullback.snd p η))
  let I : Type u := ULift.{u} (Equiv.Perm (Fin r))
  let a (i : I) : Spec (X.residueField (genericPoint X)) ⟶ Z :=
    pullback.lift
      (pullback.lift η (η ≫ finFibrePow.permHom c r i.down)
        (by rw [Category.assoc, hperm]))
      (𝟙 _) (by rw [pullback.lift_fst, Category.id_comp])
  have ha (i : I) : a i ≫ z = 𝟙 _ := pullback.lift_snd _ _ _
  have ha₁ (i : I) : a i ≫ pullback.fst p η ≫ pullback.fst σ σ = η := by
    rw [pullback.lift_fst_assoc, pullback.lift_fst]
  have ha₂ (i : I) : a i ≫ pullback.fst p η ≫ pullback.snd σ σ =
      η ≫ finFibrePow.permHom c r i.down := by
    rw [pullback.lift_fst_assoc, pullback.lift_snd]
  have hainj : Function.Injective a := by
    intro i j hij
    apply ULift.ext
    apply injective_finFibrePow_permHom c s hs r
    apply ext_of_isDominant_of_isSeparated (finFibrePow.toBase c r)
      ((finFibrePow.permHom_toBase c r i.down).trans
        (finFibrePow.permHom_toBase c r j.down).symm) η
    rw [← ha₂ i, ← ha₂ j, hij]
  have hcard : Fintype.card I = z.finrank (Classical.arbitrary _) := by
    rw [Scheme.Hom.finrank_pullback_snd, Scheme.Hom.finrank_pullback_fst, hrank]
    simp only [I, Fintype.card_ulift, Fintype.card_perm, Fintype.card_fin]
  have : IsIso (Sigma.desc a) := isIso_sigmaDesc_of_card_eq_finrank
    (K := X.residueField (genericPoint X)) (Z := Z)
    z a ha hainj (Classical.arbitrary _) hcard
  have : IsReduced (∐ fun _ : I => Spec (X.residueField (genericPoint X))) := by
    apply (IsReduced.iff_of_openCover _ (sigmaOpenCover _)).mpr
    intro i
    change IsReduced (Spec (X.residueField (genericPoint X)))
    infer_instance
  have : IsReduced Z := isReduced_of_isOpenImmersion (inv (Sigma.desc a))
  have : IsReduced R := IsSchemeTheoreticallyDominant.isReduced (pullback.fst p η)
  let e : X ⟶ B := (G.finiteSumMap c q r).1
  have hpair : pullback.fst σ σ ≫ e = pullback.snd σ σ ≫ e := by
    refine ext_of_isDominant_of_isSeparated b ?_ (pullback.fst p η) ?_
    · rw [Category.assoc, Category.assoc, (G.finiteSumMap c q r).2]
      change pullback.fst σ σ ≫ fibrePowOver.toBase c r =
        pullback.snd σ σ ≫ fibrePowOver.toBase c r
      rw [← hσ, ← Category.assoc, ← Category.assoc, pullback.condition]
    · rw [← cancel_epi (Sigma.desc a)]
      apply Sigma.hom_ext
      intro i
      simp only [Sigma.ι_comp_desc_assoc]
      have hleft := congrArg (· ≫ e) (ha₁ i)
      have hright := congrArg (· ≫ e) (ha₂ i)
      have hinv : (η ≫ finFibrePow.permHom c r i.down) ≫ e = η ≫ e := by
        rw [Category.assoc]
        exact congrArg (η ≫ ·) (G.finiteSumMap_permute c q i.down)
      simpa only [Category.assoc] using hleft.trans (hright.trans hinv).symm
  have hequal : ∀ {T : Scheme.{u}} (v w : T ⟶ X), v ≫ σ = w ≫ σ → v ≫ e = w ≫ e := by
    intro T v w hvw
    have h := congrArg (pullback.lift v w hvw ≫ ·) hpair
    simpa only [pullback.lift_fst_assoc, pullback.lift_snd_assoc] using h
  let d : Y ⟶ B := EffectiveEpi.desc σ e hequal
  have hd : σ ≫ d = e := EffectiveEpi.fac σ e hequal
  have hdb : d ≫ b = y := by
    apply (cancel_epi σ).mp
    rw [← Category.assoc, hd]
    exact (G.finiteSumMap c q r).2.trans hσ.symm
  exact ⟨σ, hσ, ⟨d, hdb⟩, hI, hfin, hflat, hsurj, hd, hkernel⟩

/-- Equal effective divisors give the same finite sum of images, for points
valued in any scheme, including nonreduced schemes. -/
theorem sumList_eq_of_sameDivisor
    {K : Type u} [Field K] {C B Y : Scheme.{u}}
    (c : C ⟶ Spec (CommRingCat.of K)) [IsSeparated c]
    [SmoothOfRelativeDimension 1 c] [GeometricallyConnected c]
    (s : Spec (CommRingCat.of K) ⟶ C) (hs : s ≫ c = 𝟙 _)
    {b : B ⟶ Spec (CommRingCat.of K)} [IsProper b] [GeometricallyIntegral b]
    (G : RelativeGroupLaw K b) (q : SchemeHomOver c b)
    {r : ℕ} {y : Y ⟶ Spec (CommRingCat.of K)} {D : RelEffCartierDiv c r y}
    (hU : D.IsUniversal) {T : Scheme.{u}} (g : T ⟶ Spec (CommRingCat.of K))
    (a a' : Fin r → SchemeHomOver g c)
    (h : SameDivisor c (fun i => (a i).1) (fun i => (a i).2)
      (fun i => (a' i).1) (fun i => (a' i).2)) :
    G.sumList g (List.ofFn fun i => NeronModelInfra.schemeHomOverComp (a i) q) =
      G.sumList g (List.ofFn fun i => NeronModelInfra.schemeHomOverComp (a' i) q) := by
  obtain ⟨σ, -, sum, -, -, -, -, hfac, hkernel⟩ :=
    exists_finiteSumMap_desc c s hs G q hU
  let v : T ⟶ finFibrePow c r :=
    WidePullback.lift g (fun i => (a i).1) (fun i => (a i).2)
  let w : T ⟶ finFibrePow c r :=
    WidePullback.lift g (fun i => (a' i).1) (fun i => (a' i).2)
  have hσvw : v ≫ σ = w ≫ σ := by
    apply (hkernel g v w (WidePullback.lift_base _ _ _ _)
      (WidePullback.lift_base _ _ _ _)).mpr
    simpa only [v, w, WidePullback.lift_π] using h
  rw [← G.finiteSumMap_evaluate c q g a, ← G.finiteSumMap_evaluate c q g a']
  apply Subtype.ext
  change v ≫ (G.finiteSumMap c q r).1 = w ≫ (G.finiteSumMap c q r).1
  rw [← hfac, ← Category.assoc, ← Category.assoc, hσvw]

end JacobianVarieties.Albanese
