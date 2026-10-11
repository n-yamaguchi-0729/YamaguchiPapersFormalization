/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_isReduced_pullback_residue_of_forall_isReduced_stalk_quotient.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.AlgebraicGeometry.Properties
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.StructureSheaf
import Mathlib.RingTheory.LocalProperties.Basic
import Mathlib.RingTheory.TensorProduct.Quotient
import Mathlib.RingTheory.LocalRing.ResidueField.Defs

/-!
# is Reduced pullback residue of forall is Reduced stalk quotient
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Schemes.Proofs
namespace isReduced_pullback_residue_of_forall_isReduced_stalk_quotient

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace CFSAux

theorem isReduced_quotient_map_of_forall_isReduced_localization
    {A R : Type*} [CommRing A] [CommRing R] (φ : A →+* R) (I : Ideal A)
    (h : ∀ (𝔮 : Ideal R) [𝔮.IsPrime], I.map φ ≤ 𝔮 →
      IsReduced (Localization.AtPrime 𝔮 ⧸ I.map ((algebraMap R (Localization.AtPrime 𝔮)).comp φ))) :
    IsReduced (R ⧸ I.map φ) := by
  classical
  set J : Ideal R := I.map φ with hJ
  have key : ∀ (x : R) (n : ℕ), x ^ n ∈ J → x ∈ J := by
    intro x n hxn
    refine Ideal.mem_of_localization_maximal fun P hP => ?_
    let _ := hP
    by_cases hle : J ≤ P
    · have hred := h P hle
      have hJmap : I.map ((algebraMap R (Localization.AtPrime P)).comp φ) =
          J.map (algebraMap R (Localization.AtPrime P)) := by rw [hJ, Ideal.map_map]
      rw [hJmap] at hred
      have hnil : IsNilpotent (Ideal.Quotient.mk (J.map (algebraMap R (Localization.AtPrime P)))
          (algebraMap R (Localization.AtPrime P) x)) := by
        refine ⟨n, ?_⟩
        rw [← map_pow, ← map_pow, Ideal.Quotient.eq_zero_iff_mem]
        exact Ideal.mem_map_of_mem _ hxn
      have h0 := hnil.eq_zero
      rwa [Ideal.Quotient.eq_zero_iff_mem] at h0
    · obtain ⟨j, hjJ, hjP⟩ := Set.not_subset.mp hle
      have hunit : IsUnit (algebraMap R (Localization.AtPrime P) j) :=
        IsLocalization.map_units (Localization.AtPrime P) (⟨j, hjP⟩ : P.primeCompl)
      have htop : J.map (algebraMap R (Localization.AtPrime P)) = ⊤ :=
        Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_map_of_mem _ hjJ) hunit
      rw [htop]; exact Submodule.mem_top
  refine ⟨fun y hy => ?_⟩
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
  obtain ⟨n, hn⟩ := hy
  rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem] at hn
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (key x n hn)

theorem isReduced_of_ringEquiv {R S : Type*} [CommRing R] [CommRing S] (e : R ≃+* S) [IsReduced R] :
    IsReduced S :=
  isReduced_of_injective e.symm.toRingHom e.symm.injective

end CFSAux

namespace CFSGlue

variable {A : Type u} [CommRing A] [IsLocalRing A]

theorem base_eq_closedPoint_iff {R : CommRingCat.{u}} (φ : Spec R ⟶ Spec (CommRingCat.of A)) (𝔮 :
  PrimeSpectrum R) :
    φ.base 𝔮 = IsLocalRing.closedPoint A ↔
      (IsLocalRing.maximalIdeal A).map (Spec.preimage φ).hom ≤ 𝔮.asIdeal := by
  set ψ := Spec.preimage φ with hψ
  have hφ : φ = Spec.map ψ := (Spec.map_preimage φ).symm
  have hbase : φ.base 𝔮 = PrimeSpectrum.comap ψ.hom 𝔮 := by
    rw [hφ, Spec.map_base]; rfl
  rw [hbase, Ideal.map_le_iff_le_comap]
  constructor
  · intro h
    have h2 : (PrimeSpectrum.comap ψ.hom 𝔮).asIdeal = (IsLocalRing.closedPoint A).asIdeal :=
      by rw [h]
    rw [PrimeSpectrum.comap_asIdeal] at h2
    rw [← show (IsLocalRing.closedPoint A).asIdeal = IsLocalRing.maximalIdeal A from rfl, ← h2]
  · intro h
    apply PrimeSpectrum.ext
    rw [PrimeSpectrum.comap_asIdeal]
    exact ((IsLocalRing.maximalIdeal.isMaximal A).eq_of_le
      (Ideal.IsPrime.ne_top (Ideal.comap_isPrime ψ.hom 𝔮.asIdeal)) h).symm

theorem isReduced_pullback_affine {R : CommRingCat.{u}} (φ : Spec R ⟶ Spec (CommRingCat.of A))
    (h : ∀ 𝔮 : PrimeSpectrum R, (IsLocalRing.maximalIdeal A).map (Spec.preimage φ).hom ≤ 𝔮.asIdeal →
      _root_.IsReduced (Localization.AtPrime 𝔮.asIdeal ⧸
        (IsLocalRing.maximalIdeal A).map ((algebraMap R (Localization.AtPrime 𝔮.asIdeal)).comp
          (Spec.preimage φ).hom))) :
    IsReduced (pullback φ (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)))) := by
  classical
  set ψ := Spec.preimage φ with hψ
  have hφ : φ = Spec.map ψ := (Spec.map_preimage φ).symm
  let _ : Algebra A R := ψ.hom.toAlgebra
  have hψalg : ψ = CommRingCat.ofHom (algebraMap A R) := rfl
  have hres : CommRingCat.ofHom (IsLocalRing.residue A) =
      CommRingCat.ofHom (algebraMap A (IsLocalRing.ResidueField A)) := rfl
  rw [hφ, hψalg, hres]
  let e := pullbackSpecIso A R (IsLocalRing.ResidueField A)
  let _ : IsReduced (Spec (CommRingCat.of (TensorProduct A R (IsLocalRing.ResidueField A)))) := by
    rw [affine_isReduced_iff]
    let _ : _root_.IsReduced (↑R ⧸ (IsLocalRing.maximalIdeal A).map (algebraMap A R)) := by
      refine CFSAux.isReduced_quotient_map_of_forall_isReduced_localization (algebraMap A R)
        (IsLocalRing.maximalIdeal A) (fun 𝔮 _ hle => ?_)
      exact h ⟨𝔮, inferInstance⟩ hle
    exact CFSAux.isReduced_of_ringEquiv
      (Algebra.TensorProduct.quotIdealMapEquivTensorQuot (R : Type u) (IsLocalRing.maximalIdeal
        A)).toRingEquiv
  exact isReduced_of_isOpenImmersion e.hom

theorem isReduced_localization_quotient_of_stalk {X : Scheme.{u}} (toBase : X ⟶ Spec
  (CommRingCat.of A))
    {R : CommRingCat.{u}} (j : Spec R ⟶ X) [IsOpenImmersion j] (𝔮 : PrimeSpectrum R)
    (hred : _root_.IsReduced (X.presheaf.stalk (j.base 𝔮) ⧸
        Ideal.map ((X.presheaf.germ ⊤ (j.base 𝔮) trivial).hom.comp
          (toBase.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom))
          (IsLocalRing.maximalIdeal A))) :
    _root_.IsReduced (Localization.AtPrime 𝔮.asIdeal ⧸
      (IsLocalRing.maximalIdeal A).map
        ((algebraMap R (Localization.AtPrime 𝔮.asIdeal)).comp (Spec.preimage (j ≫ toBase)).hom)) :=
          by
  classical
  let q : Spec R := 𝔮
  set ψ := Spec.preimage (j ≫ toBase) with hψ
  have hjψ : j ≫ toBase = Spec.map ψ := (Spec.map_preimage _).symm
  set G : CommRingCat.of A ⟶ X.presheaf.stalk (j.base q) :=
    (Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ toBase.appTop ≫ X.presheaf.germ ⊤ (j.base q) trivial
      with hG
  have hstep1 : ∀ t : Γ(X, ⊤), (j.stalkMap q).hom ((X.presheaf.germ ⊤ (j.base q) trivial).hom t) =
      ((Spec R).presheaf.germ ⊤ q trivial).hom ((j.app ⊤).hom t) := by
    intro t
    have h := Scheme.Hom.germ_stalkMap j ⊤ q trivial
    have h' := congrArg (fun f => f.hom t) h
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h'
    exact h'
  have hstep2 : ∀ s : Γ(Spec (CommRingCat.of A), ⊤), (j.app ⊤).hom (toBase.appTop.hom s) =
    (Spec.map ψ).appTop.hom s := by
    intro s
    have h : (j ≫ toBase).appTop = toBase.appTop ≫ j.appTop := rfl
    rw [← hjψ, h]; rfl
  have hstep3 : ∀ a : A, (Spec.map ψ).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a) =
      (Scheme.ΓSpecIso R).inv.hom (ψ.hom a) := by
    intro a
    have h := congrArg (fun f => f.hom a) (Scheme.ΓSpecIso_inv_naturality ψ)
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h
    exact h.symm
  have hstep4 : ∀ r : R, ((Spec R).presheaf.germ ⊤ q trivial).hom ((Scheme.ΓSpecIso R).inv.hom r) =
      (StructureSheaf.toStalk R q).hom r := by
    intro r
    have h := congrArg (fun f => f.hom r) (StructureSheaf.algebraMap_germ (R := R) ⊤ q trivial)
    rw [Scheme.ΓSpecIso_inv]
    exact h
  have hchain : ∀ a : A, (j.stalkMap q).hom (G.hom a) = (StructureSheaf.toStalk R q).hom (ψ.hom a)
    := by
    intro a
    rw [hG]
    simp only [CommRingCat.hom_comp, RingHom.comp_apply]
    rw [hstep1, hstep2, hstep3, hstep4]
  have : IsIso (j.stalkMap q) :=
    LocallyRingedSpace.IsOpenImmersion.stalk_iso j.toLRSHom q
  let e₁ : ↑(X.presheaf.stalk (j.base q)) ≃+* ↑((Spec R).presheaf.stalk q) :=
    (asIso (j.stalkMap q)).commRingCatIsoToRingEquiv
  let e₂ : ↑((Spec R).presheaf.stalk q) ≃+* Localization.AtPrime q.asIdeal :=
    (StructureSheaf.stalkIso R q).symm.toRingEquiv
  let T : ↑(X.presheaf.stalk (j.base q)) ≃+* Localization.AtPrime q.asIdeal := e₁.trans e₂
  have hT : ∀ a : A, T (G.hom a) = algebraMap R (Localization.AtPrime q.asIdeal) (ψ.hom a) := by
    intro a
    have h1 : (j.stalkMap q).hom (G.hom a) = (StructureSheaf.toStalk R q).hom (ψ.hom a) := hchain a
    change e₂ (e₁ (G.hom a)) = _
    have h2 : e₁ (G.hom a) = (j.stalkMap q).hom (G.hom a) := rfl
    rw [h2, h1, ← StructureSheaf.stalkAlgebra_map]
    exact (StructureSheaf.stalkIso R q).symm.commutes (ψ.hom a)
  have hideal : (Ideal.map ((X.presheaf.germ ⊤ (j.base q) trivial).hom.comp
        (toBase.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom))
          (IsLocalRing.maximalIdeal A)).map
        T.toRingHom =
      (IsLocalRing.maximalIdeal A).map ((algebraMap R (Localization.AtPrime q.asIdeal)).comp ψ.hom)
        := by
    rw [Ideal.map_map]
    congr 1
    ext a
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
    rw [← hT a]
    rfl
  rw [← hideal]
  exact CFSAux.isReduced_of_ringEquiv (Ideal.quotientEquiv _ _ T rfl)

theorem isReduced_of_openCover {P : Scheme.{u}} (𝒰 : P.OpenCover) (h : ∀ i, IsReduced (𝒰.X i)) :
    IsReduced P := by
  let _ : ∀ p : P, _root_.IsReduced (P.presheaf.stalk p) := by
    intro p
    obtain ⟨i, y, hy⟩ := 𝒰.exists_eq p
    let _ := h i
    subst hy
    let _ : IsIso ((𝒰.f i).stalkMap y) := inferInstance
    have hbij := ConcreteCategory.bijective_of_isIso ((𝒰.f i).stalkMap y)
    exact isReduced_of_injective ((𝒰.f i).stalkMap y).hom hbij.1
  exact isReduced_of_isReduced_stalk P

end CFSGlue

open CFSGlue in
theorem _root_.AlgebraicGeometry.isReduced_pullback_residue_of_forall_isReduced_stalk_quotient
    {A : Type u} [CommRing A] [IsLocalRing A]
    {X : Scheme.{u}} (toBase : X ⟶ Spec (CommRingCat.of A))
    (h : ∀ x : X, toBase.base x = IsLocalRing.closedPoint A →
      _root_.IsReduced (X.presheaf.stalk x ⧸
        Ideal.map ((X.presheaf.germ ⊤ x trivial).hom.comp
          (toBase.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom))
          (IsLocalRing.maximalIdeal A))) :
    IsReduced (pullback toBase (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)))) := by
  classical
  let g := Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))
  let 𝒱 := X.affineOpenCover
  let 𝒰 := Scheme.Pullback.openCoverOfLeft 𝒱.openCover toBase g
  apply isReduced_of_openCover 𝒰
  intro i
  change IsReduced (pullback (𝒱.f i ≫ toBase) g)
  apply isReduced_pullback_affine (𝒱.f i ≫ toBase)
  intro 𝔮 h𝔮
  have : IsOpenImmersion (𝒱.f i) := 𝒱.openCover.map_prop i
  apply isReduced_localization_quotient_of_stalk toBase (𝒱.f i) 𝔮
  apply h
  have := (base_eq_closedPoint_iff (𝒱.f i ≫ toBase) 𝔮).mpr h𝔮
  exact this
end isReduced_pullback_residue_of_forall_isReduced_stalk_quotient
end AlgebraicCurves.Geometry.Schemes.Proofs
end ProofImplementation
