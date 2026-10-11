/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_ringKrullDim_stalk_eq_of_locallyQuasiFinite_endomorphism.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Batteries.Tactic.Init
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Algebra.Algebra.Hom
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.Algebra.Algebra.Tower
import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Algebra.Group.Monoid
import Mathlib.Algebra.Group.Submonoid.Membership
import Mathlib.Algebra.GroupWithZero.NonZeroDivisors
import Mathlib.Algebra.Module.Submodule.Lattice
import Mathlib.Algebra.NeZero
import Mathlib.Algebra.Ring.Hom.Defs
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.Data.Set.Disjoint
import Mathlib.GroupTheory.MonoidLocalization.Away
import Mathlib.GroupTheory.OreLocalization.Basic
import Mathlib.Order.BoundedOrder.Basic
import Mathlib.Order.Defs.PartialOrder
import Mathlib.RingTheory.Algebraic.Basic
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.RingTheory.AlgebraicIndependent.Basic
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.RingTheory.AlgebraicIndependent.Transcendental
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.RingTheory.Ideal.Height
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Ideal.Over
import Mathlib.RingTheory.Ideal.Prime
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.RingTheory.IntegralClosure.Algebra.Defs
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Localization.Basic
import Mathlib.RingTheory.Localization.Defs
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.RingTheory.OreLocalization.Ring
import Mathlib.RingTheory.QuasiFinite.Basic
import Mathlib.RingTheory.Spectrum.Prime.Defs
import Mathlib.RingTheory.ZariskisMainTheorem
import Mathlib.Tactic.Conv
import Mathlib.Topology.Sheaves.CommRingCat
import Mathlib.Topology.Sheaves.Stalks
import Mathlib.Topology.Sober
import Nyll.AlgebraicCurves.Foundations.CommutativeAlgebra.Ideal_height_eq_height_under_of_finiteType_of_isIntegral
import Nyll.AlgebraicCurves.Foundations.Algebra.Algebra_trdeg_quotient_lt

/-!
# ring Krull Dim stalk eq of locally Quasi Finite endomorphism
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Schemes.Proofs
namespace ringKrullDim_stalk_eq_of_locallyQuasiFinite_endomorphism

universe u

open CategoryTheory AlgebraicGeometry


namespace LQFheight


open _root_.Algebra


theorem height_eq_height_under_of_quasiFiniteAt
    (k A B : Type u) [Field k] [CommRing A] [IsDomain A] [Algebra k A] [Algebra.FiniteType k A]
    [CommRing B] [IsDomain B] [Algebra k B] [Algebra.FiniteType k B]
    [Algebra A B] [IsScalarTower k A B] [FaithfulSMul A B]
    (q : Ideal B) [q.IsPrime] [Algebra.QuasiFiniteAt A q] :
    q.height = (q.under A).height := by
  have : Algebra.FiniteType A B := Algebra.FiniteType.of_restrictScalars_finiteType k A B
  obtain ⟨S', hfg, r, hrq, hbij⟩ :=
    Algebra.QuasiFiniteAt.exists_fg_and_exists_notMem_and_awayMap_bijective (R := A) q
  have : Module.Finite A S' := ⟨(Submodule.fg_top _).mpr hfg⟩
  have : Algebra.IsIntegral A S' := Algebra.IsIntegral.of_finite A S'
  have : IsDomain S' := inferInstance
  let : Algebra k S' := inferInstance
  have : IsScalarTower k A S' := inferInstance
  have : Algebra.FiniteType k S' := Algebra.FiniteType.trans (S := A) inferInstance
    inferInstance
  have : FaithfulSMul A S' := by
    rw [faithfulSMul_iff_algebraMap_injective]
    intro a b hab
    apply (faithfulSMul_iff_algebraMap_injective A B).mp inferInstance
    have := congrArg (fun s : S' => (s : B)) hab
    simpa using this
  let q₁ : Ideal S' := q.under S'
  have : q₁.IsPrime := Ideal.IsPrime.under S' q
  have h1 : q₁.height = (q₁.under A).height :=
    Ideal.height_eq_height_under_of_finiteType_of_isIntegral k A S' q₁
  have h1' : q₁.under A = q.under A := by
    rw [Ideal.under_under]
  have hrB : ((r : B)) ∉ q := hrq
  let Br : Type u := Localization.Away (S'.val.toRingHom r)
  let : Algebra S' Br := inferInstance
  have : IsScalarTower S' B Br := inferInstance
  let φ : Localization.Away r →ₐ[S'] Br :=
    { Localization.awayMap S'.val.toRingHom r with
      commutes' := fun s => by
        change Localization.awayMap S'.val.toRingHom r (algebraMap S' (Localization.Away r) s) =
          algebraMap B Br (S'.val.toRingHom s)
        simp only [Localization.awayMap, IsLocalization.Away.map]
        exact IsLocalization.map_eq _ s }
  let eφ : Localization.Away r ≃ₐ[S'] Br := AlgEquiv.ofBijective φ hbij
  have : IsLocalization (Submonoid.powers r) Br :=
    IsLocalization.isLocalization_of_algEquiv (Submonoid.powers r) eφ
  have : IsLocalization (Submonoid.powers (S'.val.toRingHom r)) Br := inferInstance
  let J : Ideal Br := q.map (algebraMap B Br)
  have hdisj : Disjoint (Submonoid.powers (S'.val.toRingHom r) : Set B) (q : Set B) := by
    rw [Set.disjoint_left]
    rintro _ ⟨n, rfl⟩ hmem
    exact hrB ((inferInstance : q.IsPrime).mem_of_pow_mem n hmem)
  have : J.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint _ Br q inferInstance hdisj
  have hJB : J.under B = q := IsLocalization.under_map_of_isPrime_disjoint _ Br inferInstance hdisj
  have hJS' : J.under S' = q₁ := by
    rw [← Ideal.under_under (B := B) J, hJB]
  have h2 : q.height = q₁.height := by
    rw [← hJB, IsLocalization.height_under (Submonoid.powers (S'.val.toRingHom r)) J, ← hJS',
      IsLocalization.height_under (Submonoid.powers r) J]
  rw [h2, h1, h1']


theorem injective_of_quasiFiniteAt_of_trdeg_eq
    (k A B : Type u) [Field k] [CommRing A] [IsDomain A] [Algebra k A] [Algebra.FiniteType k A]
    [CommRing B] [IsDomain B] [Algebra k B] [Algebra.FiniteType k B]
    [Algebra A B] [IsScalarTower k A B]
    (htr : Algebra.trdeg k A = Algebra.trdeg k B)
    (q : Ideal B) [q.IsPrime] [Algebra.QuasiFiniteAt A q] :
    Function.Injective (algebraMap A B) := by
  have : Algebra.FiniteType A B := Algebra.FiniteType.of_restrictScalars_finiteType k A B
  obtain ⟨S', hfg, r, hrq, hbij⟩ :=
    Algebra.QuasiFiniteAt.exists_fg_and_exists_notMem_and_awayMap_bijective (R := A) q
  have : Module.Finite A S' := ⟨(Submodule.fg_top _).mpr hfg⟩
  have : Algebra.IsIntegral A S' := Algebra.IsIntegral.of_finite A S'
  have : IsDomain S' := inferInstance
  have hr0 : (r : B) ≠ 0 := fun h => hrq (h ▸ q.zero_mem)
  have hr0' : (r : S') ≠ 0 := fun h => hr0 (by rw [h]; rfl)
  let Br : Type u := Localization.Away (S'.val.toRingHom r)
  let φ : Localization.Away r →ₐ[S'] Br :=
    { Localization.awayMap S'.val.toRingHom r with
      commutes' := fun s => by
        change Localization.awayMap S'.val.toRingHom r (algebraMap S' (Localization.Away r) s) =
          algebraMap B Br (S'.val.toRingHom s)
        simp only [Localization.awayMap, IsLocalization.Away.map]
        exact IsLocalization.map_eq _ s }
  have : IsLocalization (Submonoid.powers r) Br :=
    IsLocalization.isLocalization_of_algEquiv (Submonoid.powers r) (AlgEquiv.ofBijective φ hbij)
  have hle : Submonoid.powers (S'.val.toRingHom r) ≤ nonZeroDivisors B :=
    powers_le_nonZeroDivisors_of_noZeroDivisors hr0
  have hle' : Submonoid.powers r ≤ nonZeroDivisors S' :=
    powers_le_nonZeroDivisors_of_noZeroDivisors hr0'
  have : IsDomain Br := IsLocalization.isDomain_of_le_nonZeroDivisors _ hle
  have : FaithfulSMul B Br := (faithfulSMul_iff_algebraMap_injective B Br).mpr
    (IsLocalization.injective Br hle)
  have : FaithfulSMul S' Br :=
    (faithfulSMul_iff_algebraMap_injective S' Br).mpr (IsLocalization.injective Br hle')
  have : Algebra.IsAlgebraic B Br := IsLocalization.isAlgebraic Br (Submonoid.powers
    (S'.val.toRingHom r))
  have : Algebra.IsAlgebraic S' Br := IsLocalization.isAlgebraic Br (Submonoid.powers r)
  have hB : Algebra.trdeg k B = Algebra.trdeg k Br := by
    have := trdeg_add_eq k B (A := Br)
    rwa [trdeg_eq_zero (R := B) (A := Br), add_zero] at this
  have hS : Algebra.trdeg k S' = Algebra.trdeg k Br := by
    have := trdeg_add_eq k S' (A := Br)
    rwa [trdeg_eq_zero (R := S') (A := Br), add_zero] at this
  rw [RingHom.injective_iff_ker_eq_bot]
  by_contra hker
  let I : Ideal A := RingHom.ker (algebraMap A S')
  have hIB : RingHom.ker (algebraMap A B) = I := by
    ext a
    simp only [I, RingHom.mem_ker]
    exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
  have hIbot : I ≠ ⊥ := fun h => hker (hIB.trans h)
  have hItop : I ≠ ⊤ := by
    intro h
    have h1 : (1 : A) ∈ I := h ▸ Submodule.mem_top
    rw [RingHom.mem_ker, map_one] at h1
    exact one_ne_zero h1
  let : Algebra (A ⧸ I) S' := (RingHom.kerLift (algebraMap A S')).toAlgebra
  have hmk : ∀ a : A, algebraMap (A ⧸ I) S' (Ideal.Quotient.mk I a) = algebraMap A S' a := fun a =>
    RingHom.kerLift_mk (algebraMap A S') a
  have : IsScalarTower A (A ⧸ I) S' := IsScalarTower.of_algebraMap_eq (fun a => (hmk a).symm)
  have : IsScalarTower k (A ⧸ I) S' := IsScalarTower.of_algebraMap_eq (fun c => by
    rw [IsScalarTower.algebraMap_apply k A S', IsScalarTower.algebraMap_apply k A (A ⧸ I),
      Ideal.Quotient.algebraMap_eq, hmk])
  have : FaithfulSMul (A ⧸ I) S' :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (RingHom.kerLift_injective (algebraMap A S'))
  have : Nontrivial (A ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hItop
  have : Algebra.IsIntegral (A ⧸ I) S' := Algebra.IsIntegral.tower_top A
  have : Algebra.IsAlgebraic (A ⧸ I) S' := Algebra.IsIntegral.isAlgebraic
  have hQ : Algebra.trdeg k (A ⧸ I) = Algebra.trdeg k S' := by
    have := trdeg_add_eq k (A ⧸ I) (A := S')
    rwa [trdeg_eq_zero (R := A ⧸ I) (A := S'), add_zero] at this
  have hlt : Algebra.trdeg k (A ⧸ I) < Algebra.trdeg k A := Algebra.trdeg_quotient_lt I hIbot hItop
  rw [hQ, hS, ← hB, ← htr] at hlt
  exact lt_irrefl _ hlt

end LQFheight

namespace LQFdimEndo

open CategoryTheory AlgebraicGeometry

variable {k : Type u} [Field k] {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of k)}

/-- The base-ring homomorphism to sections on an open induced by the scheme structure morphism. -/
noncomputable def secAlg (f : X ⟶ Spec (CommRingCat.of k)) (U : X.Opens) : k →+* Γ(X, U) :=
  (f.appLE ⊤ U le_top).hom.comp (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom

theorem appLE_comp_secAlg (h : X ⟶ X) (hov : h ≫ f = f) (U V : X.Opens) (e : V ≤ h ⁻¹ᵁ U) :
    (h.appLE U V e).hom.comp (secAlg f U) = secAlg f V := by
  unfold secAlg
  rw [← RingHom.comp_assoc]
  congr 1
  have : f.appLE ⊤ U le_top ≫ h.appLE U V e = f.appLE ⊤ V le_top := by
    erw [Scheme.Hom.appLE_comp_appLE]
    conv_rhs => rw [← hov]
  exact congrArg (fun g => g.hom) this

theorem germ_comp_secAlg (U : X.Opens) (x : X) (hx : x ∈ U) :
    (X.presheaf.germ U x hx).hom.comp (secAlg f U) =
      ((Spec (CommRingCat.of k)).presheaf.germ ⊤ (f.base x) trivial ≫ f.stalkMap x).hom.comp
        (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom := by
  unfold secAlg
  rw [← RingHom.comp_assoc]
  congr 1
  have := Scheme.Hom.germ_stalkMap f ⊤ x trivial
  have h2 : f.appLE ⊤ U le_top ≫ X.presheaf.germ U x hx =
      (Spec (CommRingCat.of k)).presheaf.germ ⊤ (f.base x) trivial ≫ f.stalkMap x := by
    erw [Scheme.Hom.appLE, Category.assoc, X.presheaf.germ_res, ← this]
  exact congrArg (fun g => g.hom) h2

theorem main [LocallyOfFiniteType f] [IsIntegral X]
    (h : X ⟶ X) (hov : h ≫ f = f) [LocallyQuasiFinite h] (x : X) :
    ringKrullDim (X.presheaf.stalk x) = ringKrullDim (X.presheaf.stalk (h.base x)) := by
  obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset (X := X) (x := h.base x) (U := ⊤)
    trivial
  have hxU' : x ∈ h ⁻¹ᵁ U := hxU
  obtain ⟨V, hV, hxV, hVsub⟩ := exists_isAffineOpen_mem_and_subset (X := X) (x := x) (U := h ⁻¹ᵁ U)
    hxU'
  have hVU : V ≤ h ⁻¹ᵁ U := hVsub
  have : Nonempty U := ⟨⟨h.base x, hxU⟩⟩
  have : Nonempty V := ⟨⟨x, hxV⟩⟩
  let A : Type u := Γ(X, U)
  let B : Type u := Γ(X, V)
  let : Algebra k A := (secAlg f U).toAlgebra
  let : Algebra k B := (secAlg f V).toAlgebra
  let : Algebra A B := (h.appLE U V hVU).hom.toAlgebra
  have : IsScalarTower k A B := IsScalarTower.of_algebraMap_eq' (appLE_comp_secAlg h hov U V
    hVU).symm
  have hftA : (secAlg f U).FiniteType :=
    (f.finiteType_appLE (U := ⊤) (isAffineOpen_top _) hU le_top).comp
      (RingHom.FiniteType.of_surjective _ (Scheme.ΓSpecIso (CommRingCat.of
        k)).commRingCatIsoToRingEquiv.symm.surjective)
  have hftB : (secAlg f V).FiniteType :=
    (f.finiteType_appLE (U := ⊤) (isAffineOpen_top _) hV le_top).comp
      (RingHom.FiniteType.of_surjective _ (Scheme.ΓSpecIso (CommRingCat.of
        k)).commRingCatIsoToRingEquiv.symm.surjective)
  have : Algebra.FiniteType k A := hftA
  have : Algebra.FiniteType k B := hftB
  let q : Ideal B := (hV.primeIdealOf ⟨x, hxV⟩).asIdeal
  let p : Ideal A := (hU.primeIdealOf ⟨h.base x, hxU⟩).asIdeal
  have : Algebra.QuasiFiniteAt A q := (h.quasiFiniteAt x).quasiFiniteAt hV hU hVU hxV
  let K : Type u := X.functionField
  have : IsFractionRing A K := functionField_isFractionRing_of_isAffineOpen X U hU
  have : IsFractionRing B K := functionField_isFractionRing_of_isAffineOpen X V hV
  let : Algebra k K := ((algebraMap A K).comp (secAlg f U)).toAlgebra
  have : IsScalarTower k A K := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower k B K := by
    apply IsScalarTower.of_algebraMap_eq'
    change (algebraMap A K).comp (secAlg f U) = (algebraMap B K).comp (secAlg f V)
    change (X.presheaf.germ U (genericPoint X) _).hom.comp (secAlg f U) =
      (X.presheaf.germ V (genericPoint X) _).hom.comp (secAlg f V)
    rw [germ_comp_secAlg, germ_comp_secAlg]
  have : FaithfulSMul A K := (faithfulSMul_iff_algebraMap_injective A K).mpr
    (IsFractionRing.injective A K)
  have : FaithfulSMul B K := (faithfulSMul_iff_algebraMap_injective B K).mpr
    (IsFractionRing.injective B K)
  have : Algebra.IsAlgebraic A K := IsLocalization.isAlgebraic K (nonZeroDivisors A)
  have : Algebra.IsAlgebraic B K := IsLocalization.isAlgebraic K (nonZeroDivisors B)
  have htrA : Algebra.trdeg k A = Algebra.trdeg k K := by
    have := trdeg_add_eq k A (A := K)
    rwa [trdeg_eq_zero (R := A) (A := K), add_zero] at this
  have htrB : Algebra.trdeg k B = Algebra.trdeg k K := by
    have := trdeg_add_eq k B (A := K)
    rwa [trdeg_eq_zero (R := B) (A := K), add_zero] at this
  have htr : Algebra.trdeg k A = Algebra.trdeg k B := htrA.trans htrB.symm
  have : FaithfulSMul A B := (faithfulSMul_iff_algebraMap_injective A B).mpr
    (LQFheight.injective_of_quasiFiniteAt_of_trdeg_eq k A B htr q)
  have hheight : q.height = (q.under A).height :=
    LQFheight.height_eq_height_under_of_quasiFiniteAt k A B q
  have hpq : q.under A = p := by
    have hc := IsAffineOpen.comap_primeIdealOf_appLE (f := h) U hU V hV hVU hxV
    exact congrArg PrimeSpectrum.asIdeal hc
  let xV : V := ⟨x, hxV⟩
  let yU : U := ⟨h.base x, hxU⟩
  let : Algebra B (X.presheaf.stalk (xV : X)) := TopCat.Presheaf.algebra_section_stalk X.presheaf xV
  let : Algebra A (X.presheaf.stalk (yU : X)) := TopCat.Presheaf.algebra_section_stalk X.presheaf yU
  have : IsLocalization.AtPrime (X.presheaf.stalk (xV : X)) q := hV.isLocalization_stalk xV
  have : IsLocalization.AtPrime (X.presheaf.stalk (yU : X)) p := hU.isLocalization_stalk yU
  change ringKrullDim (X.presheaf.stalk (xV : X)) = ringKrullDim (X.presheaf.stalk (yU : X))
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height q (X.presheaf.stalk (xV : X)),
    IsLocalization.AtPrime.ringKrullDim_eq_height p (X.presheaf.stalk (yU : X)), hheight, hpq]

end LQFdimEndo

theorem _root_.AlgebraicGeometry.ringKrullDim_stalk_eq_of_locallyQuasiFinite_endomorphism
    {k : Type u} [Field k] {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of k)}
    [LocallyOfFiniteType f] [IsIntegral X]
    (h : X ⟶ X) (hov : h ≫ f = f) [LocallyQuasiFinite h] (x : X) :
    ringKrullDim (X.presheaf.stalk x) = ringKrullDim (X.presheaf.stalk (h.base x)) :=
  LQFdimEndo.main h hov x
end AlgebraicCurves.Geometry.Schemes.Proofs.ringKrullDim_stalk_eq_of_locallyQuasiFinite_endomorphism
end ProofImplementation
