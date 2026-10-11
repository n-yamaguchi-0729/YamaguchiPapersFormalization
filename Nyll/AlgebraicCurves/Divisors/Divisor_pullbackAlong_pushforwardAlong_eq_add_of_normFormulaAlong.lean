/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_Divisor_pullbackAlong_pushforwardAlong_eq_add_of_normFormulaAlong.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Divisors.Correspondences
import Nyll.AlgebraicCurves.Places.Place_exists_forall_ord_eq_finset
import Mathlib.LinearAlgebra.Charpoly.BaseChange

/-!
# Divisor pullback Along pushforward Along eq add of norm Formula Along
-/

section ProofImplementation

namespace AlgebraicCurves.Divisors.Proofs
namespace Divisor_pullbackAlong_pushforwardAlong_eq_add_of_normFormulaAlong

noncomputable section

open _root_.AlgebraicCurve
open _root_.TensorProduct

namespace AlgebraicCurve
open _root_.AlgebraicCurve
namespace BaseChangeTwo

section Along

variable {K A B C : Type*} [Field K] [Field A] [Field B] [Field C]
  [Algebra K A] [Algebra K B] [Algebra K C]

theorem isIntegral_comp {f : A →ₐ[K] B} {g : B →ₐ[K] C} (hf : f.toRingHom.IsIntegral)
    (hg : g.toRingHom.IsIntegral) : (g.comp f).toRingHom.IsIntegral :=
  RingHom.IsIntegral.trans f.toRingHom g.toRingHom hf hg

theorem restrictAlong_restrictAlong (f : A →ₐ[K] B) (g : B →ₐ[K] C)
    (hf : f.toRingHom.IsIntegral) (hg : g.toRingHom.IsIntegral)
    (hgf : (g.comp f).toRingHom.IsIntegral) (w : Place K C) :
    (w.restrictAlong g hg).restrictAlong f hf = w.restrictAlong (g.comp f) hgf :=
  Place.ext (ValuationSubring.comap_comap _ _ _)

theorem pushforwardAlong_apply [DecidableEq (Place K A)] (f : A →ₐ[K] B)
    (hf : f.toRingHom.IsIntegral) (E : Divisor K B) (v : Place K A) :
    Divisor.pushforwardAlong f hf E v =
      ∑ w ∈ E.support, if w.restrictAlong f hf = v then E w * (w.inertiaDegAlong f hf : ℤ) else 0
        := by
  let := algebraAlong f
  have := isScalarTower_along f
  have := isIntegral_along f hf
  exact Divisor.pushforward_apply E v

theorem pullbackAlong_apply_eq_ord [HasPrincipalDivisors K B] (f : A →ₐ[K] B)
    (hf : f.toRingHom.IsIntegral) {a : A} {D : Divisor K A}
    (hD : ∀ v : Place K A, D v = v.ord a) (w : Place K B) :
    Divisor.pullbackAlong f hf D w = w.ord (f a) := by
  rw [Divisor.pullbackAlong_apply, hD, ← Place.ord_restrictAlong]

theorem pushforwardAlong_apply_eq_ord (f : A →ₐ[K] B) (hf : f.toRingHom.IsIntegral)
    (hfin : FiniteAlong K f) (hN : NormFormulaAlong K f hfin) {b : B} (hb : b ≠ 0)
    {E : Divisor K B} (hE : ∀ w : Place K B, E w = w.ord b) (v : Place K A) :
    Divisor.pushforwardAlong f hf E v = v.ord (letI := algebraAlong f; Algebra.norm A b) := by
  let := algebraAlong f
  have := isScalarTower_along f
  have := isIntegral_along f hf
  have : Module.Finite A B := hfin
  exact hN b hb E hE v

theorem norm_along_ne_zero (f : A →ₐ[K] B) (hfin : FiniteAlong K f) {b : B} (hb : b ≠ 0) :
    (letI := algebraAlong f; Algebra.norm A b) ≠ 0 := by
  let := algebraAlong f
  have : Module.Finite A B := hfin
  exact Algebra.norm_ne_zero_iff.mpr hb

end Along

section Local

variable {K F F₁ F₂ Z : Type*} [Field K] [Field F] [Field F₁] [Field F₂] [Field Z]
  [Algebra K F] [Algebra K F₁] [Algebra K F₂] [Algebra K Z]

theorem pullbackAlong_pushforwardAlong_apply_eq_zero [HasPrincipalDivisors K F₁]
    (φ : F →ₐ[K] F₁) (ψ' : F →ₐ[K] F₂)
    (hφ : φ.toRingHom.IsIntegral) (hψ' : ψ'.toRingHom.IsIntegral)
    (D : Divisor K F₂) (w₁ : Place K F₁)
    (hD : ∀ v : Place K F₂, v.restrictAlong ψ' hψ' = w₁.restrictAlong φ hφ → D v = 0) :
    Divisor.pullbackAlong φ hφ (Divisor.pushforwardAlong ψ' hψ' D) w₁ = 0 := by
  classical
  rw [Divisor.pullbackAlong_apply, pushforwardAlong_apply]
  refine mul_eq_zero_of_right _ (Finset.sum_eq_zero fun v _ => ?_)
  split_ifs with h
  · rw [hD v h, zero_mul]
  · rfl

theorem pushforwardAlong_pullbackAlong_apply_eq_zero [HasPrincipalDivisors K Z]
    (φ : F →ₐ[K] F₁) (ψ' : F →ₐ[K] F₂) (u : F₁ →ₐ[K] Z) (u' : F₂ →ₐ[K] Z)
    (hsq : u.comp φ = u'.comp ψ')
    (hφ : φ.toRingHom.IsIntegral) (hψ' : ψ'.toRingHom.IsIntegral)
    (hu : u.toRingHom.IsIntegral) (hu' : u'.toRingHom.IsIntegral)
    (D : Divisor K F₂) (w₁ : Place K F₁)
    (hD : ∀ v : Place K F₂, v.restrictAlong ψ' hψ' = w₁.restrictAlong φ hφ → D v = 0) :
    Divisor.pushforwardAlong u hu (Divisor.pullbackAlong u' hu' D) w₁ = 0 := by
  classical
  rw [pushforwardAlong_apply]
  refine Finset.sum_eq_zero fun z _ => ?_
  split_ifs with h
  · rw [Divisor.pullbackAlong_apply, hD, mul_zero, zero_mul]
    rw [restrictAlong_restrictAlong ψ' u' hψ' hu' (isIntegral_comp hψ' hu'),
      ← Place.restrictAlong_congr hsq (isIntegral_comp hφ hu) (isIntegral_comp hψ' hu'),
      ← restrictAlong_restrictAlong φ u hφ hu (isIntegral_comp hφ hu), h]
  · rfl

end Local

section Gen

variable {K F₁ Z : Type*} [Field K] [Field F₁] [Field Z] [Algebra K F₁] [Algebra K Z]

theorem subalgebra_eq_top_of_adjoin_eq_top (u : F₁ →ₐ[K] Z) (hufin : FiniteAlong K u)
    (S : Set Z) (hgen : IntermediateField.adjoin K (Set.range u ∪ S) = ⊤)
    (T : letI := algebraAlong u; Subalgebra F₁ Z) (hT : S ⊆ (T : Set Z)) :
    T = ⊤ := by
  let := algebraAlong u
  have := isScalarTower_along u
  have : Module.Finite F₁ Z := hufin
  have : Algebra.IsAlgebraic F₁ Z := Algebra.IsAlgebraic.of_finite F₁ Z
  have hfield : IsField T := Subalgebra.isField_of_algebraic T
  let T' : IntermediateField K Z :=
    { (T.restrictScalars K) with
      inv_mem' := by
        intro x hx
        rcases eq_or_ne x 0 with rfl | hx0
        · rw [inv_zero]; exact (T.restrictScalars K).zero_mem
        · have hxT : (⟨x, hx⟩ : T) ≠ 0 := fun h => hx0 (congrArg Subtype.val h)
          obtain ⟨y, hy⟩ := hfield.mul_inv_cancel hxT
          have hy' : x * (y : Z) = 1 := congrArg Subtype.val hy
          have : x⁻¹ = (y : Z) := inv_eq_of_mul_eq_one_right hy'
          change x⁻¹ ∈ T
          rw [this]
          exact y.2 }
  have hle : IntermediateField.adjoin K (Set.range u ∪ S) ≤ T' := by
    rw [IntermediateField.adjoin_le_iff]
    rintro x (⟨a, rfl⟩ | hx)
    · change u a ∈ T
      exact T.algebraMap_mem a
    · exact hT hx
  rw [hgen, top_le_iff] at hle
  apply Subalgebra.toSubmodule_injective
  apply le_antisymm le_top
  intro x _
  have hx : x ∈ T' := by rw [hle]; exact IntermediateField.mem_top
  exact hx

end Gen

section Tensor

variable {K F F₁ F₂ Z Z' : Type*} [Field K] [Field F] [Field F₁] [Field F₂] [Field Z] [Field Z']
  [Algebra K F] [Algebra K F₁] [Algebra K F₂] [Algebra K Z] [Algebra K Z']


theorem map_norm_eq_norm_mul_norm
    (φ : F →ₐ[K] F₁) (ψ' : F →ₐ[K] F₂)
    (u : F₁ →ₐ[K] Z) (u' : F₂ →ₐ[K] Z) (s : F₁ →ₐ[K] Z') (s' : F₂ →ₐ[K] Z')
    (hsq : u.comp φ = u'.comp ψ') (hsq' : s.comp φ = s'.comp ψ')
    (hψ'fin : FiniteAlong K ψ') (hufin : FiniteAlong K u) (hsfin : FiniteAlong K s)
    (hgen : IntermediateField.adjoin K (Set.range u ∪ Set.range u') = ⊤)
    (hgen' : IntermediateField.adjoin K (Set.range s ∪ Set.range s') = ⊤)
    (hdeg : finrankAlong K u + finrankAlong K s = finrankAlong K ψ')
    (hne : ∃ (a : F₁) (b : F₂), s a = s' b ∧ u a ≠ u' b) (g : F₂) :
    φ (letI := algebraAlong ψ'; Algebra.norm F g) =
      (letI := algebraAlong u; Algebra.norm F₁ (u' g)) *
        (letI := algebraAlong s; Algebra.norm F₁ (s' g)) := by
  let iF1 : Algebra F F₁ := algebraAlong φ
  let iF2 : Algebra F F₂ := algebraAlong ψ'
  let iZ1 : Algebra F₁ Z := algebraAlong u
  let iZ2 : Algebra F₂ Z := algebraAlong u'
  let iZ : Algebra F Z := algebraAlong (u.comp φ)
  let iZ'1 : Algebra F₁ Z' := algebraAlong s
  let iZ'2 : Algebra F₂ Z' := algebraAlong s'
  let iZ' : Algebra F Z' := algebraAlong (s.comp φ)
  have : IsScalarTower F F₁ Z := IsScalarTower.of_algebraMap_eq fun x => rfl
  have : IsScalarTower F F₂ Z :=
    IsScalarTower.of_algebraMap_eq fun x => (AlgHom.congr_fun hsq x : u (φ x) = u' (ψ' x))
  have : IsScalarTower F F₁ Z' := IsScalarTower.of_algebraMap_eq fun x => rfl
  have : IsScalarTower F F₂ Z' :=
    IsScalarTower.of_algebraMap_eq fun x => (AlgHom.congr_fun hsq' x : s (φ x) = s' (ψ' x))
  have : Module.Finite F F₂ := hψ'fin
  have : Module.Finite F₁ Z := hufin
  have : Module.Finite F₁ Z' := hsfin
  let gZ : F₂ →ₐ[F] Z := IsScalarTower.toAlgHom F F₂ Z
  let gZ' : F₂ →ₐ[F] Z' := IsScalarTower.toAlgHom F F₂ Z'
  let PP : F₁ ⊗[F] F₂ →ₐ[F₁] Z × Z' :=
    Algebra.TensorProduct.lift (Algebra.ofId F₁ (Z × Z')) (gZ.prod gZ') (fun _ _ => Commute.all _ _)
  have hPP : ∀ (a : F₁) (b : F₂), PP (a ⊗ₜ b) = (u a * u' b, s a * s' b) := by
    intro a b
    rw [Algebra.TensorProduct.lift_tmul]
    rfl
  let Pfst : F₁ ⊗[F] F₂ →ₐ[F₁] Z := (AlgHom.fst F₁ Z Z').comp PP
  let Psnd : F₁ ⊗[F] F₂ →ₐ[F₁] Z' := (AlgHom.snd F₁ Z Z').comp PP
  have hPfst : ∀ (a : F₁) (b : F₂), Pfst (a ⊗ₜ b) = u a * u' b := fun a b => by
    change (PP (a ⊗ₜ b)).1 = _; rw [hPP]
  have hPsnd : ∀ (a : F₁) (b : F₂), Psnd (a ⊗ₜ b) = s a * s' b := fun a b => by
    change (PP (a ⊗ₜ b)).2 = _; rw [hPP]
  have hsurj₁ : Function.Surjective Pfst := by
    have htop : Pfst.range = ⊤ := by
      refine subalgebra_eq_top_of_adjoin_eq_top u hufin (Set.range u') hgen Pfst.range ?_
      rintro _ ⟨b, rfl⟩
      refine ⟨1 ⊗ₜ b, ?_⟩
      change Pfst (1 ⊗ₜ b) = _
      rw [hPfst, map_one, one_mul]
    exact fun z => by
      have hz : z ∈ Pfst.range := by rw [htop]; exact Algebra.mem_top
      exact hz
  have hsurj₂ : Function.Surjective Psnd := by
    have htop : Psnd.range = ⊤ := by
      refine subalgebra_eq_top_of_adjoin_eq_top s hsfin (Set.range s') hgen' Psnd.range ?_
      rintro _ ⟨b, rfl⟩
      refine ⟨1 ⊗ₜ b, ?_⟩
      change Psnd (1 ⊗ₜ b) = _
      rw [hPsnd, map_one, one_mul]
    exact fun z => by
      have hz : z ∈ Psnd.range := by rw [htop]; exact Algebra.mem_top
      exact hz
  have hmax₁ : (RingHom.ker Pfst.toRingHom).IsMaximal :=
    RingHom.ker_isMaximal_of_surjective Pfst.toRingHom hsurj₁
  have hmax₂ : (RingHom.ker Psnd.toRingHom).IsMaximal :=
    RingHom.ker_isMaximal_of_surjective Psnd.toRingHom hsurj₂
  have hne' : RingHom.ker Pfst.toRingHom ≠ RingHom.ker Psnd.toRingHom := by
    obtain ⟨a, b, hab, hab'⟩ := hne
    intro h
    have hmem : (a ⊗ₜ[F] (1 : F₂) - (1 : F₁) ⊗ₜ[F] b) ∈ RingHom.ker Psnd.toRingHom := by
      rw [RingHom.mem_ker]
      change Psnd _ = 0
      rw [map_sub, hPsnd, hPsnd, map_one, map_one, mul_one, one_mul, hab, sub_self]
    rw [← h, RingHom.mem_ker] at hmem
    apply hab'
    have : Pfst (a ⊗ₜ[F] (1 : F₂) - (1 : F₁) ⊗ₜ[F] b) = 0 := hmem
    rwa [map_sub, hPfst, hPfst, map_one, map_one, mul_one, one_mul, sub_eq_zero] at this
  have hcop : RingHom.ker Pfst.toRingHom ⊔ RingHom.ker Psnd.toRingHom = ⊤ :=
    Ideal.IsMaximal.coprime_of_ne hmax₁ hmax₂ hne'
  obtain ⟨x, hx, y, hy, hxy⟩ := Submodule.mem_sup.mp
    ((Ideal.eq_top_iff_one _).mp hcop)
  have hx₁ : Pfst x = 0 := hx
  have hy₂ : Psnd y = 0 := hy
  have hy₁ : Pfst y = 1 := by
    have := congrArg Pfst hxy
    rwa [map_add, hx₁, zero_add, map_one] at this
  have hx₂ : Psnd x = 1 := by
    have := congrArg Psnd hxy
    rwa [map_add, hy₂, add_zero, map_one] at this
  have hsurj : Function.Surjective PP := by
    rintro ⟨z, z'⟩
    obtain ⟨a₁, rfl⟩ := hsurj₁ z
    obtain ⟨a₂, rfl⟩ := hsurj₂ z'
    refine ⟨a₁ * y + a₂ * x, Prod.ext ?_ ?_⟩
    · change Pfst (a₁ * y + a₂ * x) = Pfst a₁
      rw [map_add, map_mul, map_mul, hy₁, hx₁, mul_one, mul_zero, add_zero]
    · change Psnd (a₁ * y + a₂ * x) = Psnd a₂
      rw [map_add, map_mul, map_mul, hy₂, hx₂, mul_zero, mul_one, zero_add]
  have hdim : Module.finrank F₁ (F₁ ⊗[F] F₂) = Module.finrank F₁ (Z × Z') := by
    rw [Module.finrank_baseChange, Module.finrank_prod]
    exact hdeg.symm
  have hinj : Function.Injective PP :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim (f := PP.toLinearMap)).mpr hsurj
  let e : F₁ ⊗[F] F₂ ≃ₐ[F₁] Z × Z' := AlgEquiv.ofBijective PP ⟨hinj, hsurj⟩
  have hlin : (Algebra.lmul F F₂ g).baseChange F₁ = Algebra.lmul F₁ (F₁ ⊗[F] F₂) ((1 : F₁) ⊗ₜ g) :=
    by
    apply LinearMap.ext
    intro t
    induction t using TensorProduct.inductionOn with
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul a b =>
        rw [LinearMap.baseChange_tmul]
        change a ⊗ₜ (g * b) = ((1 : F₁) ⊗ₜ[F] g) * (a ⊗ₜ[F] b)
        rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  have hprod : Algebra.lmul F₁ (Z × Z') (u' g, s' g) =
      LinearMap.prodMap (Algebra.lmul F₁ Z (u' g)) (Algebra.lmul F₁ Z' (s' g)) := by
    apply LinearMap.ext
    rintro ⟨z, z'⟩
    rfl
  calc φ (Algebra.norm F g)
      = algebraMap F F₁ (LinearMap.det (Algebra.lmul F F₂ g)) := by rw [Algebra.norm_apply]; rfl
    _ = LinearMap.det (Algebra.lmul F₁ (F₁ ⊗[F] F₂) ((1 : F₁) ⊗ₜ g)) := by
        rw [← hlin, LinearMap.det_baseChange]
    _ = Algebra.norm F₁ ((1 : F₁) ⊗ₜ[F] g) := (Algebra.norm_apply F₁ _).symm
    _ = Algebra.norm F₁ (e ((1 : F₁) ⊗ₜ[F] g)) := (Algebra.norm_eq_of_algEquiv e _).symm
    _ = Algebra.norm F₁ ((u' g, s' g) : Z × Z') := by
        congr 1
        change PP ((1 : F₁) ⊗ₜ g) = _
        rw [hPP, map_one, map_one, one_mul, one_mul]
    _ = LinearMap.det (Algebra.lmul F₁ Z (u' g)) * LinearMap.det (Algebra.lmul F₁ Z' (s' g)) := by
        rw [Algebra.norm_apply, hprod, LinearMap.det_prodMap]
    _ = Algebra.norm F₁ (u' g) * Algebra.norm F₁ (s' g) := by
        rw [← Algebra.norm_apply, ← Algebra.norm_apply]

end Tensor

section Main

variable {K F F₁ F₂ Z Z' : Type*} [Field K] [Field F] [Field F₁] [Field F₂] [Field Z] [Field Z']
  [Algebra K F] [Algebra K F₁] [Algebra K F₂] [Algebra K Z] [Algebra K Z']
  [HasPrincipalDivisors K F₁] [HasPrincipalDivisors K F₂]
  [HasPrincipalDivisors K Z] [HasPrincipalDivisors K Z']
  (φ : F →ₐ[K] F₁) (ψ' : F →ₐ[K] F₂)
  (u : F₁ →ₐ[K] Z) (u' : F₂ →ₐ[K] Z) (s : F₁ →ₐ[K] Z') (s' : F₂ →ₐ[K] Z')
  (hsq : u.comp φ = u'.comp ψ') (hsq' : s.comp φ = s'.comp ψ')
  (hφ : φ.toRingHom.IsIntegral) (hψ' : ψ'.toRingHom.IsIntegral)
  (hu : u.toRingHom.IsIntegral) (hu' : u'.toRingHom.IsIntegral)
  (hs : s.toRingHom.IsIntegral) (hs' : s'.toRingHom.IsIntegral)
  (hψ'fin : FiniteAlong K ψ') (hufin : FiniteAlong K u) (hsfin : FiniteAlong K s)
  (hNψ' : NormFormulaAlong K ψ' hψ'fin) (hNu : NormFormulaAlong K u hufin)
  (hNs : NormFormulaAlong K s hsfin)
  (hgen : IntermediateField.adjoin K (Set.range u ∪ Set.range u') = ⊤)
  (hgen' : IntermediateField.adjoin K (Set.range s ∪ Set.range s') = ⊤)
  (hdeg : finrankAlong K u + finrankAlong K s = finrankAlong K ψ')
  (hne : ∃ (a : F₁) (b : F₂), s a = s' b ∧ u a ≠ u' b)

/-- The composition of the indicated divisor pushforward followed by pullback. -/
def lhs : Divisor K F₂ →+ Divisor K F₁ :=
  (Divisor.pullbackAlong φ hφ).comp (Divisor.pushforwardAlong ψ' hψ')

/-- The sum of the two indicated pullback-then-pushforward maps on divisors. -/
def rhs : Divisor K F₂ →+ Divisor K F₁ :=
  (Divisor.pushforwardAlong u hu).comp (Divisor.pullbackAlong u' hu') +
    (Divisor.pushforwardAlong s hs).comp (Divisor.pullbackAlong s' hs')
omit [HasPrincipalDivisors K F₂] in
include hsq hsq' hψ'fin hufin hsfin hNψ' hNu hNs hgen hgen' hdeg hne in
theorem lhs_eq_rhs_of_forall_eq_ord {g : F₂} (hg : g ≠ 0) {D : Divisor K F₂}
    (hD : ∀ v : Place K F₂, D v = v.ord g) :
    lhs φ ψ' hφ hψ' D = rhs u u' s s' hu hu' hs hs' D := by
  ext w₁
  have h1 : ∀ v : Place K F, Divisor.pushforwardAlong ψ' hψ' D v =
      v.ord (letI := algebraAlong ψ'; Algebra.norm F g) :=
    fun v => pushforwardAlong_apply_eq_ord ψ' hψ' hψ'fin hNψ' hg hD v
  have hL : lhs φ ψ' hφ hψ' D w₁ = w₁.ord (φ (letI := algebraAlong ψ'; Algebra.norm F g)) := by
    change Divisor.pullbackAlong φ hφ (Divisor.pushforwardAlong ψ' hψ' D) w₁ = _
    exact pullbackAlong_apply_eq_ord φ hφ h1 w₁
  have hu'g : u' g ≠ 0 := (map_ne_zero u').mpr hg
  have hs'g : s' g ≠ 0 := (map_ne_zero s').mpr hg
  have hR₁ : Divisor.pushforwardAlong u hu (Divisor.pullbackAlong u' hu' D) w₁ =
      w₁.ord (letI := algebraAlong u; Algebra.norm F₁ (u' g)) :=
    pushforwardAlong_apply_eq_ord u hu hufin hNu hu'g
      (fun z => pullbackAlong_apply_eq_ord u' hu' hD z) w₁
  have hR₂ : Divisor.pushforwardAlong s hs (Divisor.pullbackAlong s' hs' D) w₁ =
      w₁.ord (letI := algebraAlong s; Algebra.norm F₁ (s' g)) :=
    pushforwardAlong_apply_eq_ord s hs hsfin hNs hs'g
      (fun z => pullbackAlong_apply_eq_ord s' hs' hD z) w₁
  have hR : rhs u u' s s' hu hu' hs hs' D w₁ =
      w₁.ord (letI := algebraAlong u; Algebra.norm F₁ (u' g)) +
        w₁.ord (letI := algebraAlong s; Algebra.norm F₁ (s' g)) := by
    change (Divisor.pushforwardAlong u hu (Divisor.pullbackAlong u' hu' D) +
      Divisor.pushforwardAlong s hs (Divisor.pullbackAlong s' hs' D)) w₁ = _
    rw [Finsupp.add_apply, hR₁, hR₂]
  rw [hL, hR, map_norm_eq_norm_mul_norm φ ψ' u u' s s' hsq hsq' hψ'fin hufin hsfin hgen hgen' hdeg
    hne g]
  exact Place.ord_mul _ (norm_along_ne_zero u hufin hu'g) (norm_along_ne_zero s hsfin hs'g)
omit [HasPrincipalDivisors K F₂] in
theorem lhs_apply_eq_zero (D : Divisor K F₂) (w₁ : Place K F₁)
    (hD : ∀ v : Place K F₂, v.restrictAlong ψ' hψ' = w₁.restrictAlong φ hφ → D v = 0) :
    lhs φ ψ' hφ hψ' D w₁ = 0 :=
  pullbackAlong_pushforwardAlong_apply_eq_zero φ ψ' hφ hψ' D w₁ hD
omit [HasPrincipalDivisors K F₁] [HasPrincipalDivisors K F₂] in
include hsq hsq' in
theorem rhs_apply_eq_zero (D : Divisor K F₂) (w₁ : Place K F₁)
    (hD : ∀ v : Place K F₂, v.restrictAlong ψ' hψ' = w₁.restrictAlong φ hφ → D v = 0) :
    rhs u u' s s' hu hu' hs hs' D w₁ = 0 := by
  change (Divisor.pushforwardAlong u hu (Divisor.pullbackAlong u' hu' D) +
    Divisor.pushforwardAlong s hs (Divisor.pullbackAlong s' hs' D)) w₁ = 0
  rw [Finsupp.add_apply,
    pushforwardAlong_pullbackAlong_apply_eq_zero φ ψ' u u' hsq hφ hψ' hu hu' D w₁ hD,
    pushforwardAlong_pullbackAlong_apply_eq_zero φ ψ' s s' hsq' hφ hψ' hs hs' D w₁ hD, add_zero]
include hsq hsq' hψ'fin hufin hsfin hNψ' hNu hNs hgen hgen' hdeg hne in
theorem lhs_single_eq_rhs_single (w₂ : Place K F₂) :
    lhs φ ψ' hφ hψ' (Finsupp.single w₂ 1) = rhs u u' s s' hu hu' hs hs' (Finsupp.single w₂ 1) := by
  classical
  set w : Place K F := w₂.restrictAlong ψ' hψ' with hw
  obtain ⟨g, hg, hgS⟩ := AlgebraicCurve.Place.exists_forall_ord_eq_finset
    (Place.fiberAlong ψ' hψ' w) (fun v => if v = w₂ then 1 else 0)
  obtain ⟨D, hD, -⟩ := HasPrincipalDivisors.exists_divisor (K := K) g hg
  set E : Divisor K F₂ := D - Finsupp.single w₂ 1 with hE
  have hDE : D = Finsupp.single w₂ 1 + E := by rw [hE]; abel
  have hEv : ∀ v : Place K F₂, v.restrictAlong ψ' hψ' = w → E v = 0 := by
    intro v hv
    have hvS : v ∈ Place.fiberAlong ψ' hψ' w := Place.mem_fiberAlong.mpr hv
    rw [hE, Finsupp.sub_apply, hD v, hgS v hvS, Finsupp.single_apply]
    by_cases h : v = w₂
    · subst h; simp
    · rw [ite_eq_right h, ite_eq_right (Ne.symm h), sub_zero]
  have hprin := lhs_eq_rhs_of_forall_eq_ord φ ψ' u u' s s' hsq hsq' hφ hψ' hu hu' hs hs'
    hψ'fin hufin hsfin hNψ' hNu hNs hgen hgen' hdeg hne hg hD
  rw [hDE, map_add, map_add] at hprin
  ext w₁
  have hpw := congrArg (fun T : Divisor K F₁ => T w₁) hprin
  simp only [Finsupp.add_apply] at hpw
  by_cases h : w₁.restrictAlong φ hφ = w
  · have hE₁ : lhs φ ψ' hφ hψ' E w₁ = 0 :=
      lhs_apply_eq_zero φ ψ' hφ hψ' E w₁ fun v hv => hEv v (hv.trans h)
    have hE₂ : rhs u u' s s' hu hu' hs hs' E w₁ = 0 :=
      rhs_apply_eq_zero φ ψ' u u' s s' hsq hsq' hφ hψ' hu hu' hs hs' E w₁ fun v hv => hEv v
        (hv.trans h)
    rwa [hE₁, hE₂, add_zero, add_zero] at hpw
  · have hsv : ∀ v : Place K F₂, v.restrictAlong ψ' hψ' = w₁.restrictAlong φ hφ →
        (Finsupp.single w₂ (1 : ℤ)) v = 0 := by
      intro v hv
      rw [Finsupp.single_apply, ite_eq_right]
      rintro rfl
      exact h (hv.symm.trans hw.symm)
    rw [lhs_apply_eq_zero φ ψ' hφ hψ' _ w₁ hsv,
      rhs_apply_eq_zero φ ψ' u u' s s' hsq hsq' hφ hψ' hu hu' hs hs' _ w₁ hsv]
include hsq hsq' hψ'fin hufin hsfin hNψ' hNu hNs hgen hgen' hdeg hne in
theorem lhs_eq_rhs : lhs φ ψ' hφ hψ' = rhs u u' s s' hu hu' hs hs' := by
  refine Finsupp.addHom_ext' fun w₂ => AddMonoidHom.ext_int ?_
  simpa using lhs_single_eq_rhs_single φ ψ' u u' s s' hsq hsq' hφ hψ' hu hu' hs hs'
    hψ'fin hufin hsfin hNψ' hNu hNs hgen hgen' hdeg hne w₂

end Main

end BaseChangeTwo
end AlgebraicCurve

end

open _root_.AlgebraicCurve AlgebraicCurve in
theorem _root_.AlgebraicCurve.Divisor.pullbackAlong_pushforwardAlong_eq_add_of_normFormulaAlong
    {K F F₁ F₂ Z Z' : Type*} [Field K] [Field F] [Field F₁] [Field F₂] [Field Z] [Field Z']
    [Algebra K F] [Algebra K F₁] [Algebra K F₂] [Algebra K Z] [Algebra K Z']
    [HasPrincipalDivisors K F₁] [HasPrincipalDivisors K F₂]
    [HasPrincipalDivisors K Z] [HasPrincipalDivisors K Z']
    (φ : F →ₐ[K] F₁) (ψ' : F →ₐ[K] F₂)
    (u : F₁ →ₐ[K] Z) (u' : F₂ →ₐ[K] Z) (s : F₁ →ₐ[K] Z') (s' : F₂ →ₐ[K] Z')
    (hsq : u.comp φ = u'.comp ψ') (hsq' : s.comp φ = s'.comp ψ')
    (hφ : φ.toRingHom.IsIntegral) (hψ' : ψ'.toRingHom.IsIntegral)
    (hu : u.toRingHom.IsIntegral) (hu' : u'.toRingHom.IsIntegral)
    (hs : s.toRingHom.IsIntegral) (hs' : s'.toRingHom.IsIntegral)
    (hψ'fin : FiniteAlong K ψ') (hufin : FiniteAlong K u) (hsfin : FiniteAlong K s)
    (hNψ' : NormFormulaAlong K ψ' hψ'fin) (hNu : NormFormulaAlong K u hufin)
    (hNs : NormFormulaAlong K s hsfin)
    (hgen : IntermediateField.adjoin K (Set.range u ∪ Set.range u') = ⊤)
    (hgen' : IntermediateField.adjoin K (Set.range s ∪ Set.range s') = ⊤)
    (hdeg : finrankAlong K u + finrankAlong K s = finrankAlong K ψ')
    (hne : ∃ (a : F₁) (b : F₂), s a = s' b ∧ u a ≠ u' b)
    (D : Divisor K F₂) :
    Divisor.pullbackAlong φ hφ (Divisor.pushforwardAlong ψ' hψ' D)
      = Divisor.pushforwardAlong u hu (Divisor.pullbackAlong u' hu' D)
        + Divisor.pushforwardAlong s hs (Divisor.pullbackAlong s' hs' D) := by
  have h := AlgebraicCurve.BaseChangeTwo.lhs_eq_rhs φ ψ' u u' s s' hsq hsq' hφ hψ' hu hu' hs hs'
    hψ'fin hufin hsfin hNψ' hNu hNs hgen hgen' hdeg hne
  exact congrArg (fun T : Divisor K F₂ →+ Divisor K F₁ => T D) h
end Divisor_pullbackAlong_pushforwardAlong_eq_add_of_normFormulaAlong
end AlgebraicCurves.Divisors.Proofs
end ProofImplementation
