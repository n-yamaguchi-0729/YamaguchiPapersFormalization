/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Purity.Local.AdicCompletionTorsionReflection
import Nyll.EtaleFundamentalGroups.Purity.Local.MaximalAdicCompletion
import Nyll.EtaleFundamentalGroups.Purity.PuncturedSpectrumCover
import Mathlib.Algebra.Module.LocalizedModule.Basic
import Mathlib.RingTheory.Finiteness.Ideal

/-!
# The mixed completion/localization equalizer

For a Noetherian local ring, a module is the fibre product of its
maximal-adic completion and its restrictions to the chosen principal cover
of the punctured spectrum.  The overlap is computed by localizing the
completed module at the same generators.
-/

noncomputable section

namespace EtaleFundamentalGroups

open IsLocalRing
open scoped TensorProduct

universe u v w

/-- If an element vanishes after localization at each member of a finite
family spanning `I`, then some power of `I` annihilates it. -/
theorem exists_pow_annihilates_of_localizedModule_mk_eq_zero
    {R : Type u} [CommRing R] {M : Type v}
    [AddCommGroup M] [Module R M]
    {I : Ideal R} (hI : I.FG) {ι : Type w} [Finite ι]
    (f : ι → R) (hspan : Ideal.span (Set.range f) = I)
    (x : M)
    (hx : ∀ i, LocalizedModule.mkLinearMap (Submonoid.powers (f i)) M x = 0) :
    ∃ n : ℕ, ∀ r : (I ^ n : Ideal R), r.1 • x = 0 := by
  let A : Ideal R := (Submodule.span R {x}).annihilator
  have hf : ∀ i, f i ∈ A.radical := by
    intro i
    rw [Ideal.mem_radical_iff]
    obtain ⟨s, hs⟩ := (IsLocalizedModule.eq_zero_iff
      (Submonoid.powers (f i))
      (LocalizedModule.mkLinearMap (Submonoid.powers (f i)) M)).mp (hx i)
    obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff s.1 (f i)).mp s.2
    refine ⟨n, (Submodule.mem_annihilator_span_singleton x _).mpr ?_⟩
    simpa only [Submonoid.smul_def, hn] using hs
  have hle : I ≤ A.radical := by
    rw [← hspan]
    exact Ideal.span_le.mpr fun _ ⟨i, hi⟩ ↦ hi ▸ hf i
  obtain ⟨n, hn⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hle hI
  refine ⟨n, fun r ↦ ?_⟩
  exact (Submodule.mem_annihilator_span_singleton x r.1).mp (hn r.2)

section MaximalAdic

variable (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
variable (M : Type v) [AddCommGroup M] [Module R M]

private abbrev Rhat := AdicCompletion (maximalIdeal R) R

private abbrev GeneratorIndex :=
  AlgebraicGeometry.Scheme.puncturedSpectrumGeneratorIndex R

private abbrev generator (i : GeneratorIndex R) : R :=
  AlgebraicGeometry.Scheme.puncturedSpectrumGenerator R i

/-- The completion component together with localized components on the
chosen principal cover of the punctured spectrum. -/
abbrev MaximalAdicCompletionMixedSource :=
  (Rhat R ⊗[R] M) ×
    ((i : GeneratorIndex R) →
      LocalizedModule (Submonoid.powers (generator R i)) M)

/-- The common overlap of the completion and punctured-localization
components. -/
abbrev MaximalAdicCompletionMixedTarget :=
  (i : GeneratorIndex R) →
    LocalizedModule (Submonoid.powers (generator R i)) (Rhat R ⊗[R] M)

/-- Restrict the completed component to every chosen principal open. -/
def maximalAdicCompletionMixedLeft :
    MaximalAdicCompletionMixedSource R M →ₗ[R]
      MaximalAdicCompletionMixedTarget R M :=
  LinearMap.pi fun i ↦
    (LocalizedModule.mkLinearMap
      (Submonoid.powers (generator R i)) (Rhat R ⊗[R] M)).comp
      (LinearMap.fst R _ _)

/-- Extend every punctured-localization component to the completed module. -/
def maximalAdicCompletionMixedRight :
    MaximalAdicCompletionMixedSource R M →ₗ[R]
      MaximalAdicCompletionMixedTarget R M :=
  LinearMap.pi fun i ↦
    (IsLocalizedModule.map (Submonoid.powers (generator R i))
      (LocalizedModule.mkLinearMap (Submonoid.powers (generator R i)) M)
      (LocalizedModule.mkLinearMap (Submonoid.powers (generator R i))
        (Rhat R ⊗[R] M))
      (TensorProduct.mk R (Rhat R) M 1)).comp
      ((LinearMap.proj i).comp (LinearMap.snd R _ _))

omit [IsNoetherianRing R] in
@[simp]
theorem maximalAdicCompletionMixedLeft_apply
    (x : MaximalAdicCompletionMixedSource R M)
    (i : GeneratorIndex R) :
    maximalAdicCompletionMixedLeft R M x i =
      LocalizedModule.mk x.1 1 :=
  rfl

omit [IsNoetherianRing R] in
@[simp]
theorem maximalAdicCompletionMixedRight_apply
    (x : MaximalAdicCompletionMixedSource R M)
    (i : GeneratorIndex R) :
    maximalAdicCompletionMixedRight R M x i =
      IsLocalizedModule.map (Submonoid.powers (generator R i))
        (LocalizedModule.mkLinearMap (Submonoid.powers (generator R i)) M)
        (LocalizedModule.mkLinearMap (Submonoid.powers (generator R i))
          (Rhat R ⊗[R] M))
        (TensorProduct.mk R (Rhat R) M 1) (x.2 i) :=
  rfl

/-- The canonical pair consisting of completion and punctured restrictions. -/
private def maximalAdicCompletionMixedPairMap :
    M →ₗ[R] MaximalAdicCompletionMixedSource R M :=
  (TensorProduct.mk R (Rhat R) M 1).prod <|
    LinearMap.pi fun i ↦
      LocalizedModule.mkLinearMap (Submonoid.powers (generator R i)) M

/-- The canonical map into the mixed completion/localization equalizer. -/
def maximalAdicCompletionMixedEqualizerMap :
    M →ₗ[R] LinearMap.eqLocus
      (maximalAdicCompletionMixedLeft R M)
      (maximalAdicCompletionMixedRight R M) :=
  LinearMap.codRestrict _ (maximalAdicCompletionMixedPairMap R M) <| by
    intro m
    ext i
    change LocalizedModule.mk (1 ⊗ₜ[R] m) 1 =
      IsLocalizedModule.map (Submonoid.powers (generator R i))
        (LocalizedModule.mkLinearMap (Submonoid.powers (generator R i)) M)
        (LocalizedModule.mkLinearMap (Submonoid.powers (generator R i))
          (Rhat R ⊗[R] M))
        (TensorProduct.mk R (Rhat R) M 1) (LocalizedModule.mk m 1)
    symm
    exact IsLocalizedModule.map_LocalizedModules
      (Submonoid.powers (generator R i))
      (TensorProduct.mk R (Rhat R) M 1) m 1

omit [IsNoetherianRing R] in
@[simp]
theorem maximalAdicCompletionMixedEqualizerMap_completion
    (m : M) :
    (maximalAdicCompletionMixedEqualizerMap R M m).1.1 = 1 ⊗ₜ[R] m :=
  rfl

omit [IsNoetherianRing R] in
@[simp]
theorem maximalAdicCompletionMixedEqualizerMap_localization
    (m : M) (i : GeneratorIndex R) :
    (maximalAdicCompletionMixedEqualizerMap R M m).1.2 i =
      LocalizedModule.mk m 1 :=
  rfl

/-- The Amitsur difference, reassociated so that torsion reflection applies
to its outer completed factor. -/
private def maximalAdicCompletionAmitsurDifference :
    Rhat R ⊗[R] M →ₗ[R] Rhat R ⊗[R] (Rhat R ⊗[R] M) :=
  (TensorProduct.assoc R (Rhat R) (Rhat R) M).toLinearMap.comp
    ((Algebra.TensorProduct.includeLeftSubRight R (Rhat R)).rTensor M)

omit [IsNoetherianRing R] in
@[simp]
private theorem maximalAdicCompletionAmitsurDifference_tmul
    (s : Rhat R) (m : M) :
    maximalAdicCompletionAmitsurDifference R M (s ⊗ₜ[R] m) =
      s ⊗ₜ[R] (1 ⊗ₜ[R] m) - 1 ⊗ₜ[R] (s ⊗ₜ[R] m) := by
  simp only [maximalAdicCompletionAmitsurDifference, LinearMap.comp_apply,
    LinearMap.rTensor_tmul,
    Algebra.TensorProduct.includeLeftSubRight_apply,
    TensorProduct.sub_tmul, map_sub]
  rfl

/-- Multiplication of the two completed factors. -/
private def maximalAdicCompletionAmitsurCounit :
    Rhat R ⊗[R] (Rhat R ⊗[R] M) →ₗ[R] Rhat R ⊗[R] M :=
  ((Algebra.TensorProduct.lmul' R :
      Rhat R ⊗[R] Rhat R →ₐ[R] Rhat R).toLinearMap.rTensor M).comp
    (TensorProduct.assoc R (Rhat R) (Rhat R) M).symm.toLinearMap

omit [IsNoetherianRing R] in
@[simp]
private theorem maximalAdicCompletionAmitsurCounit_tmul
    (a s : Rhat R) (m : M) :
    maximalAdicCompletionAmitsurCounit R M
        (a ⊗ₜ[R] (s ⊗ₜ[R] m)) =
      (a * s) ⊗ₜ[R] m := by
  simp [maximalAdicCompletionAmitsurCounit]

omit [IsNoetherianRing R] in
@[simp]
private theorem maximalAdicCompletionAmitsurCounit_one_tmul
    (x : Rhat R ⊗[R] M) :
    maximalAdicCompletionAmitsurCounit R M (1 ⊗ₜ[R] x) = x := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy =>
      rw [TensorProduct.tmul_add, map_add, hx, hy]
  | tmul s m => simp

omit [IsNoetherianRing R] in
@[simp]
private theorem maximalAdicCompletionAmitsurCounit_difference
    (x : Rhat R ⊗[R] M) :
    maximalAdicCompletionAmitsurCounit R M
        (maximalAdicCompletionAmitsurDifference R M x) = 0 := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => rw [map_add, map_add, hx, hy, add_zero]
  | tmul s m => simp

/-- A power-torsion Amitsur difference for maximal-adic completion is zero. -/
private theorem maximalAdicCompletionAmitsurDifference_eq_zero_of_pow
    (n : ℕ) (x : Rhat R ⊗[R] M)
    (hx : ∀ r : ((maximalIdeal R) ^ n : Ideal R),
      r.1 • maximalAdicCompletionAmitsurDifference R M x = 0) :
    maximalAdicCompletionAmitsurDifference R M x = 0 := by
  obtain ⟨y, _, hy⟩ :=
    adicCompletion_exists_eq_tmul_of_isTorsionBySet_pow
      (maximalIdeal R) (maximalIdeal R).fg_of_isNoetherianRing n
      (maximalAdicCompletionAmitsurDifference R M x) hx
  have hyzero : y = 0 := by
    have h := congrArg (maximalAdicCompletionAmitsurCounit R M) hy
    simpa using h.symm
  rw [hyzero, TensorProduct.tmul_zero] at hy
  exact hy

omit [IsNoetherianRing R] in
private theorem maximalAdicCompletionAmitsurDifference_localized_eq_zero
    (p : LinearMap.eqLocus
      (maximalAdicCompletionMixedLeft R M)
      (maximalAdicCompletionMixedRight R M))
    (i : GeneratorIndex R) :
    LocalizedModule.mkLinearMap (Submonoid.powers (generator R i))
        (Rhat R ⊗[R] (Rhat R ⊗[R] M))
        (maximalAdicCompletionAmitsurDifference R M p.1.1) = 0 := by
  let P : Submonoid R := Submonoid.powers (generator R i)
  let g : M →ₗ[R] Rhat R ⊗[R] M := TensorProduct.mk R (Rhat R) M 1
  let d : Rhat R ⊗[R] M →ₗ[R] Rhat R ⊗[R] (Rhat R ⊗[R] M) :=
    maximalAdicCompletionAmitsurDifference R M
  let locM := LocalizedModule.mkLinearMap P M
  let locHat := LocalizedModule.mkLinearMap P (Rhat R ⊗[R] M)
  let locDouble :=
    LocalizedModule.mkLinearMap P (Rhat R ⊗[R] (Rhat R ⊗[R] M))
  let mapG := IsLocalizedModule.map P locM locHat g
  let mapD := IsLocalizedModule.map P locHat locDouble d
  have hp : locHat p.1.1 = mapG (p.1.2 i) := by
    have hp' := congrFun p.2 i
    exact hp'
  have hdg : d.comp g = 0 := by
    ext m
    simp [d, g]
  calc
    locDouble (d p.1.1) = mapD (locHat p.1.1) := by
      symm
      exact IsLocalizedModule.map_apply P locHat locDouble d p.1.1
    _ = mapD (mapG (p.1.2 i)) := congrArg mapD hp
    _ = (mapD.comp mapG) (p.1.2 i) := rfl
    _ = (IsLocalizedModule.map P locM locDouble (d.comp g))
          (p.1.2 i) := by
      exact congrArg (fun h ↦ h (p.1.2 i))
        (IsLocalizedModule.map_comp' P locM locHat locDouble g d).symm
    _ = 0 := by rw [hdg]; simp

private theorem maximalAdicCompletionAmitsurDifference_eq_zero
    (p : LinearMap.eqLocus
      (maximalAdicCompletionMixedLeft R M)
      (maximalAdicCompletionMixedRight R M)) :
    maximalAdicCompletionAmitsurDifference R M p.1.1 = 0 := by
  have hspan : Ideal.span (Set.range (generator R)) = maximalIdeal R := by
    have hrange :
        Set.range (generator R) = (maximalIdeal R).generators := by
      ext x
      constructor
      · rintro ⟨i, rfl⟩
        exact i.2
      · intro hx
        exact ⟨⟨x, hx⟩, rfl⟩
    rw [hrange]
    exact (maximalIdeal R).span_generators
  obtain ⟨n, hn⟩ :=
    exists_pow_annihilates_of_localizedModule_mk_eq_zero
      (maximalIdeal R).fg_of_isNoetherianRing (generator R) hspan
      (maximalAdicCompletionAmitsurDifference R M p.1.1)
      (maximalAdicCompletionAmitsurDifference_localized_eq_zero R M p)
  exact maximalAdicCompletionAmitsurDifference_eq_zero_of_pow R M n p.1.1 hn

/-- A module over a Noetherian local ring is the mixed equalizer of its
maximal-adic completion and its restrictions to the chosen principal cover
of the punctured spectrum. -/
noncomputable def maximalAdicCompletionMixedEqualizerEquiv :
    M ≃ₗ[R] LinearMap.eqLocus
      (maximalAdicCompletionMixedLeft R M)
      (maximalAdicCompletionMixedRight R M) :=
  LinearEquiv.ofBijective (maximalAdicCompletionMixedEqualizerMap R M) <| by
    let : Module.FaithfullyFlat R (Rhat R) :=
      maximalAdicCompletion_faithfullyFlat R
    constructor
    · intro m m' hmm'
      apply Module.FaithfullyFlat.tensorProduct_mk_injective
        (A := R) (B := Rhat R) M
      exact congrArg (fun q ↦ q.1.1) hmm'
    · intro p
      have hd := maximalAdicCompletionAmitsurDifference_eq_zero R M p
      have hsub :
          ((Algebra.TensorProduct.includeLeftSubRight R (Rhat R)).rTensor M)
              p.1.1 = 0 := by
        apply (TensorProduct.assoc R (Rhat R) (Rhat R) M).injective
        simpa [maximalAdicCompletionAmitsurDifference] using hd
      have heq :
          tensorProductDescentLeft (R := R) (S := Rhat R) (M := M) p.1.1 =
            tensorProductDescentRight (R := R) (S := Rhat R) (M := M) p.1.1 := by
        apply sub_eq_zero.mp
        simpa [Algebra.TensorProduct.includeLeftSubRight,
          LinearMap.rTensor_sub, tensorProductDescentLeft,
          tensorProductDescentRight] using hsub
      let q : LinearMap.eqLocus
          (tensorProductDescentLeft (R := R) (S := Rhat R) (M := M))
          (tensorProductDescentRight (R := R) (S := Rhat R) (M := M)) :=
        ⟨p.1.1, heq⟩
      let m : M := (maximalAdicCompletionModuleEqualizerEquiv R M).symm q
      have hmhat : 1 ⊗ₜ[R] m = p.1.1 := by
        have hm := (maximalAdicCompletionModuleEqualizerEquiv R M).apply_symm_apply q
        exact congrArg Subtype.val hm
      refine ⟨m, Subtype.ext ?_⟩
      apply Prod.ext
      · exact hmhat
      · funext i
        let P : Submonoid R := Submonoid.powers (generator R i)
        let locM := LocalizedModule.mkLinearMap P M
        let locHat := LocalizedModule.mkLinearMap P (Rhat R ⊗[R] M)
        let g : M →ₗ[R] Rhat R ⊗[R] M := TensorProduct.mk R (Rhat R) M 1
        let mapG := IsLocalizedModule.map P locM locHat g
        apply IsLocalizedModule.map_injective P locM locHat g
          (Module.FaithfullyFlat.tensorProduct_mk_injective
            (A := R) (B := Rhat R) M)
        calc
          mapG (locM m) = locHat (g m) :=
            IsLocalizedModule.map_apply P locM locHat g m
          _ = locHat p.1.1 := congrArg locHat hmhat
          _ = mapG (p.1.2 i) := by
            exact congrFun p.2 i

/-- The mixed equalizer equivalence is the canonical completion/localization
pair, in a form convenient for downstream Hom and algebra descent. -/
@[simp]
theorem maximalAdicCompletionMixedEqualizerEquiv_apply (m : M) :
    (maximalAdicCompletionMixedEqualizerEquiv R M m :
      MaximalAdicCompletionMixedSource R M) =
      (1 ⊗ₜ[R] m, fun _ ↦ LocalizedModule.mk m 1) :=
  rfl

end MaximalAdic

end EtaleFundamentalGroups

end
