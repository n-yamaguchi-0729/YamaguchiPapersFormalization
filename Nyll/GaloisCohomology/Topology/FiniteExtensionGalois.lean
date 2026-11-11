/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.Topology.Algebra.OpenSubgroup
public import Nyll.GaloisCohomology.Kummer.Concrete.GaloisClosureConjugation
public import Nyll.ValuedFieldTheory.Valuation.Completion.SeparableClosureAutTopology
public import Mathlib.FieldTheory.IntermediateField.Algebraic
public import Mathlib.FieldTheory.Galois.Infinite
public import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Open Galois subgroups from finite field extensions

Scalar restriction is continuous and identifies the upper Galois group
with the open subgroup fixing the embedded finite extension field.
-/

@[expose] public section

namespace GaloisCohomology

open scoped Topology

universe u v w

variable (K : Type u) (E : Type v) (Ω : Type w)
  [Field K] [Field E] [Field Ω] [Algebra K E] [Algebra E Ω] [Algebra K Ω]
  [IsScalarTower K E Ω]

/-- Restriction of scalars is continuous for an algebraic upper extension. -/
theorem continuous_galoisRestrictScalars [Algebra.IsAlgebraic E Ω] :
    Continuous (AlgEquiv.restrictScalarsHom K : Gal(Ω/E) →* Gal(Ω/K)) := by
  classical
  apply continuous_of_tendsto_nhds_one
  rw [Filter.tendsto_def]
  intro U hU
  obtain ⟨F, hF, hFU⟩ := (krullTopology_mem_nhds_one_iff K Ω U).mp hU
  let b : Module.Basis (Fin (Module.finrank K F)) K F := Module.finBasis K F
  have hopen : IsOpen (⋂ j, (MulAction.stabilizer Gal(Ω/E) (b j : Ω) :
      Set Gal(Ω/E))) := isOpen_iInter_of_finite fun j =>
    stabilizer_isOpen_of_isIntegral (K := E) (b j : Ω)
  have hone : (1 : Gal(Ω/E)) ∈ ⋂ j,
      (MulAction.stabilizer Gal(Ω/E) (b j : Ω) : Set Gal(Ω/E)) :=
    Set.mem_iInter.mpr fun _ => Subgroup.one_mem _
  apply Filter.mem_of_superset (hopen.mem_nhds hone)
  intro σ hσ
  apply hFU
  apply (IntermediateField.mem_fixingSubgroup_iff F (σ.restrictScalars K)).mpr
  have hlin : ((σ.restrictScalars K).toAlgHom.comp F.val).toLinearMap =
      F.val.toLinearMap := b.ext fun j =>
    MulAction.mem_stabilizer_iff.mp (Set.mem_iInter.mp hσ j)
  intro x hx
  exact congrArg (fun f : F →ₗ[K] Ω => f ⟨x, hx⟩) hlin

/-- The image of scalar restriction fixes exactly the embedded lower field. -/
theorem galoisRestrictScalars_range :
    (AlgEquiv.restrictScalarsHom K : Gal(Ω/E) →* Gal(Ω/K)).range =
      (IsScalarTower.toAlgHom K E Ω).fieldRange.fixingSubgroup := by
  ext σ
  constructor
  · rintro ⟨τ, rfl⟩
    apply (IntermediateField.mem_fixingSubgroup_iff _ _).mpr
    rintro x ⟨y, rfl⟩
    exact τ.commutes y
  · intro hσ
    let τ : Gal(Ω/E) :=
      { σ.toRingEquiv with
        commutes' := fun y =>
          (IntermediateField.mem_fixingSubgroup_iff _ _).mp hσ _ ⟨y, rfl⟩ }
    exact ⟨τ, AlgEquiv.ext fun _ => rfl⟩

/-- Equal scalar-restriction images determine a unique isomorphism of the
embedded fields. The isomorphism preserves their actual embeddings into the
common Galois extension, not just the degrees of the fields. -/
theorem exists_unique_algEquiv_of_galoisRestrictScalars_range_eq
    (E' : Type*) [Field E'] [Algebra K E'] [Algebra E' Ω]
    [IsScalarTower K E' Ω] [IsGalois K Ω]
    (h : (AlgEquiv.restrictScalarsHom K : Gal(Ω/E) →* Gal(Ω/K)).range =
      (AlgEquiv.restrictScalarsHom K : Gal(Ω/E') →* Gal(Ω/K)).range) :
    ∃! e : E ≃ₐ[K] E', ∀ x, algebraMap E' Ω (e x) = algebraMap E Ω x := by
  let f : E →ₐ[K] Ω := IsScalarTower.toAlgHom K E Ω
  let f' : E' →ₐ[K] Ω := IsScalarTower.toAlgHom K E' Ω
  have hfix : f.fieldRange.fixingSubgroup = f'.fieldRange.fixingSubgroup := by
    simpa only [galoisRestrictScalars_range] using h
  have hrange : f.fieldRange = f'.fieldRange := by
    rw [← InfiniteGalois.fixedField_fixingSubgroup f.fieldRange,
      ← InfiniteGalois.fixedField_fixingSubgroup f'.fieldRange, hfix]
  let e : E ≃ₐ[K] E' :=
    (f.equivFieldRange.trans (IntermediateField.equivOfEq hrange)).trans
      f'.equivFieldRange.symm
  have he (x : E) : algebraMap E' Ω (e x) = algebraMap E Ω x := by
    have hval := congrArg (fun z : f'.fieldRange => (z : Ω))
      (f'.equivFieldRange.apply_symm_apply
        (IntermediateField.equivOfEq hrange (f.equivFieldRange x)))
    simpa only [e, AlgEquiv.trans_apply, AlgHom.equivFieldRange_apply_coe,
      IntermediateField.equivOfEq_apply, f, f', IsScalarTower.toAlgHom_apply] using hval
  refine ⟨e, he, ?_⟩
  intro e' he'
  apply AlgEquiv.ext
  intro x
  exact (algebraMap E' Ω).injective ((he' x).trans (he x).symm)

variable [FiniteDimensional K E]

/-- The finite extension gives an actual open subgroup of the lower Galois group. -/
def finiteExtensionGaloisOpenSubgroup : OpenSubgroup Gal(Ω/K) where
  toSubgroup := (AlgEquiv.restrictScalarsHom K : Gal(Ω/E) →* Gal(Ω/K)).range
  isOpen' := by
    rw [galoisRestrictScalars_range K E Ω]
    have : FiniteDimensional K (IsScalarTower.toAlgHom K E Ω).fieldRange :=
      Module.Finite.equiv (IsScalarTower.toAlgHom K E Ω).equivFieldRange.toLinearEquiv
    exact IntermediateField.fixingSubgroup_isOpen _

variable [IsAlgClosure E Ω]

/-- Scalar restriction identifies the upper absolute Galois group with this
open subgroup. This includes inseparable finite extensions of the lower field. -/
noncomputable def finiteExtensionGaloisOpenSubgroupEquiv :
    Gal(Ω/E) ≃ₜ* (finiteExtensionGaloisOpenSubgroup K E Ω : Subgroup Gal(Ω/K)) := by
  have : Algebra.IsAlgebraic K Ω := Algebra.IsAlgebraic.trans K E Ω
  have : CompactSpace Gal(Ω/E) :=
    (KummerTheory.absoluteGaloisClosureEquiv E Ω).symm.toHomeomorph.compactSpace
  let e : Gal(Ω/E) ≃* (finiteExtensionGaloisOpenSubgroup K E Ω : Subgroup Gal(Ω/K)) :=
    MonoidHom.ofInjective (f := AlgEquiv.restrictScalarsHom K)
      (AlgEquiv.restrictScalars_injective K)
  have he : Continuous e := (continuous_galoisRestrictScalars K E Ω).subtype_mk _
  exact { e with
    continuous_toFun := he
    continuous_invFun := he.continuous_symm_of_equiv_compact_to_t2 }

end GaloisCohomology
