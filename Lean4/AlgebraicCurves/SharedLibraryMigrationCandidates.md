# Shared-library migration candidates from AC/JV

Date: 2026-10-04. Status: first, bounded inventory for cleanup after the current AC/JV repair and validation work. No declarations, imports, instances, or aggregates were changed for this inventory, and no additional build was run. “Generic” below describes the inspected statement and hypotheses; it does not certify the proof or mean that moving its current file is safe.

This complements [LibraryScope.md](LibraryScope.md), rather than replacing its scope and Jacobian completion contract. The existing README centralizes AC/JV documentation here; the recommended repository location for this memo is `Lean4/AlgebraicCurves/SharedLibraryMigrationCandidates.md`.

## Placement rules

- Preserve existing mathematical namespaces where practical. A file move need not rename a public declaration.
- `SchemeTheory` already owns affine geometry, descent, morphisms, category theory, and supporting ring theory. Proposed new leaves below are explicitly marked **new**; no existing general sheaf/module subtree was found there.
- Extract prerequisites before consumers. A shared leaf must not acquire an AC/JV import merely to retain the implementation unchanged. In particular, move the small invertibility API out of the Picard functor before its generic consequences.
- Compare against the pinned Mathlib and existing shared APIs before adding another implementation. Preserve actual comparison maps and hypotheses, not merely existentially isomorphic objects.

## High-confidence candidates

### 1. Basic line-bundle API currently inside the Picard functor

**Source:** `Lean4/AlgebraicCurves/Geometry/Picard/Functor.lean`, lines 30–60.

**Declarations:** `AlgebraicGeometry.Scheme.Modules.IsInvertible`, `AlgebraicGeometry.Scheme.Modules.pullbackUnitIso`, `AlgebraicGeometry.Scheme.Modules.isInvertible_unit`, `AlgebraicGeometry.Scheme.Modules.IsInvertible.pullback`.

**Why generic:** `IsInvertible M` is local triviality against the unit sheaf on an arbitrary scheme. Pullback preservation takes any scheme morphism; it assumes no curve, properness, dimension, base point, or Picard representability.

**Destination:** existing namespace `AlgebraicGeometry.Scheme.Modules`; **new** `SchemeTheory/Sheaves/Invertible.lean` and, if necessary, a separate pullback-unit leaf.

**Caution:** split only the generic prefix. Keep `RelPicard` functor construction separate. The file currently imports `Geometry/Schemes/SchemeHomOver.lean`, which is needed by its later relative-Picard material; the extracted prefix should use direct Mathlib module imports instead. Review the adjacent `Scheme.Hom.opensMapFinal` instance for existing Mathlib ownership rather than copying another global instance.

### 2. Restriction of module sheaves to an open subscheme

**Source:** `Lean4/AlgebraicCurves/Geometry/Sheaves/ModulesRestrictOpen.lean`.

**Declarations:** `AlgebraicGeometry.Scheme.Modules.restrictOpen`, `restrictOpenIsoRestrictFunctor`, `restrictOpenIsoPullback`; the file also contains the more general `PresheafOfModules.pushforwardNatTrans` and `pushforwardPushforwardAdj`.

**Why generic:** the scheme part takes only `X : Scheme` and `U : X.Opens`. The presheaf part is over arbitrary categories and ring-valued presheaves.

**Destination:** existing namespaces above; **new** `SchemeTheory/Sheaves/RestrictOpen.lean`. Factor the arbitrary-category machinery into a small leaf under the existing `SchemeTheory/CategoryTheory/` directory, or an eventual general sheaf library.

**Caution:** this file currently imports only `Mathlib.AlgebraicGeometry.Modules.Sheaf`, so it is a relatively clean extraction candidate. Preserve the adjunction and comparison-isomorphism API, rather than relying on new definitional equalities after moving it.

### 3. Local freeness and its preservation by pullback

**Sources:** `Lean4/AlgebraicCurves/Geometry/Sheaves/ModulesLocallyFreeOfRank.lean`; `Lean4/AlgebraicCurves/Geometry/Sheaves/Scheme_Modules_IsLocallyFreeOfRank_pullback.lean`.

**Declarations:** `AlgebraicGeometry.Scheme.Modules.IsLocallyFreeOfRank`; `AlgebraicGeometry.Scheme.Modules.IsLocallyFreeOfRank.pullback`.

**Why generic:** rank is an arbitrary natural number, the module is on an arbitrary scheme, and the pullback morphism is unrestricted.

**Destination:** existing namespace; **new** `SchemeTheory/Sheaves/LocallyFree.lean`.

**Caution:** move the definition with its theorem. The proof already uses Mathlib's sheaf pullback-free API; compare that API before choosing whether this extra predicate is the shared public representation. Do not export the implementation's `pullback'` merely because it exists.

### 4. Unique gluing of module-sheaf morphisms

**Source:** `Lean4/AlgebraicCurves/Geometry/Sheaves/Scheme_Modules_existsUnique_hom_app_eq_of_iSup_eq_top.lean`.

**Declaration:** `AlgebraicGeometry.Scheme.Modules.existsUnique_hom_app_eq_of_iSup_eq_top`.

**Why generic:** for arbitrary `M N : X.Modules` and opens `U i` with supremum top, compatible linear maps on opens contained in the cover glue to a unique `M ⟶ N`. The hypotheses express cover and restriction compatibility only.

**Destination:** existing namespace; **new** `SchemeTheory/Sheaves/Gluing.lean`.

**Caution:** its imports are already Mathlib-only. Keep the uniqueness and component formula, which are the useful reusable interface. A wider ringed-space generalization is optional future work, not required for extraction.

### 5. Invertible sheaves: tensor closure and faithfully flat descent

**Sources:** `Lean4/AlgebraicCurves/Geometry/Sheaves/Scheme_Modules_IsInvertible_tensor.lean`; its `_tensor_monoidalV2.lean` counterpart; `Lean4/AlgebraicCurves/Geometry/Sheaves/Scheme_Modules_IsInvertible_exists_iso_toDescentData_of_isAffineHom_of_flat_of_surjective.lean`.

**Declarations:** `AlgebraicGeometry.Scheme.Modules.IsInvertible.tensor`, `tensor_monoidalV2`, and `exists_iso_toDescentData_of_isAffineHom_of_flat_of_surjective` in that same `IsInvertible` namespace.

**Why generic:** tensor closure assumes two invertible sheaves on any scheme. Descent assumes an affine, flat, surjective morphism `q : Y' ⟶ Y` and invertible objects in its module descent datum; it returns an invertible sheaf on `Y` realizing that datum. There is no curve hypothesis.

**Destination:** **new** sheaf tensor leaf below `SchemeTheory/Sheaves/`, and a module-sheaf descent leaf below the existing `SchemeTheory/Descent/`; keep the mathematical namespace.

**Caution:** depends on item 1 plus shared monoidal/internal-hom/pullback machinery. The V2 pullback file currently imports the older pullback file: these are not independent implementations to move wholesale into separate public APIs. The descent theorem also uses its affine case, open-cover stack theorem, full-faithfulness theorem, and a generic pseudofunctor descent assembly lemma. Extract their actual lower-level dependency closure first.

### 6. Faithfully flat descent of invertible modules

**Source:** `Lean4/AlgebraicCurves/Foundations/Algebra/Module_Invertible_of_invertible_tensorProduct_of_faithfullyFlat.lean`, public theorem at line 203.

**Declaration:** `Module.Invertible.of_invertible_tensorProduct_of_faithfullyFlat`.

**Why generic:** for commutative rings `R → S` with `Module.FaithfullyFlat R S`, invertibility of `S ⊗[R] M` implies invertibility of the arbitrary `R`-module `M`. No geometric hypotheses occur.

**Destination:** existing `Module.Invertible` namespace; **new** `SchemeTheory/RingTheory/Descent/InvertibleModule.lean`, next to the existing `FaithfullyFlatModuleEqualizer.lean` and `FaithfullyFlatModuleHomDescent.lean`.

**Caution:** current imports are Mathlib-only. Compare the proof's `S17FF` dual-base-change helpers with Mathlib and the existing descent leaves; do not promote that implementation namespace as the public API. The existing shared module-descent leaves still use an `EtaleFundamentalGroups` namespace, so directory ownership and namespace cleanup are separate decisions.

### 7. Flat kernels and tensor injectivity

**Sources:** `Lean4/AlgebraicCurves/Foundations/Algebra/Module_Flat_ker_of_surjective_of_flat.lean`; `Lean4/AlgebraicCurves/Foundations/Algebra/Module_Flat_lTensor_injective_of_exact_of_surjective_of_flat.lean`.

**Declarations:** `Module.Flat.ker_of_surjective_of_flat`; `Module.Flat.lTensor_injective_of_exact_of_surjective_of_flat`.

**Why generic:** a surjection between flat modules has flat kernel. The supporting theorem says tensoring an injective map in a short exact sequence remains injective when the quotient is flat; the tensor factor is arbitrary.

**Destination:** existing `Module.Flat` namespace; **new** `SchemeTheory/RingTheory/FlatModule.lean`, or a future general commutative-algebra library. These are module results, not additions to the scheme-morphism `SchemeTheory/Morphisms/Flat.lean`.

**Caution:** move the supporting theorem first or in the same small leaf. It has Mathlib-only imports. Preserve the exactness, surjectivity, and flatness assumptions and check for an equivalent pinned-Mathlib theorem before retaining a duplicate proof.

### 8. Normality facts, including an existing shared-to-AC reverse edge

**Sources:** `Lean4/AlgebraicCurves/Foundations/CommutativeAlgebra/IsIntegrallyClosed_of_faithfullyFlat.lean`; `Lean4/AlgebraicCurves/Foundations/CommutativeAlgebra/Algebra_Etale_isDomain_and_isIntegrallyClosed_of_isLocalization_atPrime.lean`.

**Declarations:** `IsIntegrallyClosed.of_faithfullyFlat`; `Algebra.Etale.isDomain_and_isIntegrallyClosed_of_isLocalization_atPrime`.

**Why generic:** the first descends integral closedness along a faithfully flat map of domains. The second takes an integrally closed domain `P`, an étale `P`-algebra `A`, a prime of `A`, and its localization, and proves that localization is a domain and integrally closed.

**Destination:** existing namespaces; the existing `SchemeTheory/RingTheory/Descent/EtaleLocalNormality.lean` is the natural owner/consumer for the étale result; a sibling **new** faithfully-flat normality leaf fits the other theorem.

**Caution:** `EtaleLocalNormality.lean` already directly imports the AC étale theorem. Extracting that Mathlib-only prerequisite would remove a verified reverse library dependency. Its shared theorem `SchemeTheory.isDomain_and_isIntegrallyClosed_atPrime_of_etale` is a localization-at-the-base variant, so compare and consolidate without silently dropping either interface.

### 9. A categorical pullback lemma

**Source:** `Lean4/AlgebraicCurves/Foundations/CategoryTheory/CategoryTheory_IsPullback_fst_pullbackMap_of_comp_eq.lean`.

**Declaration:** `CategoryTheory.IsPullback.fst_pullbackMap_of_comp_eq`.

**Why generic:** it assumes an arbitrary category, composable morphisms with a commutative triangle, and the two required pullbacks. There are no scheme or ring hypotheses.

**Destination:** existing `CategoryTheory.IsPullback` namespace; **new** `SchemeTheory/CategoryTheory/Pullback.lean` as the existing local shared category-theory home, or an eventual general category-theory library.

**Caution:** imports only the corresponding Mathlib pullback module. Search that pinned API for an equivalent pasting/map lemma before extracting a separate theorem. Keep this below every geometric consumer.

### 10. Affine base-change sections currently in JV

**Source:** `Lean4/JacobianVarieties/Picard/exists_algEquiv_sections_stage_baseChange_of_isAffineOpen.lean`.

**Declarations:** public `AlgebraicGeometry.RelPicard.exists_algEquiv_sections_stage_baseChange_of_isAffineOpen` (line 428); local implementation theorem `AlgebraicGeometry.Scheme.TwoAffineOpenCover.exists_algEquiv_sections_baseChange` inside that file's proof namespace (line 213).

**Why generic:** the core theorem takes any scheme over `Spec R`, any affine open, and any `R`-algebra `A`, and identifies sections after base change with `A ⊗[R] Γ(X,U)`, including the formula on `1 ⊗ s`. The public theorem adds a scalar tower and transport to a named preimage open. Neither assumes a curve or a two-open covering.

**Destination:** existing `SchemeTheory/Affine/FlatBaseChangeSections.lean` as the comparison point; preferably a **new** neighboring `AffineBaseChangeSections.lean` if retaining its no-flatness affine-open interface. Use `AlgebraicGeometry`/scheme affine-open namespaces for the core, with the RelPicard stage wrapper left above it if needed.

**Caution:** the existing `affinePullbackSectionsTensorEquiv` covers qcqs morphisms with a flat base-change morphism. The JV affine-open theorem does not require flatness. They are related APIs, not interchangeable statements. Factor `algebraOfHom`, `specMap`, and the affine transport construction away from `TwoAffineOpenCover`/`StageHom`/Picard imports before lowering it.

### 11. Stalk ideal membership under local base change

**Source:** `Lean4/AlgebraicCurves/Geometry/Schemes/mem_map_maximalIdeal_of_stalkMap_mem_map_maximalIdeal_of_iso_pullback.lean`.

**Declaration:** `AlgebraicGeometry.mem_map_maximalIdeal_of_stalkMap_mem_map_maximalIdeal_of_iso_pullback`; private helper `germ_stalkMap_stalkClosedPointTo` in the same file.

**Why generic:** assumptions are a local ring homomorphism with the specified surjectivity to the residue field, arbitrary schemes, a pullback isomorphism over the base, and a point over the closed point. The conclusion reflects membership in the ideal generated by the base maximal ideal through the stalk map.

**Destination:** existing affine/stalk namespace `AlgebraicGeometry`; **new** `SchemeTheory/Affine/StalkBaseChange.lean`, beside `StalkLocalization.lean` and `ChartStalkLocalization.lean`.

**Caution:** imports are Mathlib-only. Retain the residue-field surjectivity and over-base compatibility assumptions. The germ-composition helper is general but private; expose it only if independent consumers justify a stable API.

## Generic, but factor before deciding placement

- **Effective descent actions.** `AlgebraicGeometry.DescentAction.effective_of_isPullback_of_flat_surjective` in `Lean4/AlgebraicCurves/Geometry/Descent/DescentAction_effective_of_isPullback_of_flat_surjective.lean` assumes arbitrary schemes, an action, a flat/surjective/quasi-compact quotient map, and a kernel-pair pullback square. Candidate owner: existing `SchemeTheory/Descent/`, near `FpqcLocalCoequalizer.lean`. Move the generic `DescentAction.lean` definitions with it and compare the quotient interface; neither the kernel-pair square nor its construction can be replaced by an unproved assumption package.
- **Projective/Segre chart machinery.** `AlgebraicGeometry.ChowDatumProj.nonempty_of` in `Lean4/AlgebraicCurves/Geometry/Schemes/ChowDatumProj_nonempty_of.lean` works over any commutative ring and scheme, converting `ChowDatum` to `ChowDatumProj`. Its private `AlgebraicGeometry.ProjSpace.Segre.segreChart_preimage_ratio` (within the file's proof namespace) computes a coordinate basic-open preimage as an intersection. Candidate: **new** `SchemeTheory/Projective/Segre.lean` and separate Chow infrastructure. Its AC `Geometry/Projective/ProjSpace.lean` prerequisite must be factored too; moving the consumer alone would create a shared-to-AC edge.
- **Dual-number coefficient arithmetic.** In `Lean4/JacobianVarieties/Picard/exists_crossSections_of_isFrameOn_of_map_eq_oneAddEpsMul_smul.lean`, private `CoverCross.coefficient_transition` (inside the file's proof namespace) is a pure commutative-ring identity: `a₀r₀ = a₁r₁ = 1`, `a₀ = a₁`, and `b₀ = a₁f + b₁` imply `b₀r₀ = b₁r₁ + f`. `coefficient_transition_restrict` transports the identity through affine dual-number section restrictions. Candidate: a small **new** ring-theory helper only if reused, with sheaf transport below Picard. Do not move the whole cross-cover deformation proof or expose private helpers merely for their names.
- **The theorem of the cube.** `AlgebraicGeometry.Scheme.Modules.nonempty_iso_tensorUnit_of_pullback_three_slices` in `Lean4/JacobianVarieties/Picard/Scheme_Modules_nonempty_iso_tensorUnit_of_pullback_three_slices.lean` is stated for proper integral `X,Y` and separated finite-type integral `Z` over an algebraically closed field, with rational base points and a line bundle trivial on three slices. Its statement is higher-dimensional, but its current proof imports the curve case and curve-testing/Picard results. A future general Picard/line-bundle library is plausible; it is **not** an immediately low-level SchemeTheory move.

## Keep the genuinely curve/Jacobian layer

For example, `AlgebraicGeometry.RelPicard.subsingleton_H1_and_finrank_H0_fibre_poincare_tensor_sectionTwist` in `Lean4/JacobianVarieties/Picard/Subsingleton_H1_and_finrank_H0_fibre_poincare_tensor_sectionTwist.lean` explicitly assumes `SmoothOfRelativeDimension 1`, a represented relative Picard object, genus determined through a curve-model Riemann–Roch formula, and `2 * g ≤ r + 1`. Its Poincaré-twist cohomology and rank formula belong in the curve/Jacobian layer. Likewise, retain degree-zero divisor classes, curve genus, Abel–Jacobi, and their representability-specific consequences there; generic wording in a filename is not sufficient reason to move them.

## Cleanup order and acceptance checks

1. Finish the current repair/validation milestone before any relocation.
2. Start with Mathlib-only leaves and the actual reverse edge in item 8. Then extract generic definitions (items 1–3), followed by gluing, tensor, and descent dependency closures.
3. Reconcile equivalent APIs and V2/legacy instance ownership. Preserve source copyright, author, license, pinned upstream references, and relevant attribution when splitting or moving files.
4. Preserve public names initially where feasible; update direct leaf imports and canonical `All.lean` reachability in the same change. Do not create aliases solely to make the inventory look complete.
5. Compute the direct-import reverse closure for the actual changed modules; check for cycles and residual shared-to-AC/JV imports. Validate the moved leaf, direct consumers, then the smallest affected aggregate. The relocation is not complete on static inspection alone.

This inventory deliberately does not audit every AC/JV theorem or prescribe a wholesale library reorganization.

## Additional candidates from the pinned Anthropic FLT archive

Date: 2026-10-04. This addendum follows a full download of [Anthropic FLT revision `aa2d8b34692b16c70f699536de0d8e75b9a3e9ef`](https://github.com/anthropics/fermats-last-theorem/tree/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef), the revision already cited by AC/JV. All 60,478 archive Lean files were searched; the 29,511 theorem files matched the independently retrieved Git tree's blob hashes. This was source inspection only: no upstream scripts, compiler, or verification tools were run, and no declarations were migrated.

The following exact declarations were not found in the current `Lean4` sources or the inspected Mathlib ring-theory/algebraic-geometry directories. This does not exclude equivalent APIs under different names. Dependency counts below are static upstream import-closure sizes, excluding Lean/Mathlib and including statement, proof, and helper modules; they are not counts of new files that must be imported.

### A. Algebra and graded-algebra descent

**Declarations:** `Algebra.bijective_tensorProduct_equalizer_of_faithfullyFlat_of_descentDatum` and `Algebra.bijective_tensorProduct_equalizer_of_faithfullyFlat_of_cocycle`.

**Sources:** [ordinary descent statement](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Algebra_bijective_tensorProduct_equalizer_of_faithfullyFlat_of_descentDatum.lean), [graded statement](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Algebra_bijective_tensorProduct_equalizer_of_faithfullyFlat_of_cocycle.lean); their concrete proofs are the corresponding `P2M/Sol/S_*.lean` files.

**Conditions and result:** commutative rings, a faithfully flat map `S → S′`, an `S′`-algebra, a compatible tensor-product descent isomorphism, and its cocycle identity. The proof constructs the equalizer algebra and proves its scalar-extension map bijective. The graded version additionally assumes degree preservation and proves closure under homogeneous components.

**Placement and priority:** first compare with existing module equalizer/descent APIs, then extract to the shared ring-theory descent layer. Each upstream closure has **5 modules**. This is a useful lower-level prerequisite for item B.

### B. Descent of schemes with a compatible very ample line bundle

**Declaration:** `AlgebraicGeometry.exists_descent_of_faithfullyFlat_of_cocycle`.

**Source:** [statement and complete hypotheses](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_exists_descent_of_faithfullyFlat_of_cocycle.lean).

**Conditions and result:** a faithfully flat base extension, an invertible sheaf giving a closed immersion into projective space (`ClosedImmersionBySections`), specified double/triple pullback diagrams, and a compatible sheaf isomorphism satisfying the cocycle identity. The proof descends the graded section ring, constructs the scheme as `Proj`, and descends the line bundle. Keep these hypotheses: this is not unrestricted effective descent for arbitrary schemes.

**Placement:** `SchemeTheory/Descent/`, with generic section-ring and `Proj` prerequisites below it. The upstream closure has **256 modules**; factor and deduplicate it rather than copying that closure wholesale.

### C. Descent of projective presentations

**Declaration:** `AlgebraicGeometry.Scheme.Modules.exists_projPresentation_isPullback_toProj_of_faithfullyFlat`.

**Source:** [statement](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_isPullback_toProj_of_faithfullyFlat.lean).

**Conditions and result:** a quasi-compact separated scheme over an affine base, an invertible sheaf, a faithfully flat base-change square, and a projective presentation of its pullback. It constructs a presentation downstairs, a compatible presentation upstairs, and the pullback square, with formulas expressing the original sections in the new sections.

**Placement:** generic scheme-module/projective infrastructure. The upstream closure has **71 modules**. A projective presentation alone is not an assertion that its map is a closed immersion; preserve that distinction from item B.

### D. Finite presentation through a faithfully flat finite-presentation cover

**Declaration:** `Algebra.FinitePresentation.of_faithfullyFlat_of_finitePresentation`.

**Source:** [statement](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Algebra_FinitePresentation_of_faithfullyFlat_of_finitePresentation.lean).

**Conditions and result:** a compatible tower of commutative algebras `R → A → B`, faithfully flat `A → B`, and finite presentation of both `B/A` and `B/R`; conclude finite presentation of `A/R`.

**Placement:** shared ring-theory descent. The upstream closure has **15 modules**. Compare with current Mathlib's `Algebra.FinitePresentation.of_finitePresentation_tensorProduct_of_faithfullyFlat` before retaining a separate proof.

### Already imported components and the Jacobian boundary

The following are already present and should be considered for lowering, not reimporting:

- `Module.FaithfullyFlat.exists_submodule_isBaseChange_of_cocycle` in `AlgebraicCurves/Foundations/Algebra/`
- `Scheme.exists_quotient_of_finiteLocallyFree_equivalenceRelation` and `exists_representableBy_of_representableBy_restrict_finiteEtale` in `AlgebraicCurves/Geometry/Schemes/`
- `DescentAction.effective_of_finiteEtale` in `AlgebraicCurves/Geometry/Descent/`
- `RelPicard.LFP.exists_fg_nonempty_iso_pullbackAlong` in `JacobianVarieties/Picard/`

The inspected upstream Jacobian/Picard existence route is rigidified by a section `ε`. In particular, `exists_relJacobian_of_smoothOfRelativeDimension_one` assumes a DVR base, and its `Pic0` point dictionary is over algebraically closed fields. The arbitrary-field chart theorem `RelPicard.exists_finite_etale_hasChartSections_of_field` is available, but still assumes `ε` and sufficiently large `FiniteMapData`; those chart/descent components are already in JV. No ready-to-use arbitrary-field, base-point-free Jacobian existence API was identified. The unrigidified Picard-sheaf/descent work needed for that goal remains separate; these extraction candidates do not close it by themselves.

### Verification and provenance limits

The whole-source token scan found `sorry` only at the three intentional comparison holes in `verification/comparator/Challenge.lean`; that file is outside the inspected candidate import closures. No `axiom`, `sorryAx`, `native_decide`, `unsafe`, `extern`, `implemented_by`, `admit`, `partial def`, or `#eval` tokens were found. Concrete proof bodies were inspected, but this is not a fresh kernel check or proof of compatibility with the current project.

Upstream pins Lean **4.33.1** and Mathlib **`db584cd6d46c92f209a44c0f1c829460d327499d`**; the inspected project pins Lean **4.35.0-rc2** and Mathlib **`065356127b1dc0016f66b7283ce0ce2c4055aa55`**. Reconcile APIs and instances during any later migration. Preserve the Apache-2.0 license, fixed-revision source links, upstream `NOTICE`/`ATTRIBUTION.md`, and any further FLT/Mathlib author and copyright notices. The cleanup order and acceptance checks above still apply.

## AC/JV ownership correction: concrete relocation batches

Date: 2026-10-05. The cleanup now includes actual placement between AC and JV, as well as extraction into shared libraries. This is an actionable, bounded move plan, not a claim that the moves have already happened. A direct-import scan of the inspected source found **zero AC → JV edges**. Preserve that boundary: an upward file move must not leave its AC consumers importing JV.

### Ownership by mathematical content

- **AC:** abstract divisor classes and their elementary `Pic0` quotient API, function-field genus, Riemann–Roch, and cohomology/base change for curves. The name `Pic0` alone does not make a theorem Jacobian-scheme theory: its quotient is already defined in `AlgebraicCurves/Divisors/ClassGroup.lean`.
- **JV:** relative Picard representability and gluing, the Picard deformation-class specification and its classification theorems, represented `Pic⁰`, Jacobian/Abel–Jacobi constructions, and their Poincaré/Weil-pairing interfaces.
- **Shared:** arbitrary-category, ring/module, and scheme/sheaf infrastructure without curve or Picard hypotheses, using the existing SchemeTheory inventory above. Do not move general curve cohomology into SchemeTheory merely because its conclusion concerns a sheaf.

### Batch 1: small divisor-class leaves, JV → AC

Move these three files from `Lean4/JacobianVarieties/Pic0/` to `Lean4/AlgebraicCurves/Divisors/`, keeping each basename and public declaration:

1. `Pic0_zsmul_mk.lean`: `AlgebraicCurve.Pic0.zsmul_mk`; integer scalar multiplication commutes with the degree-zero divisor quotient map
2. `Pic0_mk_eq_zero_iff.lean`: `AlgebraicCurve.Pic0.mk_eq_zero_iff`; the quotient class is zero exactly when the divisor is principal
3. `Pic0_subsingleton_of_forall_isPrincipal.lean`: `AlgebraicCurve.Pic0.subsingleton_of_forall_isPrincipal`; all degree-zero divisors principal implies the quotient is subsingleton

All three import only `AlgebraicCurves.Divisors.ClassGroup`. Their hypotheses contain fields, the field-algebra structure, and divisors; there is no represented Picard scheme. Direct nonaggregate consumers are `JacobianVarieties/Pic0/Pic0_zsmul_mk_eq_zero_of_isPrincipal.lean`, the genus-zero theorem below, and the two `JacobianVarieties/WeilPairing/DivisorialWeilPairingData_toHom_injective_of_divisible*.lean` leaves. Rewrite those imports and the owning aggregates in the same change. These moves need no extraction of a JV prerequisite.

### Batch 2: curve consequences, JV → AC

- `Lean4/JacobianVarieties/Pic0/Pic0_subsingleton_of_genusFF_eq_zero.lean` → `Lean4/AlgebraicCurves/Cohomology/RiemannRoch/Pic0_subsingleton_of_genusFF_eq_zero.lean`. Declaration: `AlgebraicCurve.Pic0.subsingleton_of_genusFF_eq_zero`. It assumes an algebraically closed base field, a curve function field essentially of finite type, and `genusFF = 0`; it concludes the abstract divisor-class `Pic0` is subsingleton. Move **after batch 1**, because its only JV dependency is `Pic0_subsingleton_of_forall_isPrincipal`. Its only current direct consumer is `JacobianVarieties/Pic0/All.lean`.
- `Lean4/JacobianVarieties/Picard/IsIso_baseChangeHom_pushforward_of_forall_fibre.lean` → `Lean4/AlgebraicCurves/Cohomology/Sheaves/IsIso_baseChangeHom_pushforward_of_forall_fibre.lean`. Declaration: `AlgebraicGeometry.RelPicard.isIso_baseChangeHom_pushforward_of_forall_fibre`. The actual assumptions are a noetherian base, a proper smooth relative curve of dimension one with a section and sufficiently large finite-map data, an invertible sheaf, fibrewise `H¹ = 0`, and constant `H⁰` rank. No `RepresentsRelSubPic` or Jacobian is assumed. All current imports are AC. Update its two JV leaf consumers, `Pullback_map_counit_app_ne_zero_of_forall_fibre.lean` and `Exists_pullbackSection_thetaBundle_eq_zero_iff.lean`, and the aggregates. Preserve the current public namespace initially; changing the module owner need not rename the theorem.

### Batch 3: Picard classification, AC → JV

- `Lean4/AlgebraicCurves/Geometry/Picard/PicDualNumberDeformationClassSpec.lean` → `Lean4/JacobianVarieties/Picard/PicDualNumberDeformationClassSpec.lean`. Main declaration: `AlgebraicGeometry.RelPicard.IsDeformationClassMap`, specifying the Čech `H¹` class assigned to a rigidified infinitesimal line bundle; the same file supplies `dualNumberThickening`, `oneAddEpsMul`, and `H1StructureSheaf`. It has **20 direct nonaggregate consumers, all in JV**, including `IsDeformationClassMap_injective.lean`, `IsDeformationClassMap_surjective.lean`, and `exists_isDeformationClassMap.lean`. Remove it from the AC Picard aggregate, add it to the JV Picard aggregate, and rewrite all 20 imports. Its lower-level AC deformation/sheaf prerequisites stay below it.
- `Lean4/AlgebraicCurves/Geometry/Picard/RelSubPic/Glue.lean` → `Lean4/JacobianVarieties/Picard/RelSubPicGlue.lean`, **after splitting its generic prefix**. The Picard declarations `AlgebraicGeometry.RelPicard.designationOfRepresentableBy`, `gluedDesignation`, and `RepresentsRelSubPic.nonempty_gluedDesignation` build a represented relative Picard object from representability/local charts. All **six direct nonaggregate consumers are JV** chart/existence leaves. However, its first section also proves arbitrary-category `CategoryTheory.Functor.overTotal_isSheaf` and its two elementary helpers. Put that section beside the generic `CategoryTheory_OverTotalPresheaf` provider before moving the Picard tail. The final shared home should be a new `SchemeTheory/CategoryTheory/OverTotalPresheaf.lean`; lower the provider with the helper section, rather than giving SchemeTheory an AC import. The Picard tail can continue importing the lower generic provider while that shared extraction is staged.

### Mixed providers: split before moving upward

Do **not** move the entire `AlgebraicCurves/Geometry/Picard/` directory. Three checked examples explain the necessary boundary work:

- `Designation.lean` mixes `GoodReductionJacobian.AbelianSchemePropertyBundle` with `RelativePic0Designation` and `AvatarSchemeBridge`. The abelian-scheme property package has AC abelian-scheme consumers and belongs with `Geometry/AbelianSchemes`, while the Picard carrier/bridge can ultimately belong to JV. Split them first.
- `Representation.lean` defines `SubPicCondition` and `RepresentsRelSubPic`, but still has **16 direct nonaggregate AC consumers**, including `Geometry/Deformation/RigKerDualNumber.lean` and generic norm-module leaves. Separate the predicate from representability, remove unnecessary high-level imports in lower consumers using their actual declaration usage, and move the coherent Picard consumer closure only afterward. A blind file move would introduce AC → JV edges.
- `ThetaBundle.lean` mixes `sectionIdeal`, `sectionTwist`, and `fibreModule` with `picardBundle` and `thetaBundle`. Keep/extract the section-ideal and fibre-module API below relative-divisor and curve-cohomology consumers; then move the Picard-specific constructions upward. It currently has **13 nonaggregate AC consumers**. Neither its filename nor its 106 JV imports justifies moving the whole file unchanged.

### Execution and verification order

1. Keep the separately staged five generic-flatness relocations separate from these edits; reuse their final shared paths when imports overlap.
2. At the compiler owner's next safe source boundary, perform batches 1–3 as small source/import/aggregate changes, beginning with the three independent quotient leaves. Do not mutate a source or its import closure during an active validation run. The mixed-provider split follows these bounded moves, not the other way around.
3. Preserve public theorem statements, mathematical namespaces, proof bodies for pure moves, and full source attribution. Use real moves and precise import rewrites; do not leave permanent forwarding files solely to hide old ownership.
4. Recompute direct consumers and reverse import closures from the then-current source. Require no new AC → JV edge, no new SchemeTheory → AC/JV edge, no duplicate module identity or missing aggregate reachability, and no import cycle. Static checks do not establish Lean success.
5. Validate each moved leaf and its direct consumers, then the smallest owning aggregates. Record the actual moves and verification in the same substantive commit as this appendix; retain the existing FLT addendum unchanged.
