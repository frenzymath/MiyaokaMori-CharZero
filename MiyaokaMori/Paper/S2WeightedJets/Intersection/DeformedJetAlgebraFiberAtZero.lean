import MiyaokaMori.Prelude
import MiyaokaMori.Paper.S2WeightedJets.Intersection.DeformedJetAlgebraFiberAtZero_PartIso
import MiyaokaMori.Paper.S2WeightedJets.Intersection.DeformedJetAlgebraFiberAtZero_ComparisonIso
import MiyaokaMori.Paper.S2WeightedJets.Jets.DeformedJetAlgebraFiberAtZero_LinearPieceDual
import MiyaokaMori.Algebra.WeightedSymAlgebraCongr

/-! # The fibre of the deformed jet algebra at `λ = 0`

`(deformedJetAlgebra Z sec hs r).restrictToLambda 0 ≅ weightedSymAlgebra r (fun _ => E)`: at `λ = 0` the Rees
deformation of the jet algebra `S` becomes the weighted symmetric algebra of `E^∨ ≅ (sec^*T_{Z/C})^∨` (one copy in
each weight `1, …, r`; `weightedSymAlgebra` takes the **duals** of its arguments as generators, see
`weightedSymAlgebra.gen`). This is "at `λ = 0` all nonlinear terms vanish" in Lemma 2.3 of the
paper; the algebraic input is Stacks 052P (`R/λR = gr_I(A)` for the extended Rees algebra).

Structure:
* the description of the pieces of the fibre, `reesDeformation_restrictToLambda_zero_part_iso`
  (`(s₀^*R)_j ≅ ⊕_{p ≤ j} I^{(p)}_j / I^{(p+1)}_j`, generic `S`), lives in `DeformedJetAlgebraFiberAtZero_PartIso`;
* `jetGradedAlgebra_linearPiece_iso_dual_of_smooth` (`DeformedJetAlgebraFiberAtZero_LinearPieceDual`), jet-specific:
  `S_{q+1}/I^{(2)}_{q+1} ≅ (sec^*T_{Z/C})^∨` **under the paper's smoothness hypotheses** (assembled from
  `jetGradedAlgebra_linearPiece_iso_pullback_omega`, proved through the `JetLinearPiece_*` modules);
* `reesDeformation_restrictToLambda_zero_iso_weightedSym` (this file): for a generic locally weighted-polynomial `S`
  with the jet weights, given identifications of the linear pieces `S_{q+1}/I^{(2)}_{q+1}` with `V_q^∨`,
  `s₀^*R ≅ weightedSymAlgebra V` (the comparison morphism `Φ : weightedSymAlgebra V ⟶ s₀^*R` of
  `DeformedJetAlgebraFiberAtZero_Comparison` is an isomorphism by `reesDeformation.comparisonHom_isIso`,
  `DeformedJetAlgebraFiberAtZero_ComparisonIso`);
* the final statement `deformedJetAlgebra_restrictToLambda_zero`, assembled from the previous two and `hEZ`.

The statement carries the paper's standing hypotheses
`[IsClosedImmersion sec] (Zx : Z.left.Opens) (hsZx : ∀ c, sec.base c ∈ Zx) [SmoothOfRelativeDimension (n+1) (Zx.ι ≫ Z.hom)]`
(§2 of the paper: `sec` lands in the open `𝒵^× ⊆ 𝒵` smooth over `C` of relative dimension `n+1`), exactly those of
`jetGradedAlgebra_isLocallyWeightedPolynomial`; `hloc` is kept since it is what the generic step consumes. Without them
the statement is false: `C = ℙ¹`, `Z = Spec_C (Sym L₁^∨ ×_{O_C} Sym L₂^∨)` with `L₁ = O(1)`, `L₂ = O` (two total spaces
glued along their zero sections), `sec` the zero section, `r = n = 1`: `hloc` holds (`S = Sym(I/I²)`,
`I/I² = L₁^∨ ⊕ L₂^∨`), `E = sec^*T_{Z/C} ≅ O_C²` (the two Euler fields), but `(s₀^*R)_1 = S_1 = O(-1) ⊕ O ≇ O_C² = E^∨`.
The same hypotheses appear in `deformedJetAlgebra_spec`, `deformation_removing_nonlinear`,
`deformationFamily_fiber_zero`, `deformationFamily_flat_projective` and `split_tautological_top_intersection_eq`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-! ## The pieces of the fibre

The description of the pieces of the fibre (`reesDeformation.partIsoGr`,
`reesDeformation_restrictToLambda_zero_part_iso`) lives in `DeformedJetAlgebraFiberAtZero_PartIso` (imported here),
so that the isomorphism below can be proved from the modules that build on `partIsoGr` without an import cycle. -/

namespace AlgebraicGeometry.Scheme.GradedQCAlgebra

/-! ## §2 The fibre as a weighted symmetric algebra -/

/-- **The fibre at `λ = 0` of the Rees deformation of a locally weighted-polynomial algebra with the jet weights is
the weighted symmetric algebra of the (duals of the) linear pieces** (generic `S`; source: Lemma 2.3
of the paper — at `λ = 0` only the linear parts of the transition functions survive; Stacks 052P).

Proof. Write `T := s₀^*R`, `ε_j := reesDeformation.partIsoGr S j` (the description of the pieces of `T`, a named
`def`), `L_m := coker (S.irrelevantPow 2 m).2 = S_m/I^{(2)}_m` (for `m ≥ 1` the weight-`m` linear piece
`(S_+/S_+^2)_m`), and `γ_q := reesDeformation.linearPieceToFiber S q : L_{q+1} ⟶ T_{q+1}`. No separate object
`gr_{S_+}(S)` is constructed: `T` itself plays that role, with `ε` as the description of its pieces.
(1) (`DeformedJetAlgebraFiberAtZero_LinearPiece`, `_Generators`) `I^{(1)}_m = S_m` for `m ≥ 1`
    (`isIso_irrelevantPow_one_snd`), hence `L_{q+1} ≅ coker (stepHom S 1 (q+1))` (`linearPieceIso`) and the generator
    map `γ_q` (the `p = 1` summand of `ε_{q+1}`) is a monomorphism; `T_0 ≅ S_0` (`fiberPartZeroIso`); the product
    `irrelevantPowMul : I^{(p)}_j ⊗ I^{(p')}_{j'} ⟶ I^{(p+p')}_{j+j'}`.
(2) (`_WeightedSymLift`) the universal property of `weightedSymAlgebra` gives `Φ : weightedSymAlgebra V ⟶ T` with
    `genIncl V q ≫ Φ.app (q+1) = (φ q).some.hom ≫ γ_q` (`_Comparison`).
(3) (`_ReesAtlas`, `_FiberChart`) `hS` gives a weighted-polynomial atlas `𝒜` of `S`; the atlas of `R` built in
    `reesDeformation_isLocallyWeightedPolynomial` is turned into data (`reesAtlas`, chart isomorphisms `reesChartEquiv`
    with `Φ_i ∘ e_i = Θ_i`) and pulled back along `s₀` to the **fibre chart** `χ_i : T(U_i) ≃+* Γ(U_i)[y_s]`
    (Stacks 01I9, `pullbackAtlasEquiv`); on the generator map, the class `γ_q(x)` of `x ∈ S_{q+1}(U_i)` goes to the
    **linear part** `homogeneousComponent 1 (φ_i x)` (`fiberChartEquiv_ofPiece_linearPieceToFiber`, via the Rees lift
    `reesLift`).
(4) (`_ComparisonIso`) `χ_i ∘ Φ(U_i) ∘ symLiftHom : Sym_{Γ(U_i)}(⊕_q Γ(U_i, V_q^∨)) → Γ(U_i)[y_s]` is a
    `Γ(U_i)`-algebra map that is injective on each `W_q` with image the linear forms in the `y_s` of weight `q+1`, and
    hitting every `y_s` (`𝒜.symm_mem`, `Stacks01y1Aux.surjective_app_of_epi`); such a map is bijective
    (`WeightedSym.algHom_bijective_of_gen`, pure algebra), so `Φ` is bijective on the section ring over every chart,
    hence on every piece (`Hom.app_app_bijective_of_sectionsRingHom_bijective`), hence an isomorphism
    (`isIso_of_affineOpens_cover_bijective`): `reesDeformation.comparisonHom_isIso`.
The multiplicativity of `ε` (`grSummandIncl_tensor_comp_mul_π_same/_ne`, the statement "`s₀^*R ≅ gr_{S_+}(S)` as
algebras") is proved in `_Generators` but is not invoked by this route.
Edge cases: `r = 0` (`σ` empty): `S = O_X`, `R = O_{A¹_X}`, both sides are `O_X` in weight `0` and `0` in positive
weights; `X = ∅`. -/
theorem reesDeformation_restrictToLambda_zero_iso_weightedSym {k : Type u} [Field k] {X : AlgebraicGeometry.Scheme.{u}}
    [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] (S : X.GradedQCAlgebra) (n r : ℕ)
    (hS : S.IsLocallyWeightedPolynomial
      (fun iq : ULift.{u} (Fin (n + 1) × Fin r) => ((iq.down.2 : ℕ) + 1)) (fun _ => Nat.succ_pos _))
    (V : Fin r → X.Modules) [∀ q, (V q).IsLocallyFree] [∀ q, (V q).IsFiniteType]
    (φ : ∀ q : Fin r, Nonempty (AlgebraicGeometry.Scheme.Modules.dual (V q) ≅
      CategoryTheory.Limits.cokernel (S.irrelevantPow 2 (q.1 + 1)).2)) :
    Nonempty (S.reesDeformation.restrictToLambda (0 : k) ≅ AlgebraicGeometry.Scheme.weightedSymAlgebra V) := by
  -- `hS` gives a weighted-polynomial atlas `𝒜` with the jet weights `w s = s.down.2 + 1`; the comparison morphism
  -- `Φ : weightedSymAlgebra V ⟶ s₀^*R` built from the identifications `φ` is an isomorphism by
  -- `reesDeformation.comparisonHom_isIso` (`DeformedJetAlgebraFiberAtZero_ComparisonIso`); invert it.
  obtain ⟨𝒜⟩ := hS
  have := reesDeformation.comparisonHom_isIso S (k := k) 𝒜 (fun _ => Nat.succ_pos _) V (fun q => (φ q).some)
    (fun iq => iq.down.2) (fun _ => rfl)
  exact ⟨(asIso (reesDeformation.comparisonHom S (k := k) V (fun q => (φ q).some))).symm⟩

end AlgebraicGeometry.Scheme.GradedQCAlgebra

/-! ## The linear pieces of the jet algebra

The jet-specific identification of the linear pieces is `jetGradedAlgebra_linearPiece_iso_dual_of_smooth` in
`DeformedJetAlgebraFiberAtZero_LinearPieceDual`, assembled from `jetGradedAlgebra_linearPiece_iso_pullback_omega` and
`dual_coneTangentBundle_iso_pullback_omega`. A version without the smoothness hypotheses (with only `hloc`, `hE`,
`hEZ`) would be false (counterexample in the module docstring). -/

/-! ## §3 Leaf (c), assembled -/

/-- **The fibre of the deformed jet algebra at `λ = 0` is the weighted symmetric algebra of `E ≅ s^*T_{Z/C}` (one copy
in each weight `1, …, r`).** Source: Lemma 2.3 of the paper ("at `λ = 0` all nonlinear terms
vanish"); §2 of the paper for the standing hypothesis that `sec` lands in an open `Zx ⊆ Z` smooth over `C` of relative
dimension `n+1`.

Assembled from two statements: `jetGradedAlgebra_linearPiece_iso_dual_of_smooth` — the weight-`(q+1)` linear piece
`S_{q+1}/I^{(2)}_{q+1}` of the jet algebra is `(sec^*T_{Z/C})^∨` — and `reesDeformation_restrictToLambda_zero_iso_weightedSym`
(for a locally weighted-polynomial `S` with the jet weights, the fibre at `0` of its Rees deformation is
`weightedSymAlgebra V` once `V_q^∨ ≅ S_{q+1}/I^{(2)}_{q+1}`), with `V_q := E` and `E^∨ ≅ (sec^*T)^∨` from `hEZ`
(`Modules.dualMapIso`).
Convention check: `weightedSymAlgebra V` has generators `V_q^∨` in weight `q+1` (`weightedSymAlgebra.gen`), and the
linear pieces of the jet algebra are duals of `sec^*T` (jet coordinates are functions), so the statement is consistent.
The hypotheses `[IsClosedImmersion sec] (Zx) (hsZx) [SmoothOfRelativeDimension (n+1) (Zx.ι ≫ Z.hom)]` are needed by
`jetGradedAlgebra_linearPiece_iso_dual_of_smooth`; without them the statement is false (module docstring). `hloc` is
kept as a hypothesis although it follows from them (`jetGradedAlgebra_isLocallyWeightedPolynomial`), since the
generic step consumes it directly. -/
theorem deformedJetAlgebra_restrictToLambda_zero {k : Type u} [Field k] [CharZero k] {C : SmoothProjectiveCurve k}
    (Z : CategoryTheory.Over C.toScheme) [AlgebraicGeometry.IsAffineHom Z.hom] (sec : C.toScheme ⟶ Z.left)
    (hs : sec ≫ Z.hom = CategoryTheory.CategoryStruct.id _) [AlgebraicGeometry.IsClosedImmersion sec]
    (Zx : Z.left.Opens) (hsZx : ∀ c, sec.base c ∈ Zx) (n r : ℕ)
    [AlgebraicGeometry.SmoothOfRelativeDimension (n + 1) (Zx.ι ≫ Z.hom)]
    (E : AlgebraicGeometry.VectorBundle C.toVariety) (hE : E.rank = n + 1)
    (hEZ : Nonempty (E.toModules ≅ coneTangentBundle Z.hom sec hs))
    (hloc : ((jetGradedAlgebra (k := k) Z sec hs r).1).IsLocallyWeightedPolynomial
      (fun iq : ULift.{u} (Fin (n + 1) × Fin r) => ((iq.down.2 : ℕ) + 1)) (fun _ => Nat.succ_pos _)) :
    Nonempty ((deformedJetAlgebra Z sec hs r).restrictToLambda (0 : k) ≅
      (@AlgebraicGeometry.Scheme.weightedSymAlgebra _ r (fun _ : Fin r => E.toModules) (fun _ => E.locallyFree) (fun _ => E.isFiniteType))) := by
  obtain ⟨e⟩ := hEZ
  exact @AlgebraicGeometry.Scheme.GradedQCAlgebra.reesDeformation_restrictToLambda_zero_iso_weightedSym k _ _ _
    (jetGradedAlgebra (k := k) Z sec hs r).1 n r hloc (fun _ : Fin r => E.toModules)
    (fun _ => E.locallyFree) (fun _ => E.isFiniteType)
    (fun q => ⟨(AlgebraicGeometry.Scheme.Modules.dualMapIso e).symm ≪≫
      (jetGradedAlgebra_linearPiece_iso_dual_of_smooth Z sec hs Zx hsZx n r q).some.symm⟩)

end
