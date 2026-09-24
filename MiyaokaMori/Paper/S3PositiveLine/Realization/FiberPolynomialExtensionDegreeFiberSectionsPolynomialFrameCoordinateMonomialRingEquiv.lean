import MiyaokaMori.Paper.S3PositiveLine.Realization.FiberPolynomialExtensionDegreeAffineLinePolynomial
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.FiberPolynomialExtensionDegreeFiberSectionsPolynomialFrameCoordinateMonomialConstants
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveBundle.FiberPolynomialExtensionDegreeFiberSectionsPolynomialFrameCoordinateMonomialRingEquivCoordinate
import MiyaokaMori.AlgebraicGeometry.Modules.TotalSpace.FiberPolynomialExtensionDegreeFiberSectionsPolynomialFrameCoordinateMonomialRingEquivFiberAffine
import MiyaokaMori.AlgebraicGeometry.Modules.RelativeSpecAffine
import MiyaokaMori.Paper.S3PositiveLine.JetNeighborhood.TautologicalSection
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.Frame

/-! # The fiber of the total space is an affine line with coordinate the tautological section

The fiber of `p : Tot(L) → C` over any point `y` is the affine line over `κ(y)`, with coordinate the
tautological section `ξ`: a ring isomorphism `φ : κ(y)[t] ≃+* Γ(Tot(L)_y, O)` sending constants to the
constants of the structure map `Tot(L)_y → Spec κ(y)` (`Scheme.Hom.fiberResidueConstants`), and a
trivialization `τ` of `ξ`'s line bundle on the fiber with `φ(t) = τ(ξ|_{Tot(L)_y})`.

Source: §3 of the paper (`Tot(L)` is locally `Spec O(V)[t]`; the fiber coordinate in the proof of Theorem 4.2).

The statement is over `κ(y)` for an arbitrary point `y`; `κ(y) = k` for a closed point of a variety
over `k = k̄` is applied only in the parent module. The theorem is assembled from
* the base-change glue `Scheme.Hom.fiber_exists_polynomial_ringEquiv`:
  for `f : X → Y`, an affine open `V ∋ y` with `f⁻¹V` affine and `Γ(f⁻¹V, O) = Γ(V, O)[x]`, the fiber has
  `Γ(F, O) ≅ κ(y)[t]` with `C c ↦ const c`, `t ↦ x|_F`; Mathlib `pullbackSpecIso`-type pasting,
  `IsAffineOpen.fromSpec`, `Polynomial.polyEquivTensor`), and
* the geometric lemma `totalSpace_exists_coordinate_of_isFrame`: over an affine open
  `V` with a frame `ε` of `L`, `Γ(p⁻¹V, O) = Γ(V, O)[x]` with `x = ξ/p^*ε`, i.e. a trivialization `τ₀` of `p^*L` on
  `p⁻¹V` with `τ₀(ξ|_{p⁻¹V}) = x`.
Glue in this module: frames exist on affine neighbourhoods (`Modules.exists_affine_frame_le`), `p` is affine
(`relativeSpec_isAffineHom`, `IsAffineOpen.preimage`), the fiber inclusion lifts through `p⁻¹V`
(`IsOpenImmersion.lift`, `range_fiberι_subset_range_ι`), transport of `τ₀` to the fiber
(`exists_unit_trivialization_of_comp`) and `appTop_ι_appLE_eq_appLE`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- (§3 of the paper) **The fiber of `Tot(L) → C` over any point `y` is the affine line over
`κ(y)`, with coordinate the tautological section `ξ`.**

Setting: `L` a line bundle on the smooth projective curve `C` over `k`, `p : Tot(L) → C`, `y ∈ C` *any*
point (closedness is not needed), `κ := κ(y)`, `F := p.fiber y = Tot(L) ×_C Spec κ`, `i := p.fiberι y`,
`π_F := p.fiberToSpecResidueField y : F → Spec κ`, `g := C.fromSpecResidueField y`, so `i ≫ p = π_F ≫ g`
(`Scheme.Hom.fiber_fac`). `const := fiberResidueConstants p y : κ → Γ(F, O_F)` is `π_F^♯` on global
sections.
Claim: there are a ring isomorphism `φ : κ[t] ≃+* Γ(F, O_F)` and a trivialization `τ : i^*(p^*L) ≅ O_F`
such that `φ(C a) = const a` for all `a ∈ κ` and `φ(t) = τ(i^*ξ)` (`ξ = tautologicalSection L`; the section
`τ(i^*ξ)` of `O_F` is read as a function through `unitSectionAsFunction`, definitionally the identity).

Proof (self-contained):
1. Frame. Choose an affine open `V ∋ y` and a frame `ε` of `L|_V` (`LineBundle.Frame`; it exists because
   `L` is locally free of rank one, hence trivial on an open neighbourhood of `y`, which contains an affine
   open neighbourhood). Let `t := ε^∨ ∈ Γ(V, L^∨)` be the dual frame (`t(ε) = 1`), a frame of `L^∨|_V`.
2. The chart. `p` is the relative `Spec` of `S := Sym(L^∨)` (`totalSpace = relativeSpec S.total`), so
   `p⁻¹V = Spec A(V)` with `A(V) := Γ(V, S) = (symGradedAlgebra (dual L)).total.sectionsRing V`
   (`relativeSpec.affineIso` / `AffineAlgebra.chart_isPullback`, RelativeSpecUniversalProperty), and the
   structure map `σ : S → p_*O_Tot` (`relativeSpec.structureHom`) is the identity `A(V) = Γ(p⁻¹V, O)` on `V`.
   With the basis `{t}` of the free `Γ(V, O)`-module `Γ(V, L^∨)`, `A(V) ≅ Γ(V, O)[x]` as `Γ(V, O)`-algebras
   with `x ↦ t` (degree one), `Γ(V, O) ↦` constants: this is
   `totalSpace_exists_sectionsRing_ringEquiv_mvPolynomial` (TotalSpaceSectionsRingEquivMvPolynomial;
   `SymmetricAlgebra.equivMvPolynomial` on the basis `{t}`), which must be strengthened to record that the
   variable is the image of the basis element `t` (its proof does send `t` to the variable).
3. The fiber is the base change of the chart. `g` lands in `V` (`Scheme.range_fromSpecResidueField`), so
   `g = g_V ≫ V.ι` with `g_V : Spec κ → V` (`IsOpenImmersion.lift`); the pullback of `p` along `V.ι` is
   `p ∣_ V : p⁻¹V → V` (Mathlib `isPullback_morphismRestrict`), so by pasting of pullbacks
   (`pullbackRightPullbackFstIso`) `F ≅ pullback (p ∣_ V) g_V` over `V`. Under `hV.isoSpec : V ≅ Spec Γ(V, O)`,
   `p ∣_ V` is `Spec.map (Γ(V, O) → A(V))` and `g_V` is `Spec.map (ev_y : Γ(V, O) → κ)` (the residue-field
   point of an affine scheme is `Spec` of the evaluation map: `IsAffineOpen.fromSpecResidueField`,
   `Spec.fiberToSpecResidueFieldIso`), so Mathlib's `pullbackSpecIso` gives
   `F ≅ Spec (A(V) ⊗_{Γ(V, O)} κ)`, compatibly with `π_F = Spec.map (κ → A(V) ⊗ κ, a ↦ 1 ⊗ a)`.
4. The coordinate ring. `A(V) ⊗_{Γ(V, O)} κ ≅ Γ(V, O)[x] ⊗_{Γ(V, O)} κ ≅ κ[x]` (polynomial rings commute
   with base change: Mathlib `Polynomial.polyEquivTensor` / `MvPolynomial.algebraTensorAlgEquiv`), sending
   `x ⊗ 1 ↦ x` and `1 ⊗ a ↦ C a`. Taking global sections (`Scheme.ΓSpecIso`) gives
   `φ : κ[x] ≃+* Γ(F, O_F)`, and `φ(C a) = const a` because `π_F` corresponds to `a ↦ 1 ⊗ a`.
5. The coordinate is `ξ`. The tautological section `ξ ∈ Γ(Tot, p^*L)` corresponds under
   `totalSpaceHomEquiv` to `𝟙_{Tot}`, whose algebra map `S → p_*O_Tot` is `σ`; its degree-one part, the
   functional `L^∨ → p_*O_Tot` of `ξ` (`totalSpace.tautologicalFunctional`, `functionalOfSectionCore`,
   TotalSpaceSectionConstructions), is `σ|_{L^∨}`, i.e. `⟨ξ, p^*t⟩ = σ(t) = x` in `Γ(p⁻¹V, O)`. Since `ε`
   is a frame with `t(ε) = 1`, this says `ξ|_{p⁻¹V} = x · p^*ε` in `Γ(p⁻¹V, p^*L)`. Restricting along
   `i : F → p⁻¹V ⊂ Tot` (`sectionPullbackAlong` is `O`-linear: `sectionPullbackAlong_smul`, and
   `i^♯(x) = φ(X)` by step 4), `i^*ξ = φ(X) · i^*(p^*ε)`. Let `τ : i^*(p^*L) ≅ O_F` be the trivialization
   with `τ(i^*(p^*ε)) = 1`: the pullback of the frame trivialization `ε.trivialization : O_V ≅ L|_V` along
   `F → V` (transport along `i ≫ p = π_F ≫ g_V ≫ V.ι`: `exists_unit_trivialization_of_comp`,
   `Modules.pullbackComp`). Then `τ(i^*ξ) = φ(X) · τ(i^*(p^*ε)) = φ(X)` (`Hom.app_smul`). ∎

Auxiliary facts:
(a) `totalSpace_exists_sectionsRing_ringEquiv_mvPolynomial` strengthened to record the variable
(`x` = image of the dual frame `t` under `sectionsRing V ∋ ι₁(t)`);
(b) `p.fiber y ≅ Spec (A(V) ⊗_{Γ(V, O)} κ(y))` for `y` in an affine open `V`, in the `Scheme.Hom.fiber`
API, compatible with `fiberToSpecResidueField` (Mathlib: `pullbackSpecIso`, `isPullback_morphismRestrict`,
`pullbackRightPullbackFstIso`; project: `relativeSpec.affineIso` / `chart_isPullback`);
(c) `ξ|_{p⁻¹V} = σ(t) · p^*ε` (the "`ξ = t·ε`" statement of `totLine_sections_over_frame`,
, whose current statement only asserts `Nonempty (… ≃ₐ …)`);
(d) polynomial base change `κ ⊗_{Γ(V, O)} Γ(V, O)[x] ≅ κ[x]` in the form needed by step 4 (Mathlib
`Polynomial.polyEquivTensor`, `MvPolynomial.algebraTensorAlgEquiv`).
Edge cases: `y` non-closed (then `κ(y) ⊋ k`; the statement is over `κ(y)` and stays true); `V = C` when `L`
is trivial; `L` arbitrary. Nothing here uses `IsAlgClosed k`.

Steps 3–4 and the constants formula are `Scheme.Hom.fiber_exists_polynomial_ringEquiv` (in general); steps 1–2
and 5 are `totalSpace_exists_coordinate_of_isFrame`; the proof below is glue only. -/
theorem totalSpace_fiber_exists_ringEquiv_tautologicalSection {k : Type u} [Field k]
    {C : SmoothProjectiveCurve k} (L : LineBundle C.toVariety) (y : C.toScheme) :
    ∃ (φ : Polynomial (C.toScheme.residueField y : Type u) ≃+*
        Γ((AlgebraicGeometry.Scheme.totalSpace L.toModules).hom.fiber y, ⊤))
      (τ : (AlgebraicGeometry.Scheme.Modules.pullback
          ((AlgebraicGeometry.Scheme.totalSpace L.toModules).hom.fiberι y)).obj
            ((AlgebraicGeometry.Scheme.Modules.pullback
              (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj L.toModules) ≅
          SheafOfModules.unit ((AlgebraicGeometry.Scheme.totalSpace L.toModules).hom.fiber y).ringCatSheaf),
      (∀ a : (C.toScheme.residueField y : Type u), φ (Polynomial.C a) =
          (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom.fiberResidueConstants y a) ∧
      φ Polynomial.X = AlgebraicGeometry.Scheme.Modules.unitSectionAsFunction (τ.hom.app ⊤ (sectionPullbackAlong
        ((AlgebraicGeometry.Scheme.totalSpace L.toModules).hom.fiberι y) (tautologicalSection L))) := by
  -- notation
  set p := (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom with hp
  -- an affine open neighbourhood `V ∋ y` with a frame `ε` of `L`
  obtain ⟨V, hV, -, hy, ε, hε⟩ :=
    AlgebraicGeometry.Scheme.Modules.exists_affine_frame_le L.toModules (U := ⊤) (p := y) trivial
  -- the frame coordinate `x = ξ/p^*ε` on `p⁻¹V`
  obtain ⟨x, τ₀, hx, hξ⟩ := totalSpace_exists_coordinate_of_isFrame L V hV ε hε
  -- `p` is affine, so `p⁻¹V` is affine and the fiber is `Spec` of `Γ(p⁻¹V, O) ⊗ κ(y) = κ(y)[t]`
  have : AlgebraicGeometry.IsAffineHom p := AlgebraicGeometry.Scheme.relativeSpec_isAffineHom _
  have hA : AlgebraicGeometry.IsAffineOpen (p ⁻¹ᵁ V) := hV.preimage p
  obtain ⟨φ, hC, hX⟩ := p.fiber_exists_polynomial_ringEquiv y hV hy hA x hx
  -- the fiber inclusion lifts through `p⁻¹V`
  let j : p.fiber y ⟶ (p ⁻¹ᵁ V).toScheme :=
    AlgebraicGeometry.IsOpenImmersion.lift (p ⁻¹ᵁ V).ι (p.fiberι y) (p.range_fiberι_subset_range_ι y hy)
  have hj : j ≫ (p ⁻¹ᵁ V).ι = p.fiberι y := AlgebraicGeometry.IsOpenImmersion.lift_fac _ _ _
  -- transport the trivialization `τ₀` to the fiber
  obtain ⟨τ, hτ⟩ := exists_unit_trivialization_of_comp j (p ⁻¹ᵁ V).ι _ τ₀ (p.fiberι y) hj
  refine ⟨φ, τ, hC, ?_⟩
  rw [hX]
  change _ = τ.hom.app ⊤ (sectionPullbackAlong (p.fiberι y) (tautologicalSection L))
  rw [hτ]
  change _ = j.appTop.hom (AlgebraicGeometry.Scheme.Modules.unitSectionAsFunction
    (τ₀.hom.app ⊤ (sectionPullbackAlong (p ⁻¹ᵁ V).ι (tautologicalSection L))))
  rw [hξ]
  exact (AlgebraicGeometry.Scheme.Hom.appTop_ι_appLE_eq_appLE j (p.fiberι y) hj _ _ x).symm

end
