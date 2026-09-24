import MiyaokaMori.Paper.S3PositiveLine.Realization.FiberPolynomialExtensionDegreeFiberChart
import MiyaokaMori.AlgebraicGeometry.Modules.TotalSpace.FiberPolynomialExtensionDegreeFiberSectionsPolynomial
import MiyaokaMori.Paper.S3PositiveLine.Realization.MorphismNearZeroData
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.P1MapDegreeFromPolynomials
import MiyaokaMori.Paper.S3PositiveLine.Realization.ProjectivizationMorphismCongrIso
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.SectionPullbackNotZeroAt

/-! # The fiber of an open of `Tot(L)` inside the ruled fiber `P¹`, and extension of polynomial tuples

The fiber `U_y` of an open `U ⊆ Tot(L)` over a closed point `y` sits inside the ruled fiber
`W_y = π_W^{-1}(y) ≅ P¹`; a tuple of sections of `p^*M` on `Tot(L)` with ξ-degree `≤ r₀` restricts to
`U_y` as a tuple of polynomials of degree `≤ r₀`, and its projectivization extends to a morphism
`g : P¹ → P^N` of `O(1)`-degree `m ≤ r₀` (`m ≥ 1` when `g` is nonconstant).

Source: Theorem 4.2 of the paper ("Homogenizing in the fiber coordinate gives homogeneous
coordinates of a common degree at most `r_0`. Removing a common factor can only decrease the degree.").

The degree bound for the general fiber (`FiberPolynomialExtensionDegree.lean`) is assembled from this
module plus general facts (factoring through a closed immersion, degree bookkeeping). This module also
provides the canonical open immersion `totalSpaceOpenFiberToRuledFiber : U_y ⟶ W_y`.

`fiber_restriction_extends_to_p1` is assembled from two lemmas in sibling modules
(`FiberPolynomialExtensionDegreeFiberChart`: `totalSpace_fiber_chart_ruledFiber_iso_p1`, the fiber
`Tot(L)_y ≅ A¹ ⊆ P¹ ≅ W_y` with the standard chart; `FiberPolynomialExtensionDegreeFiberSectionsPolynomial`:
`totalSpace_fiber_sections_polynomial`, the restricted sections are polynomials of degree `≤ r₀`),
the lemmas `p1_map_degree_of_polynomial_tuple`, `projectivizationMorphism_pullback`,
`projectivizationMorphism_congr_iso`, `isZeroAt_iso_iff`, and glue
(`FiberPolynomialExtensionDegreeAffineLinePolynomial`, and the fiber maps below).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- The canonical morphism from the (scheme-theoretic) fiber of `U ⊆ Tot(L) → C̃` over `y` into the
fiber of the ruling `π_W : W → C̃` over `y`, induced by the open immersion `U ⊆ Tot(L) ⊆ W`
(`pullback.map` along `U.ι ≫ ruledSurface.totalSpaceIncl L`, identity on `Spec κ(y)` and `C̃`). -/
noncomputable def totalSpaceOpenFiberToRuledFiber {k : Type u} [Field k] {C : SmoothProjectiveCurve k}
    (L : LineBundle C.toVariety)
    (U : (AlgebraicGeometry.Scheme.totalSpace L.toModules).left.Opens) (y : C.toScheme) :
    (U.ι ≫ (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).fiber y ⟶
      (ruledSurface.π L).fiber y :=
  pullback.map (U.ι ≫ (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom)
    (C.toScheme.fromSpecResidueField y) (ruledSurface.π L) (C.toScheme.fromSpecResidueField y)
    (U.ι ≫ ruledSurface.totalSpaceIncl L) (𝟙 _) (𝟙 _)
    (by rw [Category.comp_id, Category.assoc, ruledSurface.totalSpaceIncl_comp_π])
    (by simp)

/-- The fiber inclusion `U_y ⟶ W_y` is an open immersion (base change of the open immersion
`U ⊆ W`; Mathlib `Scheme.pullback_map_isOpenImmersion`). Not registered as a global instance. -/
theorem totalSpaceOpenFiberToRuledFiber_isOpenImmersion {k : Type u} [Field k]
    {C : SmoothProjectiveCurve k} (L : LineBundle C.toVariety)
    (U : (AlgebraicGeometry.Scheme.totalSpace L.toModules).left.Opens) (y : C.toScheme) :
    AlgebraicGeometry.IsOpenImmersion (totalSpaceOpenFiberToRuledFiber L U y) := by
  have := ruledSurface.totalSpaceIncl_isOpenImmersion L
  unfold totalSpaceOpenFiberToRuledFiber
  exact AlgebraicGeometry.Scheme.pullback_map_isOpenImmersion _ _ _ _ _ _ _ _ _

/-- Compatibility with the fiber embeddings: `U_y → W_y → W` equals `U_y → U → Tot(L) → W`. -/
theorem totalSpaceOpenFiberToRuledFiber_comp_fiberι {k : Type u} [Field k]
    {C : SmoothProjectiveCurve k} (L : LineBundle C.toVariety)
    (U : (AlgebraicGeometry.Scheme.totalSpace L.toModules).left.Opens) (y : C.toScheme) :
    totalSpaceOpenFiberToRuledFiber L U y ≫ (ruledSurface.π L).fiberι y =
      (U.ι ≫ (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).fiberι y ≫
        U.ι ≫ ruledSurface.totalSpaceIncl L := by
  unfold totalSpaceOpenFiberToRuledFiber AlgebraicGeometry.Scheme.Hom.fiberι
  exact pullback.lift_fst _ _ _

/-- The fiber of `U ⊆ Tot(L) → C̃` over `y` maps into the fiber of `Tot(L) → C̃` over `y`
(`pullback.map` along the open immersion `U.ι`). -/
noncomputable def totalSpaceOpenFiberToTotalSpaceFiber {k : Type u} [Field k]
    {C : SmoothProjectiveCurve k} (L : LineBundle C.toVariety)
    (U : (AlgebraicGeometry.Scheme.totalSpace L.toModules).left.Opens) (y : C.toScheme) :
    (U.ι ≫ (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).fiber y ⟶
      (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom.fiber y :=
  pullback.map (U.ι ≫ (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom)
    (C.toScheme.fromSpecResidueField y) (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom
    (C.toScheme.fromSpecResidueField y) U.ι (𝟙 _) (𝟙 _) (by rw [Category.comp_id]) (by simp)

/-- `U_y → Tot(L)_y → Tot(L)` equals `U_y → U → Tot(L)`. -/
theorem totalSpaceOpenFiberToTotalSpaceFiber_comp_fiberι {k : Type u} [Field k]
    {C : SmoothProjectiveCurve k} (L : LineBundle C.toVariety)
    (U : (AlgebraicGeometry.Scheme.totalSpace L.toModules).left.Opens) (y : C.toScheme) :
    totalSpaceOpenFiberToTotalSpaceFiber L U y ≫
        (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom.fiberι y =
      (U.ι ≫ (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).fiberι y ≫ U.ι := by
  unfold totalSpaceOpenFiberToTotalSpaceFiber AlgebraicGeometry.Scheme.Hom.fiberι
  exact pullback.lift_fst _ _ _

/-- `U_y → Tot(L)_y` is an open immersion (base change of `U.ι`). Not a global instance. -/
theorem totalSpaceOpenFiberToTotalSpaceFiber_isOpenImmersion {k : Type u} [Field k]
    {C : SmoothProjectiveCurve k} (L : LineBundle C.toVariety)
    (U : (AlgebraicGeometry.Scheme.totalSpace L.toModules).left.Opens) (y : C.toScheme) :
    AlgebraicGeometry.IsOpenImmersion (totalSpaceOpenFiberToTotalSpaceFiber L U y) := by
  unfold totalSpaceOpenFiberToTotalSpaceFiber
  exact AlgebraicGeometry.Scheme.pullback_map_isOpenImmersion _ _ _ _ _ _ _ _ _

set_option backward.isDefEq.respectTransparency false in
/-- `U_y → Tot(L)_y → W_y` is the fiber inclusion `U_y → W_y` (functoriality of `pullback.map`,
Mathlib `pullback.map_comp`; the `set_option` is the one Mathlib itself uses for that lemma). -/
theorem totalSpaceOpenFiberToTotalSpaceFiber_comp_totalSpaceFiberToRuledFiber {k : Type u} [Field k]
    {C : SmoothProjectiveCurve k} (L : LineBundle C.toVariety)
    (U : (AlgebraicGeometry.Scheme.totalSpace L.toModules).left.Opens) (y : C.toScheme) :
    totalSpaceOpenFiberToTotalSpaceFiber L U y ≫ totalSpaceFiberToRuledFiber L y =
      totalSpaceOpenFiberToRuledFiber L U y := by
  unfold totalSpaceOpenFiberToTotalSpaceFiber totalSpaceFiberToRuledFiber totalSpaceOpenFiberToRuledFiber
  rw [pullback.map_comp]
  simp

/-- If `U` contains the zero section, the fiber `U_y` is nonempty (it contains the zero-section
point over `y`, since `zeroSection ≫ p = 𝟙`). -/
theorem totalSpaceOpenFiber_nonempty {k : Type u} [Field k]
    {C : SmoothProjectiveCurve k} (L : LineBundle C.toVariety)
    (U : (AlgebraicGeometry.Scheme.totalSpace L.toModules).left.Opens)
    (hU0 : Set.range (AlgebraicGeometry.Scheme.zeroSection L.toModules).base ⊆
      (U : Set (AlgebraicGeometry.Scheme.totalSpace L.toModules).left)) (y : C.toScheme) :
    Nonempty ((U.ι ≫ (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).fiber y) := by
  have hmem : (AlgebraicGeometry.Scheme.zeroSection L.toModules).base y ∈
      (U : Set (AlgebraicGeometry.Scheme.totalSpace L.toModules).left) := hU0 ⟨y, rfl⟩
  have hrange : (AlgebraicGeometry.Scheme.zeroSection L.toModules).base y ∈ Set.range U.ι.base := by
    rw [AlgebraicGeometry.Scheme.Opens.range_ι]; exact hmem
  obtain ⟨u, hu⟩ := hrange
  have hy : (U.ι ≫ (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).base u = y := by
    rw [AlgebraicGeometry.Scheme.Hom.comp_apply, hu, ← AlgebraicGeometry.Scheme.Hom.comp_apply,
      AlgebraicGeometry.Scheme.zeroSection_comp]
    rfl
  exact ⟨((U.ι ≫ (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).fiberHomeo y).symm ⟨u, hy⟩⟩

/-- **Extension of the restricted polynomial tuple to `P¹`** (Theorem 4.2 of the paper).

Setting: `L`, `M` line bundles on the smooth projective curve `C` over `k = k̄`;
`p : Tot(L) → C`; `P ℓ ∈ Γ(Tot(L), p^*M)` (`ℓ = 0, …, N`, `N = X.embDim`) with ξ-degree `≤ r₀` (`hP`);
`U ⊆ Tot(L)` open containing the zero section (`hU0`); `Φ₀ : U → X` with
`Φ₀ ≫ emb = projectivization (P|_U)` (`hΦ`); `y` a closed point of `C`.
Claim: there are an isomorphism `e : W_y ≅ P¹` of the ruled fiber `W_y = π_W^{-1}(y)`,
a morphism `g : P¹ → P^N` and `m ≤ r₀` with `deg g^*O(1) = m`, `1 ≤ m` if `g` is nonconstant, and
`(U_y → U → X → P^N) = (U_y → W_y → P¹ → P^N)` where `U_y → W_y` is `totalSpaceOpenFiberToRuledFiber`.

Proof (as formalized below):
1. `totalSpace_fiber_chart_ruledFiber_iso_p1`:
   `α : Tot(L)_y ≅ A¹_k` over `k` and `e : W_y ≅ P¹` with `(Tot(L)_y → W_y) ≫ e = α ≫ stdChart`.
   (It uses `κ(y) = k`, Mathlib `residueFieldIsoBase`.)
2. `totalSpace_fiber_sections_polynomial`:
   polynomials `Q ℓ ∈ k[t]` of degree `≤ r₀` and a trivialization `τ₀` of `(p.fiberι y)^*(p^*M)` with
   `τ₀ (P ℓ|_{Tot(L)_y}) = α^*(Q ℓ)`.
3. Glue. `ι' : U_y → Tot(L)_y` (`totalSpaceOpenFiberToTotalSpaceFiber`) is an open immersion with
   `ι' ≫ (Tot(L)_y → W_y) = (U_y → W_y)`; `O := (ι' ≫ α.hom).opensRange ⊆ A¹`, `β : U_y ≅ O`
   (`isoOpensRange`), `j₀ := β.inv ≫ ι' : O → Tot(L)_y` satisfies `j₀ ≫ α.hom = O.ι`. Transporting `τ₀`
   along `j₀` (`exists_unit_trivialization_of_comp`) and composing with `pullbackComp` gives
   `τ' : (β.inv ≫ U_y → U)^*(U.ι^*(p^*M)) ≅ O_O` with `τ'((β.inv ≫ …)^*(U.ι^*(P ℓ))) = polynomialSection O (Q ℓ)`.
4. Not all `Q ℓ` vanish: `U_y ≠ ∅` (`totalSpaceOpenFiber_nonempty`), `hΦ.1` gives at every point of
   `U` a non-vanishing `P ℓ`; pulled back (`not_isZeroAt_sectionPullbackAlong`) and transported along
   `τ'` (`isZeroAt_iso_iff`) this gives `hO : ∀ v ∈ O, ∃ ℓ, ¬IsZeroAt (polynomialSection O (Q ℓ)) v`, and
   `Q ℓ ≠ 0` for some `ℓ` (`polynomialSection O 0 = 0`, `IsZeroAt.zero`).
5. `p1_map_degree_of_polynomial_tuple Q`: `m ≤ r₀`, `g : P¹ → P^N`, `¬IsConstantMorphism g → 1 ≤ m`,
   `deg (LineBundle.ofModules (g^*O(1))) = m`, and `O.ι ≫ stdChart ≫ g = projectivization (polynomialSection O (Q ·))`.
6. Equality of morphisms: `(U_y → W_y) ≫ e.hom ≫ g = β.hom ≫ O.ι ≫ stdChart ≫ g = β.hom ≫ proj_O(Q)`
   (steps 1, 3, 5), while `U_y → U → X → P^N = β.hom ≫ (β.inv ≫ U_y → U) ≫ proj_U(U.ι^*P)` (`hΦ`),
   `= β.hom ≫ proj_O((β.inv ≫ …)^*(U.ι^*P))` (`projectivizationMorphism_pullback`; the map `O → U` is a
   `k`-morphism by `hα`), `= β.hom ≫ proj_O(Q)` (`projectivizationMorphism_congr_iso` along `τ'`,
   `projectivizationMorphism_congr_sections`).

Edge cases: `r₀ = 0` (all `Q ℓ` constant, `g` constant, `m = 0`, the nonconstancy clause is vacuous);
`N = 0` (`P^0` is a point, `g` constant, `m = 0`). -/
theorem fiber_restriction_extends_to_p1 {k : Type u} [Field k] [IsAlgClosed k]
    {X : SmoothProjectiveVariety k} {C : SmoothProjectiveCurve k}
    (L M : LineBundle C.toVariety) {r₀ : ℕ}
    (P : Fin (X.embDim + 1) →
      (((AlgebraicGeometry.Scheme.Modules.pullback
        (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj M.toModules).val.obj
          (Opposite.op ⊤) : Type u))
    (hP : ∀ ℓ, xiDegree L M (P ℓ) ≤ (r₀ : WithBot ℕ))
    (U : (AlgebraicGeometry.Scheme.totalSpace L.toModules).left.Opens)
    (Φ₀ : U.toScheme ⟶ X.toScheme) (hΦ : IsTupleProjectivization _ P U Φ₀)
    (hU0 : Set.range (AlgebraicGeometry.Scheme.zeroSection L.toModules).base ⊆
      (U : Set (AlgebraicGeometry.Scheme.totalSpace L.toModules).left))
    (y : C.toScheme) (hy : IsClosed ({y} : Set C.toScheme)) :
    ∃ (e : ((ruledSurface.π L).fiber y) ≅ (ProjectiveLine.asSmoothProjectiveCurve k).toScheme)
      (g : (ProjectiveLine.asSmoothProjectiveCurve k).toScheme ⟶ ProjectiveSpace X.embDim k)
      (m : ℕ),
      m ≤ r₀ ∧ (¬ IsConstantMorphism g → 1 ≤ m) ∧
      (LineBundle.ofModules (X := (ProjectiveLine.asSmoothProjectiveCurve k).toVariety)
        ((AlgebraicGeometry.Scheme.Modules.pullback g).obj
          (projectiveSpaceTwist k X.embDim 1))).degree = (m : ℤ) ∧
      (U.ι ≫ (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).fiberι y ≫ Φ₀ ≫
          X.embedding.emb =
        totalSpaceOpenFiberToRuledFiber L U y ≫ e.hom ≫ g := by
  obtain ⟨hU, hΦeq⟩ := hΦ
  obtain ⟨α, e, hα, hαe⟩ := totalSpace_fiber_chart_ruledFiber_iso_p1 L y hy
  obtain ⟨Q, hQdeg, τ₀, hτ₀⟩ := totalSpace_fiber_sections_polynomial L M P hP y hy α hα
  have hι'ι : (totalSpaceOpenFiberToTotalSpaceFiber L U y) ≫ (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom.fiberι y = ((U.ι ≫ (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom)).fiberι y ≫ U.ι :=
    totalSpaceOpenFiberToTotalSpaceFiber_comp_fiberι L U y
  have hθ : (totalSpaceOpenFiberToTotalSpaceFiber L U y) ≫ totalSpaceFiberToRuledFiber L y = totalSpaceOpenFiberToRuledFiber L U y :=
    totalSpaceOpenFiberToTotalSpaceFiber_comp_totalSpaceFiberToRuledFiber L U y
  have hι'o : AlgebraicGeometry.IsOpenImmersion (totalSpaceOpenFiberToTotalSpaceFiber L U y) :=
    totalSpaceOpenFiberToTotalSpaceFiber_isOpenImmersion L U y
  -- `O ⊆ A¹` is the image of `U_y`, `β : U_y ≅ O`
  have hβι : ((totalSpaceOpenFiberToTotalSpaceFiber L U y) ≫ α.hom).isoOpensRange.hom ≫ ((totalSpaceOpenFiberToTotalSpaceFiber L U y) ≫ α.hom).opensRange.ι = (totalSpaceOpenFiberToTotalSpaceFiber L U y) ≫ α.hom := AlgebraicGeometry.Scheme.Hom.isoOpensRange_hom_ι _
  have hβinv : ((totalSpaceOpenFiberToTotalSpaceFiber L U y) ≫ α.hom).isoOpensRange.inv ≫ ((totalSpaceOpenFiberToTotalSpaceFiber L U y) ≫ α.hom) = ((totalSpaceOpenFiberToTotalSpaceFiber L U y) ≫ α.hom).opensRange.ι := AlgebraicGeometry.Scheme.Hom.isoOpensRange_inv_comp _
  have hjα : (((totalSpaceOpenFiberToTotalSpaceFiber L U y) ≫ α.hom).isoOpensRange.inv ≫ (totalSpaceOpenFiberToTotalSpaceFiber L U y)) ≫ α.hom = ((totalSpaceOpenFiberToTotalSpaceFiber L U y) ≫ α.hom).opensRange.ι := by
    rw [Category.assoc]; exact hβinv
  have hj : (((totalSpaceOpenFiberToTotalSpaceFiber L U y) ≫ α.hom).isoOpensRange.inv ≫ (totalSpaceOpenFiberToTotalSpaceFiber L U y)) ≫ (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom.fiberι y = (((totalSpaceOpenFiberToTotalSpaceFiber L U y) ≫ α.hom).isoOpensRange.inv ≫ (U.ι ≫ (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).fiberι y) ≫ U.ι := by
    rw [Category.assoc, Category.assoc, hι'ι]
  obtain ⟨τ, hτ⟩ := exists_unit_trivialization_of_comp (((totalSpaceOpenFiberToTotalSpaceFiber L U y) ≫ α.hom).isoOpensRange.inv ≫ (totalSpaceOpenFiberToTotalSpaceFiber L U y)) ((AlgebraicGeometry.Scheme.totalSpace L.toModules).hom.fiberι y)
    ((AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj M.toModules) τ₀ ((((totalSpaceOpenFiberToTotalSpaceFiber L U y) ≫ α.hom).isoOpensRange.inv ≫ (U.ι ≫ (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).fiberι y) ≫ U.ι) hj
  have hsec : ∀ ℓ, τ.hom.app ⊤ (sectionPullbackAlong ((((totalSpaceOpenFiberToTotalSpaceFiber L U y) ≫ α.hom).isoOpensRange.inv ≫ (U.ι ≫ (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).fiberι y) ≫ U.ι) (P ℓ)) = polynomialSection ((totalSpaceOpenFiberToTotalSpaceFiber L U y) ≫ α.hom).opensRange (Q ℓ) := by
    intro ℓ
    rw [hτ, hτ₀, polynomialSection_eq_appTop, ← hjα]
    rfl
  have hsec' : ∀ ℓ, (((((AlgebraicGeometry.Scheme.Modules.pullbackComp (((totalSpaceOpenFiberToTotalSpaceFiber L U y) ≫ α.hom).isoOpensRange.inv ≫ (U.ι ≫ (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).fiberι y) U.ι).app ((AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj M.toModules)) ≪≫ τ) : (AlgebraicGeometry.Scheme.Modules.pullback (((totalSpaceOpenFiberToTotalSpaceFiber L U y) ≫ α.hom).isoOpensRange.inv ≫ (U.ι ≫ (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).fiberι y)).obj ((AlgebraicGeometry.Scheme.Modules.pullback U.ι).obj ((AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj M.toModules)) ≅ SheafOfModules.unit (((totalSpaceOpenFiberToTotalSpaceFiber L U y) ≫ α.hom).opensRange).toScheme.ringCatSheaf)).hom.app ⊤ (sectionPullbackAlong (((totalSpaceOpenFiberToTotalSpaceFiber L U y) ≫ α.hom).isoOpensRange.inv ≫ (U.ι ≫ (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).fiberι y) (sectionPullbackAlong U.ι (P ℓ))) =
      polynomialSection ((totalSpaceOpenFiberToTotalSpaceFiber L U y) ≫ α.hom).opensRange (Q ℓ) := by
    intro ℓ
    rw [← hsec ℓ]
    have h1 : (((AlgebraicGeometry.Scheme.Modules.pullbackComp (((totalSpaceOpenFiberToTotalSpaceFiber L U y) ≫ α.hom).isoOpensRange.inv ≫ (U.ι ≫ (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).fiberι y) U.ι).app
        ((AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj M.toModules)).inv.app ⊤)
          (sectionPullbackAlong ((((totalSpaceOpenFiberToTotalSpaceFiber L U y) ≫ α.hom).isoOpensRange.inv ≫ (U.ι ≫ (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).fiberι y) ≫ U.ι) (P ℓ)) =
        sectionPullbackAlong (((totalSpaceOpenFiberToTotalSpaceFiber L U y) ≫ α.hom).isoOpensRange.inv ≫ (U.ι ≫ (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).fiberι y) (sectionPullbackAlong U.ι (P ℓ)) :=
      AlgebraicGeometry.Scheme.Modules.ModuleSections.pullback_comp_inv (((totalSpaceOpenFiberToTotalSpaceFiber L U y) ≫ α.hom).isoOpensRange.inv ≫ (U.ι ≫ (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).fiberι y) U.ι (P ℓ)
    change τ.hom.app ⊤ (((AlgebraicGeometry.Scheme.Modules.pullbackComp (((totalSpaceOpenFiberToTotalSpaceFiber L U y) ≫ α.hom).isoOpensRange.inv ≫ (U.ι ≫ (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).fiberι y) U.ι).app
      ((AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj M.toModules)).hom.app ⊤
      (sectionPullbackAlong (((totalSpaceOpenFiberToTotalSpaceFiber L U y) ≫ α.hom).isoOpensRange.inv ≫ (U.ι ≫ (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).fiberι y) (sectionPullbackAlong U.ι (P ℓ)))) = _
    rw [← h1]
    congr 1
    exact AlgebraicGeometry.Scheme.Modules.iso_inv_app_hom_app
      ((AlgebraicGeometry.Scheme.Modules.pullbackComp (((totalSpaceOpenFiberToTotalSpaceFiber L U y) ≫ α.hom).isoOpensRange.inv ≫ (U.ι ≫ (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).fiberι y) U.ι).app _).symm ⊤ _
  -- nonvanishing
  have hpull : ∀ v : (((totalSpaceOpenFiberToTotalSpaceFiber L U y) ≫ α.hom).opensRange).toScheme, ∃ ℓ,
      ¬ IsZeroAt (sectionPullbackAlong (((totalSpaceOpenFiberToTotalSpaceFiber L U y) ≫ α.hom).isoOpensRange.inv ≫ (U.ι ≫ (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).fiberι y) (sectionPullbackAlong U.ι (P ℓ))) v := by
    intro v
    obtain ⟨ℓ, hℓ⟩ := hU (((((totalSpaceOpenFiberToTotalSpaceFiber L U y) ≫ α.hom).isoOpensRange.inv ≫ (U.ι ≫ (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).fiberι y)).base v)
    exact ⟨ℓ, not_isZeroAt_sectionPullbackAlong (((totalSpaceOpenFiberToTotalSpaceFiber L U y) ≫ α.hom).isoOpensRange.inv ≫ (U.ι ≫ (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).fiberι y) _ _ v hℓ⟩
  have hO' : ∀ v : (((totalSpaceOpenFiberToTotalSpaceFiber L U y) ≫ α.hom).opensRange).toScheme, ∃ ℓ,
      ¬ IsZeroAt ((((((AlgebraicGeometry.Scheme.Modules.pullbackComp (((totalSpaceOpenFiberToTotalSpaceFiber L U y) ≫ α.hom).isoOpensRange.inv ≫ (U.ι ≫ (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).fiberι y) U.ι).app ((AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj M.toModules)) ≪≫ τ) : (AlgebraicGeometry.Scheme.Modules.pullback (((totalSpaceOpenFiberToTotalSpaceFiber L U y) ≫ α.hom).isoOpensRange.inv ≫ (U.ι ≫ (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).fiberι y)).obj ((AlgebraicGeometry.Scheme.Modules.pullback U.ι).obj ((AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj M.toModules)) ≅ SheafOfModules.unit (((totalSpaceOpenFiberToTotalSpaceFiber L U y) ≫ α.hom).opensRange).toScheme.ringCatSheaf)).hom.app ⊤ (sectionPullbackAlong (((totalSpaceOpenFiberToTotalSpaceFiber L U y) ≫ α.hom).isoOpensRange.inv ≫ (U.ι ≫ (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).fiberι y) (sectionPullbackAlong U.ι (P ℓ)))) v :=
    exists_not_isZeroAt_iso ((((AlgebraicGeometry.Scheme.Modules.pullbackComp (((totalSpaceOpenFiberToTotalSpaceFiber L U y) ≫ α.hom).isoOpensRange.inv ≫ (U.ι ≫ (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).fiberι y) U.ι).app ((AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj M.toModules)) ≪≫ τ) : (AlgebraicGeometry.Scheme.Modules.pullback (((totalSpaceOpenFiberToTotalSpaceFiber L U y) ≫ α.hom).isoOpensRange.inv ≫ (U.ι ≫ (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).fiberι y)).obj ((AlgebraicGeometry.Scheme.Modules.pullback U.ι).obj ((AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj M.toModules)) ≅ SheafOfModules.unit (((totalSpaceOpenFiberToTotalSpaceFiber L U y) ≫ α.hom).opensRange).toScheme.ringCatSheaf) _ hpull
  have hO : ∀ v : (((totalSpaceOpenFiberToTotalSpaceFiber L U y) ≫ α.hom).opensRange).toScheme, ∃ ℓ, ¬ IsZeroAt (polynomialSection ((totalSpaceOpenFiberToTotalSpaceFiber L U y) ≫ α.hom).opensRange (Q ℓ)) v := by
    intro v
    obtain ⟨ℓ, h⟩ := hO' v
    rw [hsec' ℓ] at h
    exact ⟨ℓ, h⟩
  have hne : ∃ ℓ, Q ℓ ≠ 0 := by
    obtain ⟨u⟩ := totalSpaceOpenFiber_nonempty L U hU0 y
    obtain ⟨ℓ, hℓ⟩ := hO ((((totalSpaceOpenFiberToTotalSpaceFiber L U y) ≫ α.hom).isoOpensRange).hom.base u)
    refine ⟨ℓ, fun h0 => hℓ ?_⟩
    rw [h0, polynomialSection_zero]
    exact IsZeroAt.zero _
  obtain ⟨m, g, hm, hnc, hdeg, hchart⟩ := p1_map_degree_of_polynomial_tuple Q hQdeg hne
  refine ⟨e, g, m, hm, hnc, hdeg, ?_⟩
  have hθe : totalSpaceOpenFiberToRuledFiber L U y ≫ e.hom =
      ((totalSpaceOpenFiberToTotalSpaceFiber L U y) ≫ α.hom).isoOpensRange.hom ≫ ((totalSpaceOpenFiberToTotalSpaceFiber L U y) ≫ α.hom).opensRange.ι ≫ ProjectiveLine.stdChart k := by
    rw [← hθ, Category.assoc, hαe]
    conv_rhs => rw [← Category.assoc, hβι]
    rw [Category.assoc]
  have hover : (((totalSpaceOpenFiberToTotalSpaceFiber L U y) ≫ α.hom).isoOpensRange.inv ≫ (U.ι ≫ (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).fiberι y) ≫ (U.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) =
      ((((totalSpaceOpenFiberToTotalSpaceFiber L U y) ≫ α.hom).opensRange).toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) := by
    change (((totalSpaceOpenFiberToTotalSpaceFiber L U y) ≫ α.hom).isoOpensRange.inv ≫ (U.ι ≫ (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).fiberι y) ≫ (U.ι ≫ (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom ≫ (C.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k))) =
      (((totalSpaceOpenFiberToTotalSpaceFiber L U y) ≫ α.hom).opensRange).ι ≫ (AlgebraicGeometry.Scheme.affineLineOver (AlgebraicGeometry.Spec (CommRingCat.of k)) ↘
        AlgebraicGeometry.Spec (CommRingCat.of k))
    rw [← hjα]
    simp only [Category.assoc]
    rw [hα]
    change _ = ((totalSpaceOpenFiberToTotalSpaceFiber L U y) ≫ α.hom).isoOpensRange.inv ≫ (totalSpaceOpenFiberToTotalSpaceFiber L U y) ≫ ((AlgebraicGeometry.Scheme.totalSpace L.toModules).hom.fiberι y ≫ (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom ≫ (C.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k)))
    rw [← Category.assoc (totalSpaceOpenFiberToTotalSpaceFiber L U y) ((AlgebraicGeometry.Scheme.totalSpace L.toModules).hom.fiberι y), hι'ι]
    simp only [Category.assoc]
  have hfo : ((((totalSpaceOpenFiberToTotalSpaceFiber L U y) ≫ α.hom).isoOpensRange.inv ≫ (U.ι ≫ (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).fiberι y)).IsOver (AlgebraicGeometry.Spec (CommRingCat.of k)) := ⟨hover⟩
  rw [hΦeq, ← Category.assoc, hθe, Category.assoc, Category.assoc, hchart ((totalSpaceOpenFiberToTotalSpaceFiber L U y) ≫ α.hom).opensRange hO,
    ← Iso.hom_inv_id_assoc ((totalSpaceOpenFiberToTotalSpaceFiber L U y) ≫ α.hom).isoOpensRange (((U.ι ≫ (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom)).fiberι y), Category.assoc]
  congr 1
  rw [projectivizationMorphism_pullback (((totalSpaceOpenFiberToTotalSpaceFiber L U y) ≫ α.hom).isoOpensRange.inv ≫ (U.ι ≫ (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).fiberι y) _ _ hU hpull]
  exact (projectivizationMorphism_congr_iso _ _ ((((AlgebraicGeometry.Scheme.Modules.pullbackComp (((totalSpaceOpenFiberToTotalSpaceFiber L U y) ≫ α.hom).isoOpensRange.inv ≫ (U.ι ≫ (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).fiberι y) U.ι).app ((AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj M.toModules)) ≪≫ τ) : (AlgebraicGeometry.Scheme.Modules.pullback (((totalSpaceOpenFiberToTotalSpaceFiber L U y) ≫ α.hom).isoOpensRange.inv ≫ (U.ι ≫ (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).fiberι y)).obj ((AlgebraicGeometry.Scheme.Modules.pullback U.ι).obj ((AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj M.toModules)) ≅ SheafOfModules.unit (((totalSpaceOpenFiberToTotalSpaceFiber L U y) ≫ α.hom).opensRange).toScheme.ringCatSheaf) _ hpull hO').trans
    (projectivizationMorphism_congr_sections _ (funext hsec') hO' hO)

end
