import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveBundle.FiberPolynomialExtensionDegreeFiberSectionsPolynomialCoordinateChange
import MiyaokaMori.AlgebraicGeometry.Modules.TotalSpace.FiberPolynomialExtensionDegreeFiberSectionsPolynomialFrameCoordinate
import MiyaokaMori.AlgebraicGeometry.Modules.TotalSpaceCanonicallyOver
import MiyaokaMori.AlgebraicGeometry.Morphisms.AffineLineOverCanonicallyOver

/-! # Sections of bounded ξ-degree restrict to polynomials on the fibres

A section of `p^*M` on `Tot(L)` of ξ-degree `≤ r₀` restricts to the fiber `Tot(L)_y ≅ A¹_k` as a
polynomial of degree `≤ r₀` (in any `k`-coordinate on the fiber), after trivializing the restricted
line bundle. (In the paper: "homogenizing in the fiber coordinate gives homogeneous coordinates of a
common degree at most `r_0`".)

`totalSpace_fiber_sections_polynomial` is assembled from `totalSpace_fiber_sections_polynomial_exists_coordinate`
(*some* coordinate `α₀` on the fiber in which the restricted sections are polynomials of degree `≤ r₀`) and
the algebra of `FiberPolynomialExtensionDegreeFiberSectionsPolynomialCoordinateChange` (`fiberCoordinateChange α₀ α`
is the ring automorphism of `k[t]` comparing two coordinates; ring automorphisms of `k[t]` preserve
the degree, `Polynomial.degree_ringEquiv_apply`). The hypothesis `hα` (that `α` is a `k`-morphism) is
therefore not needed for the proof — every ring automorphism of `k[t]`, `k`-linear or not, preserves
the degree — but it is kept because the statement is used as is by `fiber_restriction_extends_to_p1`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

set_option linter.unusedVariables false in
/-- **Sections of bounded ξ-degree restrict to polynomials on the fibres.**

Setting: `L`, `M` line bundles on the smooth projective curve `C` over `k = k̄`, `p : Tot(L) → C`,
`P ℓ ∈ Γ(Tot(L), p^*M)` (`ℓ = 0, …, N`) with ξ-degree `≤ r₀` (`hP`), `y` a closed point of `C`, and
`α : Tot(L)_y ≅ A¹_k` any isomorphism over `k` (`hα`; such an `α` exists by the description of the fibres
of the ruled surface). Claim: there are polynomials `Q ℓ ∈ k[t]` of
degree `≤ r₀` and a trivialization `τ : (p.fiberι y)^*(p^*M) ≅ O_{Tot(L)_y}` such that the restriction
of `P ℓ` to the fiber, read through `τ`, is the function `α^*(Q ℓ)` (`affineLinePolynomial k (Q ℓ)`
pulled back along `α.hom`).

Proof (self-contained):
1. Trivialization. `(p.fiberι y)^*(p^*M) ≅ (p.fiberι y ≫ p)^*M` (`Modules.pullbackComp`) and
   `p.fiberι y ≫ p = fiberToSpecResidueField ≫ C.fromSpecResidueField y` (`Scheme.Hom.fiber_fac`);
   `(fromSpecResidueField y)^*M` is a line bundle on the one-point scheme `Spec κ(y)`, hence trivial
   (locally free of rank 1 on a point is globally free). So some `τ` exists; it is unique up to a unit
   of `Γ(Tot(L)_y, O) ≅ k[t]`, i.e. up to a nonzero constant (`Polynomial.isUnit_iff`).
2. Frame coordinates. Choose an affine open `V ∋ y` and frames `ε` of `L|_V`, `η` of `M|_V`
   (`LineBundle.Frame`). By `totLine_sections_over_frame`,
   `Γ(p⁻¹V, O) ≅ Γ(V, O)[t]` as `Γ(V, O)`-algebras, `ξ = t·ε`, and `p⁻¹V = Spec Γ(V, O)[t]` (`p` is
   affine, `totLine_isAffineHom`). Through `η`, `Γ(p⁻¹V, p^*M) ≅ Γ(p⁻¹V, O) ≅ Γ(V, O)[t]` and
   `P ℓ|_{p⁻¹V} ↦ Σ_q c_{ℓ,q} t^q`, where `c_{ℓ,q} ∈ Γ(V, O)` is the coefficient
   `xiCoefficient L M (P ℓ) q ∈ Γ(C, M ⊗ L^{-q})` written in the frames (`eq_sum_xiMonomial`).
   By `hP`, `c_{ℓ,q} = 0` for `q > r₀` (`xiDegree_lt_iff`, `xiCoefficient_eq_zero_of_xiDegree_lt`).
3. The fiber. `Tot(L)_y = Spec (Γ(V, O)[t] ⊗_{Γ(V, O)} κ(y)) = Spec κ(y)[t]` (fiber of an affine
   morphism over a point of an affine open: Mathlib `pullbackSpecIso`,
   `Spec.fiberToSpecResidueFieldIso`) and `κ(y) = k` (Mathlib `residueFieldIsoBase`, since `C` is
   locally of finite type over the algebraically closed `k` and `y` is closed). The restriction of
   `P ℓ` to the fiber, trivialized by `η(y)`, is `Σ_{q ≤ r₀} c_{ℓ,q}(y) t^q ∈ k[t]`: degree `≤ r₀` in
   the frame coordinate `t`.
4. Change of coordinate. `α` gives a second ring isomorphism `Γ(Tot(L)_y, O) ≅ Γ(A¹_k, O) = k[t']`
   (`fiberCoordinate α`; `Γ(A¹_k) = k[X]` by `AffineSpace.SpecIso` and `ΓSpecIso`,
   `affineLinePolynomialRingHom_bijective`). The two coordinates differ by a ring automorphism `σ` of
   `k[t]` (`fiberCoordinateChange α₀ α`), and every ring automorphism of `k[t]` preserves the degree:
   constants go to constants (the units), so `σ f = (f.map φ).comp (σ t)`, and
   `natDegree (σ t) · natDegree (σ⁻¹ t) = natDegree t = 1` (`Polynomial.natDegree_comp`), so
   `natDegree (σ t) = 1` (`Polynomial.degree_ringEquiv_apply`). So `Q ℓ := σ (Q₀ ℓ)` has degree `≤ r₀`
   and `α^*(Q ℓ) = α₀^*(Q₀ ℓ) = τ (P ℓ|_y)` (`fiberCoordinate_fiberCoordinateChange`).

As formalized: steps 1–3 are `totalSpace_fiber_sections_polynomial_exists_coordinate`, which produces
`α₀`, `Q₀`, `τ`; step 4 is `FiberPolynomialExtensionDegreeFiberSectionsPolynomialCoordinateChange`.
Edge cases: `r₀ = 0` (all `Q ℓ` constant); `P ℓ = 0` (`Q ℓ = 0`, degree `⊥ ≤ r₀`). -/
theorem totalSpace_fiber_sections_polynomial {k : Type u} [Field k] [IsAlgClosed k]
    {C : SmoothProjectiveCurve k} (L M : LineBundle C.toVariety) {N r₀ : ℕ}
    (P : Fin (N + 1) →
      (((AlgebraicGeometry.Scheme.Modules.pullback
        (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj M.toModules).val.obj
          (Opposite.op ⊤) : Type u))
    (hP : ∀ ℓ, xiDegree L M (P ℓ) ≤ (r₀ : WithBot ℕ))
    (y : C.toScheme) (hy : IsClosed ({y} : Set C.toScheme))
    (α : (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom.fiber y ≅
      AlgebraicGeometry.Scheme.affineLineOver (AlgebraicGeometry.Spec (CommRingCat.of k)))
    (hα : α.hom ≫ (AlgebraicGeometry.Scheme.affineLineOver (AlgebraicGeometry.Spec (CommRingCat.of k)) ↘
          AlgebraicGeometry.Spec (CommRingCat.of k)) =
        ((AlgebraicGeometry.Scheme.totalSpace L.toModules).hom.fiber y ↘
          AlgebraicGeometry.Spec (CommRingCat.of k))) :
    ∃ Q : Fin (N + 1) → Polynomial k, (∀ ℓ, (Q ℓ).degree ≤ (r₀ : WithBot ℕ)) ∧
      ∃ τ : (AlgebraicGeometry.Scheme.Modules.pullback
          ((AlgebraicGeometry.Scheme.totalSpace L.toModules).hom.fiberι y)).obj
            ((AlgebraicGeometry.Scheme.Modules.pullback
              (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj M.toModules) ≅
          SheafOfModules.unit ((AlgebraicGeometry.Scheme.totalSpace L.toModules).hom.fiber y).ringCatSheaf,
        ∀ ℓ, τ.hom.app ⊤ (sectionPullbackAlong
            ((AlgebraicGeometry.Scheme.totalSpace L.toModules).hom.fiberι y) (P ℓ)) =
          α.hom.appTop.hom (affineLinePolynomial k (Q ℓ)) := by
  obtain ⟨α₀, Q₀, hQ₀, τ, hτ⟩ :=
    totalSpace_fiber_sections_polynomial_exists_coordinate L M P hP y hy
  refine ⟨fun ℓ => fiberCoordinateChange α₀ α (Q₀ ℓ), fun ℓ => ?_, τ, fun ℓ => ?_⟩
  · rw [degree_fiberCoordinateChange]
    exact hQ₀ ℓ
  · rw [hτ ℓ, fiberCoordinate_fiberCoordinateChange]

end
