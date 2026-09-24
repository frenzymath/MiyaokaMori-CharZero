import MiyaokaMori.AlgebraicGeometry.Modules.TotalSpace.FiberPolynomialExtensionDegreeFiberSectionsPolynomialFrameCoordinateMonomialFrame
import MiyaokaMori.Paper.S3PositiveLine.Realization.FiberPolynomialExtensionDegreeFiberSectionsPolynomialFrameCoordinateMonomialRingEquiv

/-! # Monomials in the tautological section restricted to a fiber of `Tot(L)`

The geometric core of the polynomiality of the fiber sections of `Tot(L)`: on the fiber
`F = Tot(L)_y` of `p : Tot(L) → C` over a closed point `y`, there are a coordinate
`φ : k[t] ≃+* Γ(F, O_F)` (a ring isomorphism) and a trivialization `τ` of the restricted line bundle
`(p.fiberι y)^*(p^*M)` in which every monomial `c·ξ^q ∈ Γ(Tot(L), p^*M)` (`xiMonomial L M q c`,
`c ∈ Γ(C, M ⊗ L^{-q})`) restricts to a constant times `t^q`.

The coordinate is a *ring isomorphism* `k[t] ≃+* Γ(F, O_F)`, not an isomorphism of schemes
`F ≅ A¹_k`: `F` is affine (`totalSpace_fiber_isAffine`, base change of the affine morphism `p`), so the
two are equivalent, and the passage from `φ` to `α₀ : F ≅ A¹_k` with `α₀^* ∘ affineLinePolynomial = φ`
is done once and for all in `exists_iso_affineLine_of_ringEquiv`.

Source: the paper, proof of the polynomial realization theorem ("homogenizing in the fiber coordinate
gives homogeneous coordinates of a common degree at most `r_0`") and the expansion
`P = Σ_q c_q ξ^q` of equation (4.1).

The main statement `totalSpace_fiber_xiMonomial_exists_ringEquiv` is assembled from two lemmas stated
over an *arbitrary* point `y` and its residue field `κ(y)` (no `IsAlgClosed`, no closedness):
* `totalSpace_fiber_exists_ringEquiv_tautologicalSection`:
  the fiber is `A¹_{κ(y)}` *with coordinate `ξ`*: a ring isomorphism `φ₀ : κ(y)[t] ≃+* Γ(F, O_F)` sending
  constants to the constants `κ(y) → Γ(F, O_F)` of the structure map `F → Spec κ(y)`
  (`Scheme.Hom.fiberResidueConstants`), together with a trivialization `τ_L` of `(p.fiberι y)^*(p^*L)` with
  `φ₀(t) = τ_L(ξ|_F)`;
* `totalSpace_fiber_exists_trivializations_xiMonomial`:
  trivializations `τ_L`, `τ_M` (from local frames of `L`, `M` at `y`) in which
  `τ_M((c·ξ^q)|_F) = const(a) · τ_L(ξ|_F)^q` with `a = c(y) ∈ κ(y)`.
The two lemmas choose their own `τ_L`; the glue reconciles them: two trivializations
of the same line bundle differ by a unit `u ∈ Γ(F, O_F)^×`
(`AlgebraicGeometry.Scheme.Modules.exists_isUnit_app_top_eq_mul`); under `φ₀`, `u = φ₀(C r)` with `r ≠ 0`
because the units of `κ(y)[t]` are the nonzero constants (Mathlib `Polynomial.isUnit_iff`); rescaling the
variable `t ↦ r·t` (`Polynomial.algEquivOfCompEqX`) and transporting the coefficients along
`κ(y) ≅ k` (Mathlib `residueFieldIsoBase`, `Polynomial.mapEquiv`) gives the required `φ`.
All the geometry lives in the two lemmas, whose statements mention neither `k` nor `IsAlgClosed`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- **Monomials `c·ξ^q` restricted to a fiber of `Tot(L)` are constants times `t^q`.**

Setting: `L`, `M` line bundles on the smooth projective curve `C` over `k = k̄`, `p : Tot(L) → C`,
`y` a closed point of `C`, `F := p.fiber y` the scheme-theoretic fiber, `i := p.fiberι y : F → Tot(L)`.
Claim: there are a ring isomorphism `φ : k[t] ≃+* Γ(F, O_F)` and a trivialization
`τ : i^*(p^*M) ≅ O_F` such that for every `q` and every `c ∈ Γ(C, M ⊗ L^{-q})` there is a constant
`a ∈ k` with `τ (i^*(xiMonomial L M q c)) = φ (a·t^q)` (`Polynomial.C a * Polynomial.X ^ q`). Nothing
is claimed about `φ` being `k`-linear for the structure of `F` over `k`, nor about `a` depending
linearly on `c` (it does: `a = c(y)` in frames), because the user does not need either.

Proof:
1. `totalSpace_fiber_exists_trivializations_xiMonomial`: trivializations `τ_L`, `τ_M` and, for each
   `q`, `c`, a constant `a' ∈ κ(y)` with `τ_M(i^*(c·ξ^q)) = const(a') · τ_L(i^*ξ)^q`.
2. `totalSpace_fiber_exists_ringEquiv_tautologicalSection`: `φ₀ : κ(y)[t] ≃+* Γ(F, O_F)`, `τ_L'`
   with `φ₀(C a) = const a`, `φ₀(t) = τ_L'(i^*ξ)`.
3. `τ_L(s) = u · τ_L'(s)` for a unit `u` (`exists_isUnit_app_top_eq_mul`); `φ₀⁻¹(u)` is a unit of
   `κ(y)[t]`, hence a nonzero constant `C r` (`Polynomial.isUnit_iff`), so `u = φ₀(C r)`.
4. `κ(y) ≅ k`: Mathlib `residueFieldIsoBase (C ↘ Spec k) y hy` (`C → Spec k` is locally of finite type,
   `k` algebraically closed, `y` closed). Put `φ := φ₀ ∘ (t ↦ C r · t) ∘ (coefficients along k ≅ κ(y))`
   (`Polynomial.algEquivOfCompEqX (C r * X) (C r⁻¹ * X)`, `Polynomial.mapEquiv`), a ring isomorphism.
5. For `q`, `c`: with `a := e(a')`, `φ(C a * X^q) = φ₀(C a' * (C r * X)^q) = const(a') · (u · τ_L'(i^*ξ))^q
   = const(a') · τ_L(i^*ξ)^q = τ_M(i^*(c·ξ^q))`.
Edge cases: `q = 0` (`a·t^0 = a`); `c = 0` (`a = 0` from step 1); `hy` is used only in step 4
(`κ(y) = k`); for a non-closed `y` the fiber is `A¹_{κ(y)}` with `Γ(F, O) = κ(y)[t] ≇ k[t]` as rings (their
unit groups `κ(y)^*`, `k^*` differ: `k` is algebraically closed, `κ(y)` is a proper extension), so the
statement is false as written. -/
theorem totalSpace_fiber_xiMonomial_exists_ringEquiv {k : Type u} [Field k] [IsAlgClosed k]
    {C : SmoothProjectiveCurve k} (L M : LineBundle C.toVariety)
    (y : C.toScheme) (hy : IsClosed ({y} : Set C.toScheme)) :
    ∃ (φ : Polynomial k ≃+* Γ((AlgebraicGeometry.Scheme.totalSpace L.toModules).hom.fiber y, ⊤))
      (τ : (AlgebraicGeometry.Scheme.Modules.pullback
          ((AlgebraicGeometry.Scheme.totalSpace L.toModules).hom.fiberι y)).obj
            ((AlgebraicGeometry.Scheme.Modules.pullback
              (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj M.toModules) ≅
          SheafOfModules.unit ((AlgebraicGeometry.Scheme.totalSpace L.toModules).hom.fiber y).ringCatSheaf),
      ∀ (q : ℕ) (c : ((((M.zpow 1).tensor (L.zpow (-(q : ℤ)))).toModules.val.obj (Opposite.op ⊤)) : Type u)),
        ∃ a : k, τ.hom.app ⊤ (sectionPullbackAlong
            ((AlgebraicGeometry.Scheme.totalSpace L.toModules).hom.fiberι y) (xiMonomial L M q c)) =
          φ (Polynomial.C a * Polynomial.X ^ q) := by
  obtain ⟨τL, τM, hM⟩ := totalSpace_fiber_exists_trivializations_xiMonomial L M y
  obtain ⟨φ₀, τL', hC, hX⟩ := totalSpace_fiber_exists_ringEquiv_tautologicalSection L y
  obtain ⟨u, hu, hτ⟩ := AlgebraicGeometry.Scheme.Modules.exists_isUnit_app_top_eq_mul τL τL'
  obtain ⟨r, hr, hru⟩ := Polynomial.isUnit_iff.mp (hu.map φ₀.symm)
  have hφr : φ₀ (Polynomial.C r) = u := by rw [hru, RingEquiv.apply_symm_apply]
  have hr0 : r ≠ 0 := hr.ne_zero
  let e : (C.toScheme.residueField y : Type u) ≃+* k :=
    (AlgebraicGeometry.residueFieldIsoBase (C.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) y
      hy).commRingCatIsoToRingEquiv
  have hcomp : ∀ s : (C.toScheme.residueField y : Type u), s ≠ 0 →
      (Polynomial.C s * Polynomial.X).comp (Polynomial.C s⁻¹ * Polynomial.X) = Polynomial.X := by
    intro s hs
    rw [Polynomial.mul_comp, Polynomial.C_comp, Polynomial.X_comp, ← mul_assoc, ← Polynomial.C_mul,
      mul_inv_cancel₀ hs, Polynomial.C_1, one_mul]
  let σ : Polynomial (C.toScheme.residueField y : Type u) ≃ₐ[(C.toScheme.residueField y : Type u)]
      Polynomial (C.toScheme.residueField y : Type u) :=
    Polynomial.algEquivOfCompEqX (Polynomial.C r * Polynomial.X) (Polynomial.C r⁻¹ * Polynomial.X)
      (hcomp r hr0) (by simpa only [inv_inv] using hcomp r⁻¹ (inv_ne_zero hr0))
  refine ⟨((Polynomial.mapEquiv e.symm).trans σ.toRingEquiv).trans φ₀, τM, fun q c => ?_⟩
  obtain ⟨a, ha⟩ := hM q c
  refine ⟨e a, ?_⟩
  have h1 : Polynomial.mapEquiv e.symm (Polynomial.C (e a) * Polynomial.X ^ q) =
      Polynomial.C a * Polynomial.X ^ q := by
    rw [Polynomial.mapEquiv_apply, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow,
      Polynomial.map_X]
    exact congrArg (fun z => Polynomial.C z * Polynomial.X ^ q) (e.symm_apply_apply a)
  have h2 : σ (Polynomial.C a * Polynomial.X ^ q) =
      Polynomial.C a * (Polynomial.C r * Polynomial.X) ^ q := by
    simp only [σ, Polynomial.algEquivOfCompEqX_apply, map_mul, map_pow, Polynomial.aeval_C,
      Polynomial.aeval_X, Polynomial.algebraMap_eq]
  change AlgebraicGeometry.Scheme.Modules.unitSectionAsFunction (τM.hom.app ⊤ (sectionPullbackAlong
    ((AlgebraicGeometry.Scheme.totalSpace L.toModules).hom.fiberι y) (xiMonomial L M q c))) = _
  refine ha.trans ?_
  refine (congrArg (fun z : Γ((AlgebraicGeometry.Scheme.totalSpace L.toModules).hom.fiber y, ⊤) =>
      (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom.fiberResidueConstants y a * z ^ q)
    (hτ (sectionPullbackAlong ((AlgebraicGeometry.Scheme.totalSpace L.toModules).hom.fiberι y)
      (tautologicalSection L)))).trans ?_
  rw [RingEquiv.trans_apply, RingEquiv.trans_apply, h1, AlgEquiv.coe_ringEquiv, h2, map_mul, map_pow, map_mul, hC, hφr, hX]

end
