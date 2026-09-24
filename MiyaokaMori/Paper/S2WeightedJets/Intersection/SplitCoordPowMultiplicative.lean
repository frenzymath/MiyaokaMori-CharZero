import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.SectionTensor
import MiyaokaMori.Paper.S2WeightedJets.Intersection.SplitWeightedCoordinate
import MiyaokaMori.Paper.S2WeightedJets.Intersection.SplitWeightedProjectivization
import MiyaokaMori.AlgebraicGeometry.Proj.Twist.TwistMultiplication
import MiyaokaMori.AlgebraicGeometry.Proj.Twist.TwistPullbackPow
import MiyaokaMori.Paper.S2WeightedJets.Intersection.SplitWeightedAlgebraSufficientlyDivisible
import MiyaokaMori.AlgebraicGeometry.Proj.Twist.TwistPowerIso

/-! # Multiplicativity of the coordinate power sections

The coordinate power sections `x_{i,q}^{m/q} := splitTwistMul (x_{i,q}^{⊗ m/q})` are **multiplicative** in the
exponent: `x^{m/q} ⊗ x^{m'/q}` becomes `x^{(m+m')/q}` under an isomorphism `L_m ⊗ L_{m'} ≅ L_{m+m'}`
(`L_m := O(m) ⊗ π^*Q_i^{⊗ m/q}`, with `m`, `m'` divisible by all weights).

This is the core of the algebraic route to "the nonvanishing locus of the coordinate power does not depend on `m`":
together with the invariance of nonvanishing loci under isomorphisms (`NonvanishingLocusIsoInvariant`) and "the
nonvanishing locus of a tensor of line bundle sections is the intersection", induction on `r` gives
`X_{x^{m₀ r/q}} = X_{x^{m₀/q}}`.

Source: Stacks 01MO (the multiplication `O(a) ⊗ O(b) → O(a+b)` with its associativity and unit laws), 01MS (it is an
isomorphism in the invertible range); proof of Proposition 2.4 of the paper (raising the coordinate to
the `m/q`-th power does not change its zero set).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- Variable-level bridge : `f ≫ eqToHom h` and `g ≫ eqToHom h'` are heterogeneously equal
when the objects agree (`hA`, `hB`, `hB'`; possibly spelled differently) and `f`, `g` are heterogeneously equal.
Every object of each side is its own variable, so at the use site both `eqToHom`s keep exactly the spelling of the goal
and the kernel never reduces an `eqToHom` proof term. -/
theorem CategoryTheory.heq_comp_eqToHom_of_heq {C : Type*} [Category C] {A₁ B₁ B'₁ A₂ B₂ B'₂ : C}
    (f : A₁ ⟶ B₁) (g : A₂ ⟶ B₂) (h : B₁ = B'₁) (h' : B₂ = B'₂)
    (hA : A₁ = A₂) (hB : B₁ = B₂) (hB' : B'₁ = B'₂) (hfg : HEq f g) :
    HEq (f ≫ eqToHom h) (g ≫ eqToHom h') := by
  subst hA hB hB'
  obtain rfl := eq_of_heq hfg
  rfl

/-- The index transport `q(m/q) = m` on `L_{m/q}` (the `eqToHom` inside `splitTwistMul`), with the left side spelled
through `relativeProj` (as in `twistPullbackPow`) and the right side as in the target statement. -/
theorem splitTwistMul_index_eq {K : Type u} [Field K] {C : SmoothProjectiveCurve K}
    {n : ℕ} {E : AlgebraicGeometry.VectorBundle C.toVariety} (F : SubbundleFiltration E (n + 1)) (kk : ℕ)
    (i : Fin (n + 1)) (q m : ℕ) (hqm : q ∣ m) :
    AlgebraicGeometry.Scheme.Modules.tensor
        (AlgebraicGeometry.Scheme.relativeProj.twist (splitWeightedAlgebraOf F kk) ((q * (m / q) : ℕ) : ℤ))
        ((AlgebraicGeometry.Scheme.Modules.pullback
          (AlgebraicGeometry.Scheme.relativeProj (splitWeightedAlgebraOf F kk)).hom).obj
          (AlgebraicGeometry.Scheme.Modules.tensorPow (F.lineQuotient i).toModules (m / q))) =
      AlgebraicGeometry.Scheme.Modules.tensor
        (AlgebraicGeometry.Scheme.relativeProj.twist (splitWeightedAlgebraOf F kk) (m : ℤ))
        ((AlgebraicGeometry.Scheme.Modules.pullback
          (AlgebraicGeometry.Scheme.relativeProj (splitWeightedAlgebraOf F kk)).hom).obj
          (AlgebraicGeometry.Scheme.Modules.tensorPow (F.lineQuotient i).toModules (m / q))) := by
  rw [Nat.mul_div_cancel' hqm]

/-- **`splitTwistMul` is `twistPullbackPow` followed by the index transport.**

True by definition: the body of `splitTwistMul` (`TwistMultiplication`) is the `Nat.rec` term
`twistPullbackPow (splitWeightedAlgebraOf F kk) q (F.lineQuotient i).toModules` (the same term with `S`, `Q`, `π`
instantiated; `twistPullbackPow_rec_apply`) composed with `eqToHom (q(m/q) = m)` and applied to `x`; any two proofs of
the index equation are equal (proof irrelevance).

Why the proof is not `rfl`: at the *section* level (`splitTwistMul … x = …`) every `rfl`/`delta`/`unfold` makes the
kernel exceed the time budget, while the same `delta` + `rfl` at the *function* level (`splitTwistMul … = fun y => …`)
is instant. Reason: comparing `splitTwistMul … x` with any other term, the kernel's lazy delta unfolds the `abbrev`
heads (`DFunLike.coe`, `AddHom.toFun`, `Function.comp`, `ModuleCat.Hom.hom`) *before* the regular `splitTwistMul`;
reducing these projections `whnf`s the section map of `eqToHom P` down to the proof `P`, i.e. through the proof of
`Nat.mul_div_cancel'` (K-reduction of `Eq.rec` fails because `q * (m / q) ≡ m` is not decided by `whnf`). At the
function level the other side is a lambda (no delta head), so `splitTwistMul` is unfolded first and the two sides are
syntactically identical.

Proof: (1) the function-level equation `hf` by `delta splitTwistMul` + `funext`; (2) pass to the morphism level with
`congrArg` (kernel: beta, then structural); (3) split `f ≫ eqToHom h = g ≫ eqToHom h'` into `HEq f g` + proof
irrelevance with the bridge `heq_comp_eqToHom_of_heq`, so the two `eqToHom`s (with differently spelled objects) are
never compared under an `abbrev` head; (4) the goal `HEq (Nat.rec …) (twistPullbackPow …)` differs only in the
spelling `splitWeightedProjectivization F kk` vs `relativeProj (splitWeightedAlgebraOf F kk)`; the elaborator's
`isDefEq` times out on it, so `delta splitWeightedProjectivization` first, then the `rfl` lemma
`twistPullbackPow_rec_apply`; (5) `congrFun hf x`. No hypothesis beyond `q ∣ m`; `m = 0` allowed. -/
theorem splitTwistMul_eq_twistPullbackPow {K : Type u} [Field K] {C : SmoothProjectiveCurve K}
    {n : ℕ} {E : AlgebraicGeometry.VectorBundle C.toVariety} (F : SubbundleFiltration E (n + 1)) (kk : ℕ)
    (i : Fin (n + 1)) (q m : ℕ) (hqm : q ∣ m)
    (x : ((AlgebraicGeometry.Scheme.Modules.tensorPow
        (AlgebraicGeometry.Scheme.Modules.tensor
          (AlgebraicGeometry.Scheme.relativeProj.twist (splitWeightedAlgebraOf F kk) (q : ℤ))
          ((AlgebraicGeometry.Scheme.Modules.pullback
            (AlgebraicGeometry.Scheme.relativeProj (splitWeightedAlgebraOf F kk)).hom).obj
            (F.lineQuotient i).toModules)) (m / q)).val.obj (Opposite.op ⊤) : Type u)) :
    splitTwistMul F kk i q m hqm x =
      ((AlgebraicGeometry.Scheme.relativeProj.twistPullbackPow (splitWeightedAlgebraOf F kk) q
          (F.lineQuotient i).toModules (m / q) ≫
        CategoryTheory.eqToHom (splitTwistMul_index_eq F kk i q m hqm)).val.app (Opposite.op ⊤)).hom x := by
  have hf : splitTwistMul F kk i q m hqm = fun y =>
      ((AlgebraicGeometry.Scheme.relativeProj.twistPullbackPow (splitWeightedAlgebraOf F kk) q
          (F.lineQuotient i).toModules (m / q) ≫
        CategoryTheory.eqToHom (splitTwistMul_index_eq F kk i q m hqm)).val.app (Opposite.op ⊤)).hom y := by
    delta splitTwistMul
    funext y
    refine congrArg
      (fun φ : ((_ : (AlgebraicGeometry.Scheme.relativeProj (splitWeightedAlgebraOf F kk)).left.Modules) ⟶ _) =>
        (φ.val.app (Opposite.op ⊤)).hom y) ?_
    refine eq_of_heq (CategoryTheory.heq_comp_eqToHom_of_heq _ _ _ _ rfl rfl rfl ?_)
    delta splitWeightedProjectivization
    exact heq_of_eq (AlgebraicGeometry.Scheme.relativeProj.twistPullbackPow_rec_apply _ _ _ _)
  exact congrFun hf x

/-- **Multiplicativity of the coordinate power sections in the exponent (existence of an isomorphism).** Let
`m, m' > 0` both be divisible by all weights `1, …, kk`, `L_m := O(m) ⊗ π^*Q_i^{⊗ m/q}` and
`x^{m/q} := splitTwistMul (x_{i,q}^{⊗ m/q}) ∈ Γ(L_m)`. Then there is an isomorphism of module sheaves
`Φ : L_m ⊗ L_{m'} ≅ L_{m+m'}` with `Φ(x^{m/q} ⊗ x^{m'/q}) = x^{(m+m')/q}`.

Proof sketch (`S := splitWeightedAlgebraOf F kk`, `T a := O(a)`, `Q := Q_i`, `e := m/q`, `e' := m'/q`,
`τ := Modules.tensorIsoTensorObj`; the body of `splitTwistMul` is the recursion
`Ψ_e : (T q ⊗ π^*Q)^{⊗e} ⟶ T(qe) ⊗ π^*Q^{⊗e}` in `e`, followed by an `eqToHom` transporting the index `q(m/q) = m`):
1. Construction of `Φ`: reorder by the symmetric monoidal structure (`tensorμ`) to
   `(T m ⊗ T m') ⊗ (π^*Q^{⊗e} ⊗ π^*Q^{⊗e'})`, apply `twistMul S m m'` (Stacks 01MO) on the first factor and
   `(pullbackTensorIso π _ _).inv ≫ π^*(tensorPowAddIso Q e e')` (Stacks 01CD) on the second, then transport
   `e + e' = (m+m')/q` (`Nat.add_div_of_dvd_right`) by `eqToHom`.
2. `Φ` is an isomorphism: all pieces are isomorphisms, and `twistMul S m m'` is one because `m` is sufficiently
   divisible (`splitWeightedAlgebra_sufficientlyDivisible_of_dvd`, `twistMul_isIso_of_dvd`; the relative version of
   Stacks 01MS).
3. `Φ` sends `x^{m/q} ⊗ x^{m'/q}` to `x^{(m+m')/q}`: the blockwise multiplicativity
   `Ψ_{e+e'}(x^{⊗(e+e')}) = μ_{e,e'}(Ψ_e(x^{⊗e}) ⊗ Ψ_{e'}(x^{⊗e'}))` by induction on `e'`, using the unit law and the
   associativity of `twistMul` (Stacks 01MO) together with the recursion of `tensorPowAddIso`.
4. Evaluate step 3 at `e = m/q`, `e' = m'/q` and transport the indices by `eqToHom`.
The route is implemented for a general `S`, `Q` in `CoordinatePowerNonzeroLocus_SplitTwistMulAdd_TwistPullbackPow`:
`Ψ := twistPullbackPow S q Q`, `μ := twistPullbackPowMul`, the blockwise multiplicativity `twistPullbackPow_add`, and
`twistPullbackPow_mul_exists_iso` / `twistPullbackPow_mul_exists_iso_transport`. This theorem is the bridge
`splitTwistMul_eq_twistPullbackPow` rewritten three times, followed by the transport form
(`(m+m')/q = m/q + m'/q` by `Nat.add_div_of_dvd_right`).
Edge cases: `m, m' > 0` guarantee `e, e' ≥ 1`; for `kk = 0` the hypothesis `hq` cannot be satisfied. -/
theorem splitTwistMul_add_exists_iso {K : Type u} [Field K] {C : SmoothProjectiveCurve K} {n kk : ℕ}
    {E : AlgebraicGeometry.VectorBundle C.toVariety} (F : SubbundleFiltration E (n + 1))
    (i : Fin (n + 1)) (q : ℕ) (hq : q ∈ Finset.Icc 1 kk) (m m' : ℕ) (hm : 0 < m) (hm' : 0 < m')
    (hdiv : ∀ q ∈ Finset.Icc 1 kk, q ∣ m) (hdiv' : ∀ q ∈ Finset.Icc 1 kk, q ∣ m') :
    ∃ Φ : AlgebraicGeometry.Scheme.Modules.tensor
        ((AlgebraicGeometry.Scheme.relativeProj.twist (splitWeightedAlgebraOf F kk) (m : ℤ)).tensor
          ((AlgebraicGeometry.Scheme.Modules.pullback (splitWeightedProjectivization F kk).hom).obj
            (AlgebraicGeometry.Scheme.Modules.tensorPow (F.lineQuotient i).toModules (m / q))))
        ((AlgebraicGeometry.Scheme.relativeProj.twist (splitWeightedAlgebraOf F kk) (m' : ℤ)).tensor
          ((AlgebraicGeometry.Scheme.Modules.pullback (splitWeightedProjectivization F kk).hom).obj
            (AlgebraicGeometry.Scheme.Modules.tensorPow (F.lineQuotient i).toModules (m' / q)))) ≅
      (AlgebraicGeometry.Scheme.relativeProj.twist (splitWeightedAlgebraOf F kk) ((m + m' : ℕ) : ℤ)).tensor
        ((AlgebraicGeometry.Scheme.Modules.pullback (splitWeightedProjectivization F kk).hom).obj
          (AlgebraicGeometry.Scheme.Modules.tensorPow (F.lineQuotient i).toModules ((m + m') / q))),
      Φ.hom.app ⊤ (sectionTensor
        (splitTwistMul F kk i q m (hdiv q hq)
          (AlgebraicGeometry.Scheme.Modules.tensorPowSection (splitWeightedCoord F i q hq) (m / q)))
        (splitTwistMul F kk i q m' (hdiv' q hq)
          (AlgebraicGeometry.Scheme.Modules.tensorPowSection (splitWeightedCoord F i q hq) (m' / q)))) =
      splitTwistMul F kk i q (m + m') (dvd_add (hdiv q hq) (hdiv' q hq))
        (AlgebraicGeometry.Scheme.Modules.tensorPowSection (splitWeightedCoord F i q hq) ((m + m') / q)) := by
  have hd : m / q + m' / q = (m + m') / q := (Nat.add_div_of_dvd_right (hdiv q hq)).symm
  have : CategoryTheory.IsIso (AlgebraicGeometry.Scheme.relativeProj.twistMul (splitWeightedAlgebraOf F kk)
      ((q * (m / q) : ℕ) : ℤ) ((q * (m' / q) : ℕ) : ℤ)) :=
    AlgebraicGeometry.Scheme.relativeProj.twistMul_isIso_of_dvd (splitWeightedAlgebraOf F kk) m
      (splitWeightedAlgebra_sufficientlyDivisible_of_dvd F kk m hm hdiv) _ _
      (by rw [Nat.mul_div_cancel' (hdiv q hq)])
  delta splitWeightedProjectivization
  rw [splitTwistMul_eq_twistPullbackPow F kk i q m (hdiv q hq),
    splitTwistMul_eq_twistPullbackPow F kk i q m' (hdiv' q hq),
    splitTwistMul_eq_twistPullbackPow F kk i q (m + m') (dvd_add (hdiv q hq) (hdiv' q hq))]
  exact AlgebraicGeometry.Scheme.relativeProj.twistPullbackPow_mul_exists_iso_transport
    (splitWeightedAlgebraOf F kk) q (F.lineQuotient i).toModules (m / q) (m' / q) ((m + m') / q) hd _ _ _
    (splitWeightedCoord F i q hq)

end
