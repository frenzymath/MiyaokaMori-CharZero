import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Cohomology.Basic.SheafCohomologyShift
import MiyaokaMori.AlgebraicGeometry.Cohomology.ExtendByZero.Stacks01f6RestrictShortExact

/-! # Dimension-shifting comparison of two cohomology theories

**Abstract dimension-shifting comparison of two cohomology theories on `X.Modules`**
(the inductive skeleton of Hartshorne III.4.5 (p. 222) / of Stacks 01F4(1) "prove it directly
without the spectral sequence"; it is the argument of `PushforwardCohomologyLerayDegeneration.lean`,
made independent of the two functors involved).

Setting: `T : X.Modules ⥤ X₀.Modules`, `T' : X.Modules ⥤ Y₀.Modules` two functors preserving zero
morphisms, `P` a class of `O_X`-modules. Hypotheses:
* `h0`: for `M ∈ P`, `Γ(X₀, T M) ≃+ Γ(Y₀, T' M)`;
* `hS`: every `M ∈ P` sits in a short exact sequence `S : 0 → M → I → R → 0` with `R ∈ P`, whose
  images `T S`, `T' S` are short exact, whose middle terms are acyclic (`H^{k+1}(X₀, T I) = 0`,
  `H^{k+1}(Y₀, T' I) = 0`), and whose two cokernel groups
  `Γ(T R) ⧸ im Γ(T I)` and `Γ(T' R) ⧸ im Γ(T' I)` are isomorphic.
Conclusion: `H^p(X₀, T M) ≃+ H^p(Y₀, T' M)` for all `p` and all `M ∈ P`.

Proof (induction on `p`, for all `M` at once):
* `p = 0`: `H^0 = Γ` on both sides (Mathlib `Sheaf.H.equiv₀`) and `h0`.
* `p = 1`: by the long exact sequence, `H^1(X₀, T M) ≅ Γ(T R) ⧸ im Γ(T I)` because `H^1(X₀, T I) = 0`
  (`sheafCohomology.one_equiv_quotient`), likewise on `Y₀`; the two quotients are isomorphic by `hS`.
* `p = j + 2`: the connecting maps `H^{j+1}(X₀, T R) → H^{j+2}(X₀, T M)` and
  `H^{j+1}(Y₀, T' R) → H^{j+2}(Y₀, T' M)` are bijective since the middle terms are acyclic in degrees
  `j+1`, `j+2` (`sheafCohomology.δ_bijective`); conclude with the induction hypothesis for `R ∈ P`.

Only additive isomorphisms are produced (no naturality is asserted).

Source: Hartshorne III.4.5 (proof, dimension shifting); Stacks 01F4 (remark after the statement);
Grothendieck's uniqueness of universal δ-functors (Hartshorne III.1.3A) is the general principle.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

variable {X X₀ Y₀ : AlgebraicGeometry.Scheme.{u}}
  (T : X.Modules ⥤ X₀.Modules) (T' : X.Modules ⥤ Y₀.Modules)
  [T.PreservesZeroMorphisms] [T'.PreservesZeroMorphisms]

/-- The `p = 1` step: `H^1(X₀, T M) ≃+ H^1(Y₀, T' M)` from the two cokernel descriptions. -/
theorem sheafCohomology_addEquiv_one_of_quotient_addEquiv (S : ShortComplex X.Modules)
    (hT : (S.map T).ShortExact) (hT' : (S.map T').ShortExact)
    [Subsingleton (AlgebraicGeometry.sheafCohomology X₀ (S.map T).X₂ 1)]
    [Subsingleton (AlgebraicGeometry.sheafCohomology Y₀ (S.map T').X₂ 1)]
    (hq : Nonempty ((Γ((S.map T).X₃, ⊤) ⧸ AddMonoidHom.range ((S.map T).g.app ⊤).hom) ≃+
      (Γ((S.map T').X₃, ⊤) ⧸ AddMonoidHom.range ((S.map T').g.app ⊤).hom))) :
    Nonempty (CategoryTheory.Sheaf.H (S.map T).X₁.toAddCommGrpSheaf 1 ≃+
      CategoryTheory.Sheaf.H (S.map T').X₁.toAddCommGrpSheaf 1) := by
  obtain ⟨dX⟩ := AlgebraicGeometry.sheafCohomology.one_equiv_quotient hT
  obtain ⟨dY⟩ := AlgebraicGeometry.sheafCohomology.one_equiv_quotient hT'
  obtain ⟨qX⟩ := quotient_range_addEquiv_appTop (S.map T)
  obtain ⟨qY⟩ := quotient_range_addEquiv_appTop (S.map T')
  obtain ⟨e⟩ := hq
  exact ⟨dX.toAddEquiv.trans (qX.trans (e.trans (qY.symm.trans dY.toAddEquiv.symm)))⟩

/-- The shift step: `H^{j+2}(X₀, T M) ≃+ H^{j+2}(Y₀, T' M)` from
`H^{j+1}(X₀, T R) ≃+ H^{j+1}(Y₀, T' R)` when the middle terms are acyclic in degrees `j+1`, `j+2`. -/
theorem sheafCohomology_addEquiv_succ_of_addEquiv (S : ShortComplex X.Modules)
    (hT : (S.map T).ShortExact) (hT' : (S.map T').ShortExact) (j : ℕ)
    [Subsingleton (AlgebraicGeometry.sheafCohomology X₀ (S.map T).X₂ (j + 1))]
    [Subsingleton (AlgebraicGeometry.sheafCohomology X₀ (S.map T).X₂ (j + 1 + 1))]
    [Subsingleton (AlgebraicGeometry.sheafCohomology Y₀ (S.map T').X₂ (j + 1))]
    [Subsingleton (AlgebraicGeometry.sheafCohomology Y₀ (S.map T').X₂ (j + 1 + 1))]
    (r : CategoryTheory.Sheaf.H (S.map T).X₃.toAddCommGrpSheaf (j + 1) ≃+
      CategoryTheory.Sheaf.H (S.map T').X₃.toAddCommGrpSheaf (j + 1)) :
    Nonempty (CategoryTheory.Sheaf.H (S.map T).X₁.toAddCommGrpSheaf (j + 1 + 1) ≃+
      CategoryTheory.Sheaf.H (S.map T').X₁.toAddCommGrpSheaf (j + 1 + 1)) := by
  -- `LinearEquiv.ofBijective` (not `AddEquiv.ofBijective … .toAddMonoidHom`): see the remark in
  -- `PushforwardCohomologyLerayDegeneration.lean` (the latter costs 20 s of type checking).
  let dX := LinearEquiv.ofBijective _
    (AlgebraicGeometry.sheafCohomology.δ_bijective hT (j + 1) (j + 1 + 1) rfl)
  let dY := LinearEquiv.ofBijective _
    (AlgebraicGeometry.sheafCohomology.δ_bijective hT' (j + 1) (j + 1 + 1) rfl)
  exact ⟨dX.toAddEquiv.symm.trans (r.trans dY.toAddEquiv)⟩

/-- **Dimension-shifting comparison.** See the module docstring for the hypotheses. -/
theorem sheafCohomology_addEquiv_of_dimensionShift (P : X.Modules → Prop)
    (h0 : ∀ M, P M → Nonempty (Γ(T.obj M, ⊤) ≃+ Γ(T'.obj M, ⊤)))
    (hS : ∀ M, P M → ∃ S : ShortComplex X.Modules, S.ShortExact ∧ S.X₁ = M ∧ P S.X₃ ∧
      (S.map T).ShortExact ∧ (S.map T').ShortExact ∧
      (∀ k : ℕ, Subsingleton (AlgebraicGeometry.sheafCohomology X₀ (S.map T).X₂ (k + 1))) ∧
      (∀ k : ℕ, Subsingleton (AlgebraicGeometry.sheafCohomology Y₀ (S.map T').X₂ (k + 1))) ∧
      Nonempty ((Γ((S.map T).X₃, ⊤) ⧸ AddMonoidHom.range ((S.map T).g.app ⊤).hom) ≃+
        (Γ((S.map T').X₃, ⊤) ⧸ AddMonoidHom.range ((S.map T').g.app ⊤).hom)))
    (p : ℕ) :
    ∀ M : X.Modules, P M →
      Nonempty (CategoryTheory.Sheaf.H (T.obj M).toAddCommGrpSheaf p ≃+
        CategoryTheory.Sheaf.H (T'.obj M).toAddCommGrpSheaf p) := by
  induction p with
  | zero =>
    intro M hM
    obtain ⟨e⟩ := h0 M hM
    exact ⟨(Sheaf.H.equiv₀ (T.obj M).toAddCommGrpSheaf (Limits.isTerminalTop (α := X₀.Opens))).trans
      (e.trans (Sheaf.H.equiv₀ (T'.obj M).toAddCommGrpSheaf
        (Limits.isTerminalTop (α := Y₀.Opens))).symm)⟩
  | succ i ih =>
    intro M hM
    obtain ⟨S, _hSE, rfl, hR, hT, hT', hvX, hvY, hq⟩ := hS M hM
    cases i with
    | zero =>
      have := hvX 0
      have := hvY 0
      exact sheafCohomology_addEquiv_one_of_quotient_addEquiv T T' S hT hT' hq
    | succ j =>
      have := hvX j
      have := hvX (j + 1)
      have := hvY j
      have := hvY (j + 1)
      obtain ⟨r⟩ := ih S.X₃ hR
      exact sheafCohomology_addEquiv_succ_of_addEquiv T T' S hT hT' j r

end AlgebraicGeometry.Scheme.Modules

end
