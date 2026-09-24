import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Cohomology.Pushforward.PushforwardCohomologyLerayDegeneration

/-! # Leray degeneration, `A`-linear form

**Leray degeneration, `A`-linear form** (Stacks 01F4(1), 01F2; Hartshorne III Ex. 8.1): for `f : X → Y` over
`Spec A` (via `g : Y → Spec A`) and an `O_X`-module `M` with `H^q(f⁻¹V, M) = 0` for all affine `V ⊆ Y` and all
`q > 0`, the isomorphism `H^p(Y, f_*M) ≅ H^p(X, M)` of `PushforwardCohomologyLerayDegeneration.lean`
(additive only) is `A`-linear for the module structures `sheafCohomology.moduleOver` given by `⟨g⟩` on `Y`
and `⟨f ≫ g⟩` on `X`.

Use: the Chow's-lemma step of Stacks 02O5 transports `Module.Finite A` from `H^p(Z', N)` to `H^p(Z, π_*N)`
(`Module.Finite.equiv`), which needs linearity, not just an additive bijection.

## Proof (as formalized)
The additive dimension-shifting induction of `PushforwardCohomologyLerayDegeneration.lean` is repeated, but the
induction hypothesis is strengthened to "there is `e : H^p(X, M) ≃+ H^p(Y, f_*M)` which is **twisted linear**:
`e (f^♯ r • α) = r • e α` for all `r : Γ(Y, ⊤)`" (`IsPushforwardTwistedLinear`). No naturality in `M` is needed:
* `p = 0`: `e = z_Y⁻¹ ∘ z_X` with `z = sheafCohomologyZeroEquiv` (`Γ(−, ⊤)`-linear); the scalar `r` acts on
  `Γ(f_*M, ⊤) = Γ(M, ⊤)` as `f^♯ r` **by definition** (`pushforward_appTop_smul`, `rfl`: Mathlib's
  `SheafOfModules.pushforward` is `restrictScalars` along `f^♯`).
* `p = 1`: `e = d_Y⁻¹ ∘ q ∘ d_X` with `d = sheafCohomology.one_equiv_quotient` (linear) and `q` the identity
  of `Γ(R, ⊤) = Γ(f_*R, ⊤)` on the two quotients (`exists_quotient_addEquiv_pushforward_mk`); `q` is twisted
  linear by the same `rfl` (`quotient_addEquiv_pushforward_smul`).
* `p = j + 2`: `e = δ_Y ∘ e_R ∘ δ_X⁻¹` with `δ` the (linear) bijective connecting maps
  (`sheafCohomology.δ_bijective`) and `e_R` the twisted-linear isomorphism for `R` from the induction
  hypothesis.
Finally `A` acts on both sides through `Γ(Y, ⊤)`: `(f ≫ g).appTop = g.appTop ≫ f.appTop`
(`Scheme.Hom.comp_appTop`), so the scalar `c_X` of `c : A` on `X` is `f^♯ c_Y` (`structureScalar_comp_appTop`),
and `sheafCohomology.moduleOver` is `Module.compHom` (`rfl`); twisted linearity of `e` is then exactly
`A`-linearity of `e⁻¹`.

Fully proved: `#print axioms` shows only `propext`, `Classical.choice`, `Quot.sound`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y)

/-- `Γ(Y, ⊤)` acts on `Γ(f_*M, ⊤) = Γ(M, ⊤)` through `f^♯ : Γ(Y, ⊤) → Γ(X, ⊤)`, definitionally
(`pushforward` of modules is `restrictScalars` along `f^♯`). -/
theorem pushforward_appTop_smul (M : X.Modules) (r : Γ(Y, ⊤)) (y : Γ(M, ⊤)) :
    (@HSMul.hSMul Γ(Y, ⊤) Γ((pushforward f).obj M, ⊤) Γ((pushforward f).obj M, ⊤) instHSMul r y :
      Γ((pushforward f).obj M, ⊤)) = (f.appTop r • y : Γ(M, ⊤)) := rfl

/-- An additive isomorphism `e : H^p(X, M) ≃+ H^p(Y, f_*M)` is *twisted linear* if
`e (f^♯ r • α) = r • e α` for all `r : Γ(Y, ⊤)` (scalars `Γ(X, ⊤)` on the left via
`moduleSheafH`, scalars `Γ(Y, ⊤)` on the right). -/
def IsPushforwardTwistedLinear (M : X.Modules) (p : ℕ)
    (e : AlgebraicGeometry.sheafCohomology X M p ≃+
      AlgebraicGeometry.sheafCohomology Y ((pushforward f).obj M) p) : Prop :=
  ∀ (r : Γ(Y, ⊤)) (α : AlgebraicGeometry.sheafCohomology X M p), e (f.appTop r • α) = r • e α

/-- `p = 0`: `H^0(X, M) = Γ(X, M) = Γ(Y, f_*M) = H^0(Y, f_*M)`, twisted linear. -/
theorem exists_pushforward_twistedAddEquiv_zero (M : X.Modules) :
    ∃ e : AlgebraicGeometry.sheafCohomology X M 0 ≃+
      AlgebraicGeometry.sheafCohomology Y ((pushforward f).obj M) 0,
      IsPushforwardTwistedLinear f M 0 e := by
  let zX := sheafCohomologyZeroEquiv M
  let zY := sheafCohomologyZeroEquiv ((pushforward f).obj M)
  refine ⟨zX.toAddEquiv.trans zY.symm.toAddEquiv, fun r α => ?_⟩
  show zY.symm (zX (f.appTop r • α)) = r • zY.symm (zX α)
  rw [zX.map_smul, ← pushforward_appTop_smul f M r (zX α)]
  exact zY.symm.map_smul r _

/-- The identity of `Γ(X, R) = Γ(Y, f_*R)` descends to the two quotients
`Γ(R, ⊤) ⧸ im Γ(g)` (over `Γ(X, ⊤)`) and `Γ(f_*R, ⊤) ⧸ im Γ(f_*g)` (over `Γ(Y, ⊤)`), sending `[x]` to `[x]`
(the additive version `quotient_addEquiv_pushforward` does not record the formula). -/
theorem exists_quotient_addEquiv_pushforward_mk (S : ShortComplex X.Modules) :
    ∃ q : (Γ(S.X₃, ⊤) ⧸ LinearMap.range (Scheme.Modules.Hom.appTopLinear S.g)) ≃+
      (Γ((S.map (pushforward f)).X₃, ⊤) ⧸
        LinearMap.range (Scheme.Modules.Hom.appTopLinear (S.map (pushforward f)).g)),
      ∀ x : Γ(S.X₃, ⊤), q (Submodule.Quotient.mk x) =
        (LinearMap.range (Scheme.Modules.Hom.appTopLinear (S.map (pushforward f)).g)).mkQ x := by
  let pX := LinearMap.range (Scheme.Modules.Hom.appTopLinear S.g)
  let pY := LinearMap.range (Scheme.Modules.Hom.appTopLinear (S.map (pushforward f)).g)
  let qX : Γ(S.X₃, ⊤) →+ Γ(S.X₃, ⊤) ⧸ pX := pX.mkQ.toAddMonoidHom
  let qY : Γ(S.X₃, ⊤) →+ Γ((S.map (pushforward f)).X₃, ⊤) ⧸ pY := pY.mkQ.toAddMonoidHom
  have hker : qX.ker = qY.ker := by
    ext x
    constructor
    · intro hx
      obtain ⟨y, hy⟩ := LinearMap.mem_range.1 ((Submodule.Quotient.mk_eq_zero pX).1 hx)
      exact (Submodule.Quotient.mk_eq_zero pY).2 (LinearMap.mem_range.2 ⟨y, hy⟩)
    · intro hx
      obtain ⟨y, hy⟩ := LinearMap.mem_range.1 ((Submodule.Quotient.mk_eq_zero pY).1 hx)
      exact (Submodule.Quotient.mk_eq_zero pX).2 (LinearMap.mem_range.2 ⟨y, hy⟩)
  let eX := QuotientAddGroup.quotientKerEquivOfSurjective qX (Submodule.mkQ_surjective pX)
  let eY := QuotientAddGroup.quotientKerEquivOfSurjective qY (Submodule.mkQ_surjective pY)
  refine ⟨eX.symm.trans ((QuotientAddGroup.quotientAddEquivOfEq hker).trans eY), fun x => ?_⟩
  have h1 : eX.symm (Submodule.Quotient.mk x) = QuotientAddGroup.mk x := by
    apply eX.injective
    rw [eX.apply_symm_apply]
    rfl
  show eY ((QuotientAddGroup.quotientAddEquivOfEq hker) (eX.symm (Submodule.Quotient.mk x))) = _
  rw [h1]
  rfl

/-- The quotient identification `[x] ↦ [x]` is twisted linear: `q (f^♯ r • a) = r • q a`. -/
theorem quotient_addEquiv_pushforward_smul (S : ShortComplex X.Modules)
    (q : (Γ(S.X₃, ⊤) ⧸ LinearMap.range (Scheme.Modules.Hom.appTopLinear S.g)) ≃+
      (Γ((S.map (pushforward f)).X₃, ⊤) ⧸
        LinearMap.range (Scheme.Modules.Hom.appTopLinear (S.map (pushforward f)).g)))
    (hq : ∀ x : Γ(S.X₃, ⊤), q (Submodule.Quotient.mk x) =
        (LinearMap.range (Scheme.Modules.Hom.appTopLinear (S.map (pushforward f)).g)).mkQ x)
    (r : Γ(Y, ⊤)) (a : Γ(S.X₃, ⊤) ⧸ LinearMap.range (Scheme.Modules.Hom.appTopLinear S.g)) :
    q (f.appTop r • a) = r • q a := by
  induction a using Submodule.Quotient.induction_on with
  | H x =>
    rw [← Submodule.Quotient.mk_smul, hq, hq, ← pushforward_appTop_smul f S.X₃ r x]
    exact (Submodule.mkQ _).map_smul r _

/-- The `p = 1` step: `H^1(X, M) ≃+ H^1(Y, f_*M)` through `coker(Γ(I) → Γ(R))`, twisted linear. -/
theorem exists_pushforward_twistedAddEquiv_one (S : ShortComplex X.Modules) (hS : S.ShortExact)
    (hT : (S.map (pushforward f)).ShortExact)
    [Subsingleton (AlgebraicGeometry.sheafCohomology X S.X₂ 1)]
    [Subsingleton (AlgebraicGeometry.sheafCohomology Y (S.map (pushforward f)).X₂ 1)] :
    ∃ e : AlgebraicGeometry.sheafCohomology X S.X₁ 1 ≃+
      AlgebraicGeometry.sheafCohomology Y ((pushforward f).obj S.X₁) 1,
      IsPushforwardTwistedLinear f S.X₁ 1 e := by
  obtain ⟨dX⟩ := AlgebraicGeometry.sheafCohomology.one_equiv_quotient hS
  obtain ⟨dY⟩ := AlgebraicGeometry.sheafCohomology.one_equiv_quotient hT
  obtain ⟨q, hq⟩ := exists_quotient_addEquiv_pushforward_mk f S
  refine ⟨dX.toAddEquiv.trans (q.trans dY.toAddEquiv.symm), fun r α => ?_⟩
  show dY.symm (q (dX (f.appTop r • α))) = r • dY.symm (q (dX α))
  rw [dX.map_smul, quotient_addEquiv_pushforward_smul f S q hq, dY.symm.map_smul]

/-- The shift step: a twisted-linear `H^{j+1}(X, R) ≃+ H^{j+1}(Y, f_*R)` gives a twisted-linear
`H^{j+2}(X, M) ≃+ H^{j+2}(Y, f_*M)` through the (linear, bijective) connecting maps. -/
theorem exists_pushforward_twistedAddEquiv_succ (S : ShortComplex X.Modules) (hS : S.ShortExact)
    (hT : (S.map (pushforward f)).ShortExact) (j : ℕ)
    [Subsingleton (AlgebraicGeometry.sheafCohomology X S.X₂ (j + 1))]
    [Subsingleton (AlgebraicGeometry.sheafCohomology X S.X₂ (j + 1 + 1))]
    [Subsingleton (AlgebraicGeometry.sheafCohomology Y (S.map (pushforward f)).X₂ (j + 1))]
    [Subsingleton (AlgebraicGeometry.sheafCohomology Y (S.map (pushforward f)).X₂ (j + 1 + 1))]
    (r : AlgebraicGeometry.sheafCohomology X S.X₃ (j + 1) ≃+
      AlgebraicGeometry.sheafCohomology Y ((pushforward f).obj S.X₃) (j + 1))
    (hr : IsPushforwardTwistedLinear f S.X₃ (j + 1) r) :
    ∃ e : AlgebraicGeometry.sheafCohomology X S.X₁ (j + 1 + 1) ≃+
      AlgebraicGeometry.sheafCohomology Y ((pushforward f).obj S.X₁) (j + 1 + 1),
      IsPushforwardTwistedLinear f S.X₁ (j + 1 + 1) e := by
  -- `LinearEquiv.ofBijective _ …` as in the additive proof (cheap kernel check).
  let dX := LinearEquiv.ofBijective _
    (AlgebraicGeometry.sheafCohomology.δ_bijective hS (j + 1) (j + 1 + 1) rfl)
  let dY := LinearEquiv.ofBijective _
    (AlgebraicGeometry.sheafCohomology.δ_bijective hT (j + 1) (j + 1 + 1) rfl)
  refine ⟨dX.toAddEquiv.symm.trans (r.trans dY.toAddEquiv), fun s β => ?_⟩
  show dY (r (dX.symm (f.appTop s • β))) = s • dY (r (dX.symm β))
  rw [dX.symm.map_smul, hr]
  exact dY.map_smul s _

/-- **Leray degeneration, twisted-linear form**: if `H^q(f⁻¹V, M) = 0` for all affine opens `V ⊆ Y`
and all `q > 0`, then for all `p` there is `e : H^p(X, M) ≃+ H^p(Y, f_*M)` with
`e (f^♯ r • α) = r • e α` for all `r : Γ(Y, ⊤)`. Same induction as
`sheafCohomology_pushforward_addEquiv_of_hPrime_vanishing`, carrying the twisted linearity along. -/
theorem exists_pushforward_twistedAddEquiv_of_hPrime_vanishing (p : ℕ) :
    ∀ (M : X.Modules),
      (∀ (V : Y.affineOpens) (q : ℕ), 0 < q →
        Subsingleton (M.toAddCommGrpSheaf.H' q (f ⁻¹ᵁ V.1))) →
      ∃ e : AlgebraicGeometry.sheafCohomology X M p ≃+
        AlgebraicGeometry.sheafCohomology Y ((pushforward f).obj M) p,
        IsPushforwardTwistedLinear f M p e := by
  induction p with
  | zero =>
    intro M _
    exact exists_pushforward_twistedAddEquiv_zero f M
  | succ i ih =>
    intro M hM
    -- 0 → M → I → R → 0 with I injective
    let S : ShortComplex X.Modules :=
      ShortComplex.mk (Injective.ι M) (cokernel.π (Injective.ι M)) (cokernel.condition _)
    have hS : S.ShortExact :=
      { exact := ShortComplex.exact_cokernel (Injective.ι M)
        mono_f := inferInstanceAs (Mono (Injective.ι M))
        epi_g := inferInstanceAs (Epi (cokernel.π (Injective.ι M))) }
    have hinj : Injective S.X₂ := inferInstanceAs (Injective (Injective.under M))
    have hepi : Epi ((pushforward f).map S.g) :=
      epi_pushforward_map_of_hPrime_one f S hS (fun V => hM V 1 one_pos)
    have hT : (S.map (pushforward f)).ShortExact := shortExact_map_pushforward f S hS hepi
    have hR : ∀ (V : Y.affineOpens) (q : ℕ), 0 < q →
        Subsingleton (S.X₃.toAddCommGrpSheaf.H' q (f ⁻¹ᵁ V.1)) := fun V q hq =>
      hPrime_subsingleton_quotient S hS _ q (hPrime_subsingleton_of_injective S.X₂ _ q hq)
        (hM V (q + 1) (Nat.succ_pos q))
    have hXI : ∀ k : ℕ, Subsingleton (AlgebraicGeometry.sheafCohomology X S.X₂ (k + 1)) := fun k =>
      AlgebraicGeometry.sheafCohomology.subsingleton_of_injective S.X₂ k
    have hYI : ∀ k : ℕ,
        Subsingleton (AlgebraicGeometry.sheafCohomology Y (S.map (pushforward f)).X₂ (k + 1)) :=
      fun k => subsingleton_sheafCohomology_pushforward_of_injective f S.X₂ k
    cases i with
    | zero =>
      have := hXI 0
      have := hYI 0
      exact exists_pushforward_twistedAddEquiv_one f S hS hT
    | succ j =>
      have := hXI j
      have := hXI (j + 1)
      have := hYI j
      have := hYI (j + 1)
      obtain ⟨r, hr⟩ := ih S.X₃ hR
      exact exists_pushforward_twistedAddEquiv_succ f S hS hT j r hr

/-- For `f : X → Y` and `g : Y → Spec A`, the image of `c : A` in `Γ(X, ⊤)` (through `f ≫ g`) is `f^♯` of
its image in `Γ(Y, ⊤)` (through `g`): `(f ≫ g).appTop = g.appTop ≫ f.appTop`. -/
theorem structureScalar_comp_appTop {A : CommRingCat.{u}} (g : Y ⟶ AlgebraicGeometry.Spec A) (c : A) :
    (((Scheme.ΓSpecIso A).inv ≫ (f ≫ g).appTop).hom) c
      = f.appTop ((((Scheme.ΓSpecIso A).inv ≫ g.appTop).hom) c) := by
  rw [Scheme.Hom.comp_appTop]
  rfl

/-- **Leray degeneration, `A`-linear form** (Stacks 01F4(1); Hartshorne III Ex. 8.1 and III.4.5). If
`H^q(f⁻¹V, M) = 0` for all affine opens `V ⊆ Y` and all `q > 0` (hypothesis in the `H'` form used by
`sheafCohomology_pushforward_addEquiv_of_hPrime_vanishing` and by Stacks 01XB), then
`H^p(Y, f_*M) ≃ₗ[A] H^p(X, M)` for every `p`, where `A` acts through `A ≅ Γ(Spec A, ⊤) → Γ(Y, ⊤)` on the left
and through `A → Γ(Y, ⊤) → Γ(X, ⊤)` (`f.appTop`) on the right (`sheafCohomology.moduleOver`).

**Proof.** `exists_pushforward_twistedAddEquiv_of_hPrime_vanishing` gives `e : H^p(X, M) ≃+ H^p(Y, f_*M)`
with `e (f^♯ r • α) = r • e α` for `r : Γ(Y, ⊤)`. For `c : A`, `c • β = c_Y • β` on `Y` and
`c • α = c_X • α` on `X` (`sheafCohomology.moduleOver` is `Module.compHom`, `rfl`), and `c_X = f^♯ c_Y`
(`structureScalar_comp_appTop`). Hence `e (c • e⁻¹ β) = c_Y • β = c • β`, i.e. `e⁻¹` is `A`-linear.
The edge cases (`p = 0`, `f = 𝟙`, `M = 0`, `A = 0`) need no separate treatment. -/
theorem sheafCohomology_pushforward_linearEquiv_of_hPrime_vanishing
    {A : CommRingCat.{u}} {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y)
    (g : Y ⟶ AlgebraicGeometry.Spec A) (M : X.Modules)
    (hM : ∀ (V : Y.affineOpens) (q : ℕ), 0 < q →
      Subsingleton (M.toAddCommGrpSheaf.H' q (f ⁻¹ᵁ V.1)))
    (p : ℕ) :
    letI : X.Over (AlgebraicGeometry.Spec A) := ⟨f ≫ g⟩
    letI : Y.Over (AlgebraicGeometry.Spec A) := ⟨g⟩
    Nonempty (AlgebraicGeometry.sheafCohomology Y ((pushforward f).obj M) p ≃ₗ[A]
      AlgebraicGeometry.sheafCohomology X M p) := by
  let _ : X.Over (AlgebraicGeometry.Spec A) := ⟨f ≫ g⟩
  let _ : Y.Over (AlgebraicGeometry.Spec A) := ⟨g⟩
  obtain ⟨e, he⟩ := exists_pushforward_twistedAddEquiv_of_hPrime_vanishing f p M hM
  refine ⟨{ e.symm with map_smul' := fun c β => ?_ }⟩
  show e.symm (c • β) = c • e.symm β
  apply e.injective
  rw [e.apply_symm_apply]
  have h1 : c • β = (((Scheme.ΓSpecIso A).inv ≫ g.appTop).hom c) • β := rfl
  have h2 : c • e.symm β = (((Scheme.ΓSpecIso A).inv ≫ (f ≫ g).appTop).hom c) • e.symm β := rfl
  rw [h1, h2, structureScalar_comp_appTop f g c, he, e.apply_symm_apply]

end AlgebraicGeometry.Scheme.Modules

end
