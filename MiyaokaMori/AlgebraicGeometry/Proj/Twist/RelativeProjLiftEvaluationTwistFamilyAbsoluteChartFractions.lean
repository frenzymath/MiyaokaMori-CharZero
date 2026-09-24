import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Proj.Twist.ProjTwistingSheaf
import MiyaokaMori.AlgebraicGeometry.Proj.Twist.Stacks01mw

/-! # Fraction sections `a / d` of `O(n)` over `D₊(d)` (any `SetLike` grading)

Helper module for `RelativeProjLiftEvaluationTwistFamilyAbsolute.lean`. Stacks 01MN / 01MO bookkeeping for the twisting
sheaves `O(n) = Proj.twist 𝒜 n` of an arbitrary graded ring `𝒜 : ℕ → σ` (`Stacks01n2TwistStalkSections.lean` has the
same material for `Submodule` gradings only, which does not cover `S.sectionsGrading W`).

* `fracSection 𝒜 n a d ha hd hpq : Γ(D₊(d), O(n))`, `z ↦ a / d` (`a ∈ 𝒜 p`, `d ∈ 𝒜 q`, `p = q + n`).
* `res_twistSection'`: the global section `a/1 = twistSection 𝒜 a` restricts to `homogeneousSection` on every open.
* `twistSectionMul_fracSection_homogeneousSection`: `(a / d) · (d / 1) = a / 1` in `Γ(D₊(d), O(n + q))`
  (pointwise multiplication of fractions, Stacks 01MO).
* `twistMul_app_moduleTensorSection_tfa`: `twistMul` on a pure tensor section is `twistSectionMul`.
* `exists_res_eq_fracSection`: every section of `O(n)` is, near a point of `D₊(s)` (`s` of positive degree), either
  `0` or the restriction of a fraction `a / d` with `d` of **positive** degree (multiply numerator and denominator by
  `s` if needed) — Stacks 01MN, "sections are locally fractions". -/

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory Opposite TopologicalSpace
open scoped AlgebraicGeometry TensorProduct

noncomputable section

namespace AlgebraicGeometry.Proj

open MiyaokaMori.WeightedJets.ProjTwisting

variable {A σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜]

/-- The section `a / d` of `O(n)` over `D₊(d)` (`a ∈ 𝒜 p`, `d ∈ 𝒜 q`, `p = q + n`). -/
def fracSection (n : ℤ) {p q : ℕ} (a d : A) (ha : a ∈ 𝒜 p) (hd : d ∈ 𝒜 q) (hpq : (p : ℤ) = q + n) :
    Γ(AlgebraicGeometry.Proj.twist 𝒜 n, AlgebraicGeometry.Proj.basicOpen 𝒜 d) :=
  ⟨fun z ↦ Localization.mk a ⟨d, z.2⟩,
    TopCat.PrelocalPredicate.sheafifyOf (P := fractionPrelocal 𝒜 n)
      (Or.inr ⟨p, q, ⟨a, ha⟩, ⟨d, hd⟩, hpq, fun z ↦ z.2, fun _ ↦ rfl⟩)⟩

theorem fracSection_apply (n : ℤ) {p q : ℕ} (a d : A) (ha : a ∈ 𝒜 p) (hd : d ∈ 𝒜 q) (hpq : (p : ℤ) = q + n)
    (z : AlgebraicGeometry.Proj.basicOpen 𝒜 d) :
    (fracSection 𝒜 n a d ha hd hpq).1 z = Localization.mk a ⟨d, z.2⟩ := rfl

/-- The global section `a/1 = twistSection 𝒜 a` restricted to `U` is `homogeneousSection 𝒜 d a ha U`. -/
theorem res_twistSection' {d : ℕ} (a : A) (ha : a ∈ 𝒜 d) (U : (AlgebraicGeometry.Proj 𝒜).Opens) :
    (AlgebraicGeometry.Proj.twist 𝒜 (d : ℤ)).presheaf.map (homOfLE le_top).op
        (AlgebraicGeometry.Proj.twistSection 𝒜 a ha) = homogeneousSection 𝒜 d a ha U := rfl

/-- **`(a / d) · (d / 1) = a / 1` in `Γ(D₊(d), O(n + q))`** (Stacks 01MO: pointwise multiplication of homogeneous
fractions). -/
theorem twistSectionMul_fracSection_homogeneousSection (n : ℕ) {p q : ℕ} (a d : A) (ha : a ∈ 𝒜 p) (hd : d ∈ 𝒜 q)
    (hpq : (p : ℤ) = q + n) (ha' : a ∈ 𝒜 (n + q)) :
    AlgebraicGeometry.Proj.twistSectionMul 𝒜 (n : ℤ) (q : ℤ) (AlgebraicGeometry.Proj.basicOpen 𝒜 d)
        (fracSection 𝒜 n a d ha hd hpq) (homogeneousSection 𝒜 q d hd (AlgebraicGeometry.Proj.basicOpen 𝒜 d)) =
      homogeneousSection 𝒜 (n + q) a ha' (AlgebraicGeometry.Proj.basicOpen 𝒜 d) := by
  apply Subtype.ext
  funext z
  change Localization.mk a ⟨d, z.2⟩ * Localization.mk d 1 = Localization.mk a 1
  rw [Localization.mk_mul, Localization.mk_eq_mk_iff]
  apply Localization.r_of_eq
  simp only [Submonoid.coe_mul, Submonoid.coe_one, OneMemClass.coe_one]
  ring

/-- `fracSection` restricted to `W ≤ D₊(d)` is the pointwise fraction `a / d`. -/
theorem res_fracSection_apply (n : ℤ) {p q : ℕ} (a d : A) (ha : a ∈ 𝒜 p) (hd : d ∈ 𝒜 q) (hpq : (p : ℤ) = q + n)
    {W : (AlgebraicGeometry.Proj 𝒜).Opens} (hW : W ≤ AlgebraicGeometry.Proj.basicOpen 𝒜 d) (w : W) :
    ((AlgebraicGeometry.Proj.twist 𝒜 n).presheaf.map (homOfLE hW).op (fracSection 𝒜 n a d ha hd hpq)).1 w =
      Localization.mk a ⟨d, hW w.2⟩ := rfl

/-- **Sections of `O(n)` are locally fractions with denominators of positive degree** (Stacks 01MN). Near a point
`x ∈ V ∩ D₊(s)` (`s ∈ 𝒜 e`, `0 < e`), a section `g ∈ Γ(V, O(n))` is either `0` or the restriction of some
`fracSection a d` with `d` of positive degree: if `g = a / b` near `x` with `b ∈ 𝒜 j`, use `a s / (b s)`. -/
theorem exists_res_eq_fracSection (n : ℤ) {V : (AlgebraicGeometry.Proj 𝒜).Opens}
    (g : Γ(AlgebraicGeometry.Proj.twist 𝒜 n, V)) {x : AlgebraicGeometry.Proj 𝒜} (hx : x ∈ V)
    {e : ℕ} {s : A} (hs : s ∈ 𝒜 e) (hxs : x ∈ AlgebraicGeometry.Proj.basicOpen 𝒜 s) :
    ∃ (W : (AlgebraicGeometry.Proj 𝒜).Opens) (_ : x ∈ W) (hWV : W ≤ V),
      (AlgebraicGeometry.Proj.twist 𝒜 n).presheaf.map (homOfLE hWV).op g = 0 ∨
      ∃ (p q : ℕ) (a d : A) (ha : a ∈ 𝒜 p) (hd : d ∈ 𝒜 q) (hpq : (p : ℤ) = q + n) (_ : e ≤ q)
        (hW : W ≤ AlgebraicGeometry.Proj.basicOpen 𝒜 d),
        (AlgebraicGeometry.Proj.twist 𝒜 n).presheaf.map (homOfLE hWV).op g =
          (AlgebraicGeometry.Proj.twist 𝒜 n).presheaf.map (homOfLE hW).op (fracSection 𝒜 n a d ha hd hpq) := by
  obtain ⟨W₀, hxW₀, iW₀, hfrac⟩ := (show sectionsSubmodule 𝒜 n V from g).2 ⟨x, hx⟩
  let W : (AlgebraicGeometry.Proj 𝒜).Opens := W₀ ⊓ AlgebraicGeometry.Proj.basicOpen 𝒜 s
  have hxW : x ∈ W := ⟨hxW₀, hxs⟩
  have hWV : W ≤ V := inf_le_left.trans (leOfHom iW₀)
  have hWs : W ≤ AlgebraicGeometry.Proj.basicOpen 𝒜 s := inf_le_right
  refine ⟨W, hxW, hWV, ?_⟩
  rcases hfrac with h0 | ⟨i, j, a, b, hij, hb, hrep⟩
  · left
    apply Subtype.ext
    funext w
    exact congrFun h0 ⟨w.1, w.2.1⟩
  · right
    have has : (a : A) * s ∈ 𝒜 (i + e) := SetLike.mul_mem_graded a.2 hs
    have hbs : (b : A) * s ∈ 𝒜 (j + e) := SetLike.mul_mem_graded b.2 hs
    have hpq : ((i + e : ℕ) : ℤ) = ((j + e : ℕ) : ℤ) + n := by push_cast; omega
    have hW : W ≤ AlgebraicGeometry.Proj.basicOpen 𝒜 ((b : A) * s) := by
      intro w hw
      rw [AlgebraicGeometry.Proj.mem_basicOpen]
      intro hmem
      rcases w.isPrime.mem_or_mem hmem with h | h
      · exact hb ⟨w, hw.1⟩ h
      · exact hw.2 h
    refine ⟨i + e, j + e, a * s, b * s, has, hbs, hpq, Nat.le_add_left e j, hW, ?_⟩
    apply Subtype.ext
    funext w
    change g.1 (iW₀ ⟨w.1, w.2.1⟩) = Localization.mk ((a : A) * s) ⟨(b : A) * s, hW w.2⟩
    rw [show g.1 (iW₀ ⟨w.1, w.2.1⟩) = Localization.mk (a : A) ⟨b, hb ⟨w.1, w.2.1⟩⟩ from hrep ⟨w.1, w.2.1⟩,
      Localization.mk_eq_mk_iff]
    apply Localization.r_of_eq
    simp only
    ring

/-- **`Proj.twistMul` on a pure tensor section is the pointwise product** (Stacks 01MO): `Proj.twistMul` is the
transpose of `twistMulPresheaf` under the sheafification adjunction, and `twistMulPresheaf` is `twistSectionMul` on
pure tensors. (Same statement as `twistMul_app_moduleTensorSection` in `RelativeProjTwistMulLocalChart`;
repeated here to keep the import closure of the twist-family modules small.) -/
theorem twistMul_app_moduleTensorSection_tfa (a b : ℤ) (W : (AlgebraicGeometry.Proj 𝒜).Opens)
    (s : Γ(AlgebraicGeometry.Proj.twist 𝒜 a, W)) (t : Γ(AlgebraicGeometry.Proj.twist 𝒜 b, W)) :
    (AlgebraicGeometry.Proj.twistMul 𝒜 a b).app W (AlgebraicGeometry.Scheme.Modules.moduleTensorSection s t) =
      AlgebraicGeometry.Proj.twistSectionMul 𝒜 a b W s t := by
  have h2 : ((PresheafOfModules.sheafificationAdjunction (𝟙 (AlgebraicGeometry.Proj 𝒜).ringCatSheaf.obj)).homEquiv
      _ _) (AlgebraicGeometry.Proj.twistMul 𝒜 a b) = AlgebraicGeometry.Proj.twistMulPresheaf 𝒜 a b :=
    Equiv.apply_symm_apply _ _
  exact congrArg (fun k => k.app (op W) (s ⊗ₜ[Γ(AlgebraicGeometry.Proj 𝒜, W)] t)) h2

end AlgebraicGeometry.Proj


end
