import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Chow.ChernClass.FirstChernCapPointwise
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.ModulesPullbackMonoidal
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModulesTensor
import MiyaokaMori.AlgebraicGeometry.Modules.Stalk.StalkTensorPairing

/-! # The divisor of a tensor product of rational sections

Let `W` be integral and locally Noetherian, `A`, `B` line bundles with `A ⊗ B` a line bundle.
(T1a) There is a family of stalk-level pairings `μ_x : A_x × B_x → (A ⊗ B)_x` (`x` running over the points
of `W`) such that (i) it is bilinearly homogeneous for scalars of the local ring:
`μ_x(r•a, r'•b) = (r r')•μ_x(a, b)`; (ii) it is compatible with specialization to the generic point:
`μ_η(j a, j b) = j(μ_z(a, b))`; (iii) generators pair to generators: if `a`, `b` generate `A_z`, `B_z`,
then `μ_z(a, b)` generates `(A ⊗ B)_z`.
(T1) For nonzero rational sections `s ∈ A_η`, `t ∈ B_η` there is a nonzero `u ∈ (A ⊗ B)_η` with
`div(u) = div(s) + div(t)` (Stacks 02SL).
(T2) For `X` locally Noetherian, `L`, `M`, `L ⊗ M` line bundles and `ht w = e+1`,
`capPoint (L⊗M) w − capPoint L w − capPoint M w` is an `IsRatEquivGen X e w`.

Proof:
1. (T1a): take germs of the section pairing `AlgebraicGeometry.Scheme.Modules.moduleTensorSection` (defined on every open `U`,
   compatible with restriction `moduleTensorSection_restrict`, homogeneous for scalars
   `moduleTensorSection_smul`); (iii) follows on a common trivializing open from `O ⊗ O ≅ O`.
2. (T1): let `u := μ_η(s, t)`. For any `z` and generators `a`, `b`, write `s = f•j a`, `t = g•j b`
   (`exists_smul_toGenericFiber_eq`); then `u = (f g)•j(μ_z(a,b))` by (i), (ii), and `μ_z(a,b)` is a
   generator by (iii), so `ord_z(u) = ord_z(f g) = ord_z f + ord_z g`
   (`rationalSectionOrd_eq_ord_of_generator`, Mathlib's `Scheme.ord_mul`).
3. (T2): `ι_w^*(L ⊗ M) ≅ ι_w^*L ⊗ ι_w^*M` (`pullbackTensorIso`); use (T1) and Stacks 02SH (change of
   section).

Source: Stacks 02SL (divisors-lemma-c1-additive), 02SP.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u
open CategoryTheory AlgebraicGeometry Opposite
noncomputable section
namespace AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules MiyaokaMori.FirstChernCapPointClosurePushforward
  MiyaokaMori.FirstChernCapPointGeneric

/-- The image of a generator at the generic point is nonzero. -/
theorem Scheme.Modules.toGenericFiber_generator_ne_zero {W : Scheme.{u}} [IsIntegral W]
    (M : W.Modules) [M.IsLineBundle] (z : W) (t : M.presheaf.stalk z)
    (ht : Submodule.span (W.presheaf.stalk z) {t} = ⊤) :
    moduleStalkToGenericFiber W M z t ≠ 0 := by
  obtain ⟨s₀, hs₀⟩ := Scheme.Modules.exists_stalk_genericPoint_ne_zero M
  obtain ⟨g, hg⟩ := Scheme.Modules.exists_smul_toGenericFiber_eq M z t ht s₀
  intro h0
  apply hs₀
  rw [← hg, h0]
  exact smul_zero (A := M.presheaf.stalk (genericPoint W)) g

/-- (T1) **Stacks 02SL**: the divisor of rational sections is additive under tensor products. -/
theorem Scheme.Modules.exists_rationalSectionDivisor_tensor {W : Scheme.{u}} [IsIntegral W]
    [IsLocallyNoetherian W] (A B : W.Modules) [A.IsLineBundle] [B.IsLineBundle]
    [(Scheme.Modules.tensor A B).IsLineBundle]
    (s : A.stalk (genericPoint W)) (t : B.stalk (genericPoint W)) (hs : s ≠ 0) (ht : t ≠ 0) :
    ∃ u : (Scheme.Modules.tensor A B).stalk (genericPoint W), u ≠ 0 ∧
      (Scheme.Modules.tensor A B).rationalSectionDivisor u =
        A.rationalSectionDivisor s + B.rationalSectionDivisor t := by
  obtain ⟨μ, hsmul, hgen, hspan⟩ := Scheme.Modules.exists_stalkTensorPairing A B
  have key : ∀ z : W, ∃ (f g : W.functionField) (τ : (Scheme.Modules.tensor A B).presheaf.stalk z),
      f ≠ 0 ∧ g ≠ 0 ∧ Submodule.span (W.presheaf.stalk z) {τ} = ⊤ ∧
      (f * g) • moduleStalkToGenericFiber W (Scheme.Modules.tensor A B) z τ
        = μ (genericPoint W) s t ∧
      A.rationalSectionOrd s z = W.ord f z ∧ B.rationalSectionOrd t z = W.ord g z := by
    intro z
    obtain ⟨a, ha⟩ := Scheme.Modules.exists_stalk_generator A z
    obtain ⟨b, hb⟩ := Scheme.Modules.exists_stalk_generator B z
    obtain ⟨f, hf⟩ := Scheme.Modules.exists_smul_toGenericFiber_eq A z a ha s
    obtain ⟨g, hg⟩ := Scheme.Modules.exists_smul_toGenericFiber_eq B z b hb t
    have hf0 : f ≠ 0 := by
      intro h0; apply hs; rw [← hf, h0]; exact zero_smul _ _
    have hg0 : g ≠ 0 := by
      intro h0; apply ht; rw [← hg, h0]; exact zero_smul _ _
    refine ⟨f, g, μ z a b, hf0, hg0, hspan z a b ha hb, ?_,
      Scheme.Modules.rationalSectionOrd_eq_ord_of_generator A z a ha f s hs hf,
      Scheme.Modules.rationalSectionOrd_eq_ord_of_generator B z b hb g t ht hg⟩
    rw [← hgen z a b, ← hsmul, hf, hg]
  obtain ⟨f₀, g₀, τ₀, hf₀, hg₀, hτ₀, hu₀, -, -⟩ := key (genericPoint W)
  have hu : μ (genericPoint W) s t ≠ 0 := by
    rw [← hu₀]
    exact smul_ne_zero (mul_ne_zero hf₀ hg₀)
      (Scheme.Modules.toGenericFiber_generator_ne_zero _ _ τ₀ hτ₀)
  refine ⟨μ (genericPoint W) s t, hu, ?_⟩
  ext z
  obtain ⟨f, g, τ, hf, hg, hτ, huz, hordA, hordB⟩ := key z
  show (Scheme.Modules.tensor A B).rationalSectionOrd _ z =
    A.rationalSectionOrd s z + B.rationalSectionOrd t z
  rw [Scheme.Modules.rationalSectionOrd_eq_ord_of_generator _ z τ hτ (f * g) _ hu huz,
    Scheme.ord_mul hf hg, hordA, hordB]

/-- (T2) Tensor products: the pointwise difference is a generator of rational equivalence. -/
theorem isRatEquivGen_firstChernCapPoint_tensor {X : Scheme.{u}} [IsLocallyNoetherian X]
    (L M : X.Modules) [L.IsLineBundle] [M.IsLineBundle]
    [(Scheme.Modules.tensor L M).IsLineBundle] (e : ℕ) (w : X)
    (hw : Order.height w = ((e + 1 : ℕ) : ℕ∞)) :
    IsRatEquivGen X e w (firstChernCapPoint (Scheme.Modules.tensor L M) w
      - firstChernCapPoint L w - firstChernCapPoint M w) := by
  have hLN : IsLocallyNoetherian (X.pointClosure w) := Scheme.isLocallyNoetherian_pointClosure w
  obtain ⟨sT, hsT, hT⟩ := exists_firstChernCapPoint_eq (Scheme.Modules.tensor L M) w
  obtain ⟨sL, hsL, hL⟩ := exists_firstChernCapPoint_eq L w
  obtain ⟨sM, hsM, hM⟩ := exists_firstChernCapPoint_eq M w
  let ψ := Scheme.Modules.pullbackTensorIso (X.pointClosureι w) L M
  have : (Scheme.Modules.tensor ((Scheme.Modules.pullback (X.pointClosureι w)).obj L)
      ((Scheme.Modules.pullback (X.pointClosureι w)).obj M)).IsLineBundle :=
    Scheme.Modules.IsLineBundle.of_iso ψ
  obtain ⟨u, hu, hdiv⟩ := Scheme.Modules.exists_rationalSectionDivisor_tensor _ _ sL sM hsL hsM
  obtain ⟨g, hg⟩ := exists_rationalSectionDivisor_eq_add_principalCycle _ _ u
    (moduleStalkMap_iso_ne_zero ψ _ sT hsT) hu
  refine ⟨hw, inferInstance, inferInstance, hLN, g, ?_⟩
  rw [hT, hL, hM, rationalSectionDivisor_iso ψ sT hsT, hg, hdiv]
  have hadd : ∀ a b c : AlgebraicCycle (X.pointClosure w) ℤ,
      AlgebraicGeometry.AlgebraicCycle.properPushforward (X.pointClosureι w) (a + b + c)
        - AlgebraicGeometry.AlgebraicCycle.properPushforward (X.pointClosureι w) a
        - AlgebraicGeometry.AlgebraicCycle.properPushforward (X.pointClosureι w) b
      = AlgebraicGeometry.AlgebraicCycle.properPushforward (X.pointClosureι w) c := by
    intro a b c
    have h1 := map_add (AlgebraicCycle.properPushforwardHom (X.pointClosureι w)) (a + b) c
    have h2 := map_add (AlgebraicCycle.properPushforwardHom (X.pointClosureι w)) a b
    rw [h2] at h1
    show (AlgebraicCycle.properPushforwardHom (X.pointClosureι w)) (a + b + c) -
      (AlgebraicCycle.properPushforwardHom (X.pointClosureι w)) a -
      (AlgebraicCycle.properPushforwardHom (X.pointClosureι w)) b = _
    rw [h1]
    abel
  exact hadd _ _ _

end AlgebraicGeometry
end
