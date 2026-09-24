import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Morphisms.ProjectiveQuasiProjectiveProper
import MiyaokaMori.AlgebraicGeometry.Morphisms.ChowLemmaNoetherianAffineBase
import MiyaokaMori.AlgebraicGeometry.Cohomology.Coherent.ProjectiveOverNoetherianRingCohomologyFinite
import MiyaokaMori.AlgebraicGeometry.Cohomology.Pushforward.PushforwardCohomologyLerayDegenerationLinear
import MiyaokaMori.AlgebraicGeometry.Cohomology.Vanishing.Stacks02o1
import MiyaokaMori.AlgebraicGeometry.Cohomology.ExtendByZero.Stacks01xkHPrimeOpenSubscheme
import MiyaokaMori.AlgebraicGeometry.Modules.Coherent.PushforwardGenericStalkLengthOneOfIsoOnOpen

/-! # A coherent generator sheaf on an integral proper scheme

The Chow's-lemma core of Stacks 02O5 (proof, second paragraph) / EGA III 3.2.1, on an integral scheme:
for `Z` integral and `g : Z → Spec A` proper with `A` Noetherian, there is a coherent `G` on `Z` whose
stalk at the generic point `η` is a one-dimensional `κ(η) = O_{Z,η}`-vector space and whose cohomology
`H^i(Z, G)` is a finite `A`-module for every `i`. The dévissage argument for proper morphisms over a
Noetherian ring applies this to `Z = closure {ξ}` (reduced induced structure) and pushes `G` forward
along the closed immersion `Z ↪ X`.

Source: Stacks 02O5 (coherent-lemma-proper-pushforward-coherent), proof; Stacks 0200 (Chow's lemma,
Noetherian version); Hartshorne III.5.2, III.8.8; EGA III 3.2.1.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- **Coherent generator sheaf on an integral proper scheme** (Stacks 02O5, proof, the Chow's-lemma
step). `A` Noetherian, `Z` integral with generic point `η`, `g : Z → Spec A` proper. Then there is a coherent
`G : Z.Modules` with `length_{O_{Z,η}} G_η = 1` (`O_{Z,η}` is the function field, so this says `G_η ≅ κ(η)`)
and `H^i(Z, G)` a finite `A`-module for all `i` (`A`-module structure via `letI : Z.Over (Spec A) := ⟨g⟩`
and `sheafCohomology.moduleOver`).

**Proof (Stacks 02O5; the body below follows it step by step). `Z` is Noetherian: finite type over the
Noetherian `Spec A` and quasi-compact (`LocallyOfFiniteType.isLocallyNoetherian`,
`QuasiCompact.compactSpace_of_compactSpace`).**
1. *Chow's lemma over `Spec A`* (`exists_projective_birational_of_isProper_over_noetherianRing g`):
   `Z'`, `π : Z' → Z` with `π` and `π ≫ g` projective, and a nonempty open `U ⊆ Z` with `IsIso (π ∣_ U)`.
   `π` is proper (`IsProjectiveMorphism.isProper`).
2. *A relatively ample line bundle for `π`*: `IsProjectiveMorphism.isQuasiProjective_isProper π` gives
   `IsQuasiProjectiveMorphism π`, whose field `exists_relativelyAmple` is `L : Z'.Modules`, a line bundle
   with `L|_{π⁻¹V}` ample for every affine open `V ⊆ Z` (Stacks 01W8 / 0892). `L` is coherent: a line
   bundle is quasi-coherent (`IsLineBundle.isQuasicoherent`) and of finite type
   (`IsLineBundle.isFiniteType`).
3. *Relative Serre vanishing* (Stacks 02O1, `higherDirectImage_tensorPow_vanish_of_relativelyAmple π L L`):
   `n₀` with `H^p(π⁻¹V, (L ⊗ L^{⊗n₀})|_{π⁻¹V}) = 0` for all affine `V ⊆ Z`, `p > 0`. Put `N := L ⊗ L^{⊗n₀}`,
   a line bundle (`SheafOfModules.IsLineBundle.tensor`, `.tensorPow`), hence coherent.
4. *`G := π_* N` is coherent* (Stacks 02O4, `pushforward_isCoherent_of_isProjectiveMorphism π N`, `Z`
   locally Noetherian).
5. *Degenerate Leray, `A`-linearly*: the vanishing of step 3 is turned into the `H'` form by
   `hPrime_addEquiv_H_restrict` (Stacks 01E1), and then
   `sheafCohomology_pushforward_linearEquiv_of_hPrime_vanishing π g N` gives
   `H^p(Z, π_*N) ≃ₗ[A] H^p(Z', N)` for the module structures `⟨g⟩` on `Z` and `⟨π ≫ g⟩` on `Z'`.
6. *Finiteness* (`finite_sheafCohomology_of_isProjectiveMorphism_spec (π ≫ g) N p`, Stacks 02O4 with
   `S = Spec A`, `V = ⊤`): `H^p(Z', N)` is a finite `A`-module; transport along step 5
   (`Module.Finite.equiv`).
7. *The generic stalk* (`length_stalk_pushforward_genericPoint_eq_one_of_isIso_morphismRestrict π N U hU`):
   `η ∈ U`, `π ∣_ U` is an isomorphism, so `(π_*N)_η ≅ N_{η'} ≅ O_{Z',η'} ≅ O_{Z,η}`, a field, of length `1`
   over itself.

**Edge cases.** `Z` a point: `Z = Spec K`, `K` a field finite type and proper over `A`; Chow's lemma is
trivial (`Z' = Z`), `N` a line bundle on a point, `G ≅ O_Z`, `H^0 = K` finite over `A` (a proper affine
morphism is finite, Stacks 01WN) and `H^p = 0` for `p > 0`. `A` the zero ring: `Spec A = ∅`, no integral `Z`,
vacuous. `A` a field: the statement specializes to the field case.

**Why this form.** The dévissage for proper morphisms over a Noetherian ring needs, after pushing
forward along `Z ↪ X`, exactly: coherence (Stacks 01Y6), support (`Supp G = Z` since `G_η ≠ 0` and `Supp G`
is closed), `m_ξ`-annihilation and length `1` (from `length_{O_{Z,η}} G_η = 1` through the surjective
`O_{X,ξ} → O_{Z,η}`), and `A`-finiteness of cohomology (Stacks 02UV). Stating the generic-stalk condition
as `Module.length … = 1` over the field `O_{Z,η}` keeps the statement free of the closed-immersion bookkeeping. -/
theorem AlgebraicGeometry.exists_coherent_generic_finite_sheafCohomology_of_isProper_isIntegral
    {A : CommRingCat.{u}} [IsNoetherianRing A]
    {Z : AlgebraicGeometry.Scheme.{u}} [AlgebraicGeometry.IsIntegral Z]
    (g : Z ⟶ AlgebraicGeometry.Spec A) [AlgebraicGeometry.IsProper g] :
    letI : Z.Over (AlgebraicGeometry.Spec A) := ⟨g⟩
    ∃ G : Z.Modules, G.IsCoherent ∧
      Module.length (Z.presheaf.stalk (genericPoint Z)) (G.stalk (genericPoint Z)) = 1 ∧
      ∀ i : ℕ, Module.Finite A (AlgebraicGeometry.sheafCohomology Z G i) := by
  let _ : Z.Over (AlgebraicGeometry.Spec A) := ⟨g⟩
  -- `Z` is Noetherian.
  have : AlgebraicGeometry.IsLocallyNoetherian Z :=
    AlgebraicGeometry.LocallyOfFiniteType.isLocallyNoetherian g
  have : CompactSpace Z := AlgebraicGeometry.QuasiCompact.compactSpace_of_compactSpace g
  have : AlgebraicGeometry.IsNoetherian Z := ⟨⟩
  -- Step 1: Chow's lemma over `Spec A`.
  obtain ⟨Z', π, hπ, hπg, U, hU, hiso⟩ :=
    AlgebraicGeometry.exists_projective_birational_of_isProper_over_noetherianRing g
  have := hπ
  have := hπg
  have := hiso
  have : AlgebraicGeometry.IsProper π := AlgebraicGeometry.IsProjectiveMorphism.isProper π
  let _ : Z'.Over (AlgebraicGeometry.Spec A) := ⟨π ≫ g⟩
  -- Step 2: a relatively ample line bundle `L` for `π`.
  obtain ⟨L, hL, hamp⟩ :=
    (AlgebraicGeometry.IsProjectiveMorphism.isQuasiProjective_isProper π).1.exists_relativelyAmple
  have := hL
  have : L.IsCoherent := ⟨inferInstance, inferInstance⟩
  -- Step 3: relative Serre vanishing (Stacks 02O1) for `N := L ⊗ L^{⊗n₀}`.
  obtain ⟨n₀, hn₀⟩ :=
    AlgebraicGeometry.higherDirectImage_tensorPow_vanish_of_relativelyAmple π L L hamp
  let N : Z'.Modules :=
    AlgebraicGeometry.Scheme.Modules.tensor L (AlgebraicGeometry.Scheme.Modules.tensorPow L n₀)
  have : N.IsLineBundle := inferInstance
  have : N.IsCoherent := ⟨inferInstance, inferInstance⟩
  have hvan : ∀ (V : Z.affineOpens) (q : ℕ), 0 < q →
      Subsingleton (N.toAddCommGrpSheaf.H' q (π ⁻¹ᵁ V.1)) := by
    intro V q hq
    obtain ⟨e⟩ := AlgebraicGeometry.Scheme.Modules.hPrime_addEquiv_H_restrict N (π ⁻¹ᵁ V.1) q
    have := hn₀ n₀ le_rfl V q hq
    exact e.toEquiv.subsingleton
  -- Step 4: `G := π_* N` is coherent (Stacks 02O4).
  refine ⟨(AlgebraicGeometry.Scheme.Modules.pushforward π).obj N,
    AlgebraicGeometry.pushforward_isCoherent_of_isProjectiveMorphism π N, ?_, ?_⟩
  · -- Step 7: the generic stalk.
    exact AlgebraicGeometry.Scheme.Modules.length_stalk_pushforward_genericPoint_eq_one_of_isIso_morphismRestrict
      π N U hU
  · -- Steps 5–6: degenerate Leray (`A`-linear) and finiteness on the projective side.
    intro i
    obtain ⟨e⟩ :=
      AlgebraicGeometry.Scheme.Modules.sheafCohomology_pushforward_linearEquiv_of_hPrime_vanishing
        π g N hvan i
    have := AlgebraicGeometry.finite_sheafCohomology_of_isProjectiveMorphism_spec (π ≫ g) N i
    exact Module.Finite.equiv e.symm

end
