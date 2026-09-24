import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Coherent.ModuleSupportGenericPoints
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.ModulesPullbackLineBundlePow
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModuleTensorPowerIsoTensorPow
import MiyaokaMori.AlgebraicGeometry.Cohomology.Pushforward.SheafCohomologyClosedImmersionLinear
import MiyaokaMori.AlgebraicGeometry.Modules.Coherent.CoherentDevissageSupportSubset
import MiyaokaMori.AlgebraicGeometry.Chow.Snapper.Stacks0bem
import MiyaokaMori.AlgebraicGeometry.Chow.Snapper.SnapperLowDegreeInvariant
import MiyaokaMori.AlgebraicGeometry.Modules.Coherent.PointClosurePushforwardUnitStalk

/-! # The leading term of the Snapper polynomial (Stacks 0BEN)

Stacks 0BEN: for `X` proper over `k`, `F` coherent with `d = dim Supp F`, and invertible sheaves
`L_1, …, L_r`, the difference `χ(X, F ⊗ ⨂L_j^{n_j}) − Σ_i m_i χ(Z_i, ⨂(L_j|_{Z_i})^{n_j})` is a numerical
polynomial of total degree `< d`, where the `Z_i` are the `d`-dimensional irreducible components of
`Supp F` (with the reduced induced structure) and `m_i = length_{O_{X,ξ_i}} F_{ξ_i}`.

Source: Stacks 0BEN (varieties-lemma-numerical-polynomial-leading-term).

## Proof: dévissage inside `Supp F`

Write `E(G)(n) := χ(X, G ⊗ L^n) − Σ_{dim closure{ξ} = d} (length G_ξ).toNat · χ(Z_ξ, (L|_{Z_ξ})^n)`
(`Stacks0ben.defect`) and `Good G := E(G)` is a polynomial that is `0` or of total degree `< d`
(`Stacks0ben.Good`). The theorem is `Good F`, obtained from the **support-restricted dévissage**
`coherent_devissage_of_support_subset` (Stacks 01YI run
inside `T := Supp F`, which is closed of dimension `≤ d`) with `P := Good`:

* zero objects: `E(0) = 0` (`good_of_isZero`);
* two out of three: `E` is additive on short exact sequences of coherent sheaves supported in `T`
  (`defect_add`: `χ` additive after twisting, Stacks 08AA; lengths additive on stalks and finite at
  the points `ξ` with `dim closure{ξ} = d`, which are maximal in `T`), and "`0` or degree `< d`" is
  closed under `±`;
* generators: for `ξ ∈ T` take `G := i_* O_{Z_ξ}`, `i : Z_ξ = X.pointClosure ξ → X`
  (coherent, `Supp G = closure{ξ}`, `m_ξ G_ξ = 0`,
  `length G_ξ = 1`). If `dim closure{ξ} < d`, all multiplicities of `G` at `d`-dimensional points vanish
  and `E(G) = χ(G ⊗ L^n)` is a polynomial of total degree `≤ dim closure{ξ} < d` by Snapper's theorem
  (Stacks 0BEM). If `dim closure{ξ} = d`, the only `d`-dimensional point of
  `closure{ξ}` is `ξ` itself, with multiplicity `1`, and `χ(X, i_*O_{Z_ξ} ⊗ L^n) = χ(Z_ξ, (i^*L)^n)`
  (projection formula `twistList_pushforward_iso`, Stacks 02UV `sheafEulerCharacteristic_closedImmersion`,
  `i^*(L^p) ≅ (i^*L)^p`), so `E(G) = 0`.

Why not the plain 01YI on `X`: the 0BEN invariant is only meaningful for `dim Supp ≤ d`, and
two-out-of-three fails for it across dimensions (a sheaf with `dim Supp = d` is a quotient of `O_X`);
the Stacks proof of 0BEN uses the filtration 01YF, whose sheaves all live inside `Supp F` — exactly the
restricted dévissage.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.style.haveILetI false

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Stacks0ben

/-- Termwise isomorphic families give isomorphic twists. -/
private def twistListFamilyIso {X : AlgebraicGeometry.Scheme.{u}} {r : ℕ} {𝓜 𝓝 : Fin r → X.Modules}
    (e : ∀ j, 𝓜 j ≅ 𝓝 j) (l : List (Fin r)) (G : X.Modules) :
    Scheme.Modules.twistList 𝓜 l G ≅ Scheme.Modules.twistList 𝓝 l G :=
  match l with
  | [] => Iso.refl _
  | j :: l =>
    twistListFamilyIso e l (G.tensor (𝓜 j)) ≪≫
      Scheme.Modules.twistList_mapIso 𝓝 l (Scheme.Modules.tensorIsoRight G (e j))

/-- The finsum over `{dim closure{ξ} = d}` of `g` vanishes if `g` vanishes there. -/
private theorem finsum_dim_eq_zero {X : AlgebraicGeometry.Scheme.{u}} {d : ℕ} (g : X → ℚ)
    (h : ∀ ξ, topologicalKrullDim (closure {ξ} : Set X) = (d : WithBot ℕ∞) → g ξ = 0) :
    ∑ᶠ (ξ : X) (_ : topologicalKrullDim (closure {ξ} : Set X) = (d : WithBot ℕ∞)), g ξ = 0 := by
  change ∑ᶠ (ξ : X) (_ : ξ ∈ {ξ : X | topologicalKrullDim (closure {ξ} : Set X) = (d : WithBot ℕ∞)}), g ξ
    = 0
  rw [finsum_mem_def]
  refine finsum_eq_zero_of_forall_eq_zero fun ξ => ?_
  by_cases hmem : ξ ∈ {ξ : X | topologicalKrullDim (closure {ξ} : Set X) = (d : WithBot ℕ∞)}
  · rw [Set.indicator_of_mem hmem, h ξ hmem]
  · exact Set.indicator_of_notMem hmem g

/-- The finsum over `{dim closure{ξ} = d}` of `g` with `g` vanishing away from `ξ₀`
(`dim closure{ξ₀} = d`) is `g ξ₀`. -/
private theorem finsum_dim_eq_single {X : AlgebraicGeometry.Scheme.{u}} {d : ℕ} (g : X → ℚ) (ξ₀ : X)
    (hξ₀ : topologicalKrullDim (closure {ξ₀} : Set X) = (d : WithBot ℕ∞))
    (h : ∀ ξ, ξ ≠ ξ₀ → topologicalKrullDim (closure {ξ} : Set X) = (d : WithBot ℕ∞) → g ξ = 0) :
    ∑ᶠ (ξ : X) (_ : topologicalKrullDim (closure {ξ} : Set X) = (d : WithBot ℕ∞)), g ξ = g ξ₀ := by
  change ∑ᶠ (ξ : X) (_ : ξ ∈ {ξ : X | topologicalKrullDim (closure {ξ} : Set X) = (d : WithBot ℕ∞)}), g ξ
    = g ξ₀
  rw [finsum_mem_def, finsum_eq_single _ ξ₀]
  · exact Set.indicator_of_mem (show ξ₀ ∈ {ξ : X | _} from hξ₀) g
  · intro ξ hξ
    by_cases hmem : ξ ∈ {ξ : X | topologicalKrullDim (closure {ξ} : Set X) = (d : WithBot ℕ∞)}
    · rw [Set.indicator_of_mem hmem, h ξ hξ hmem]
    · exact Set.indicator_of_notMem hmem g

end AlgebraicGeometry.Stacks0ben

open Classical in
/-- **Stacks 0BEN.** For `X` proper over `k`, `F` coherent with `d = dim Supp F` and invertible sheaves
`L_1, …, L_r`: `χ(F ⊗ ⨂ L_j^{n_j}) − Σ_ξ m_ξ χ(Z_ξ, ⨂ (L_j|_{Z_ξ})^{n_j})` is a numerical polynomial of
total degree `< d`, where `ξ` runs over the points with `dim closure{ξ} = d` (those in `Supp F` are
exactly the generic points of the `d`-dimensional components; the others have `m_ξ = 0`),
`Z_ξ` is `closure{ξ}` with its reduced induced structure and `m_ξ = length_{O_{X,ξ}} F_ξ`. -/
theorem AlgebraicGeometry.exists_snapper_sub_components_totalDegree_lt {k : Type u} [Field k]
    (X : AlgebraicGeometry.Scheme.{u})
    [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] (hX : IsProperOver k X)
    (F : X.Modules) [F.IsCoherent] {r : ℕ} (L : Fin r → X.Modules) [∀ i, (L i).IsLineBundle]
    (d : ℕ) (hd : topologicalKrullDim (F.support) = d) :
    ∃ P : MvPolynomial (Fin r) ℚ, (P = 0 ∨ P.totalDegree < d) ∧
      ∀ n : Fin r → ℤ,
        (AlgebraicGeometry.sheafEulerCharacteristic (k := k) X
            ((List.finRange r).foldl (fun (G : X.Modules) (i : Fin r) => G.tensor (L i ^ n i)) F) : ℚ)
          - ∑ᶠ (ξ : X) (_ : topologicalKrullDim (closure {ξ} : Set X) = d),
              ((Module.length (X.presheaf.stalk ξ) (F.stalk ξ)).toNat : ℚ) *
              (letI : (AlgebraicGeometry.Scheme.pointClosure ξ).Over
                    (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
                  ⟨AlgebraicGeometry.Scheme.pointClosureι ξ ≫ (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩
               (AlgebraicGeometry.sheafEulerCharacteristic (k := k) (AlgebraicGeometry.Scheme.pointClosure ξ)
                  ((List.finRange r).foldl
                    (fun (G : (AlgebraicGeometry.Scheme.pointClosure ξ).Modules) (i : Fin r) =>
                      G.tensor ((AlgebraicGeometry.Scheme.Modules.pullback
                        (AlgebraicGeometry.Scheme.pointClosureι ξ)).obj (L i) ^ n i))
                    (show (AlgebraicGeometry.Scheme.pointClosure ξ).Modules from
                      SheafOfModules.unit (AlgebraicGeometry.Scheme.pointClosure ξ).ringCatSheaf)) : ℚ))
          = MvPolynomial.eval (fun i => (n i : ℚ)) P := by
  -- the statement is `Good F`
  suffices h : Stacks0ben.Good k X L d F by
    obtain ⟨Q, hQ, hQn⟩ := h
    exact ⟨Q, hQ, fun n => hQn n⟩
  have hloc : AlgebraicGeometry.IsLocallyNoetherian X := isLocallyNoetherian_of_isProperOver X hX
  have hnoeth : NoetherianSpace X := noetherianSpace_of_isProperOver X hX
  have hprop : AlgebraicGeometry.IsProper (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) := hX
  have hcpt : CompactSpace X :=
    AlgebraicGeometry.QuasiCompact.compactSpace_of_compactSpace
      (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
  have : AlgebraicGeometry.IsNoetherian X := ⟨⟩
  have hTc : IsClosed F.support := Scheme.Modules.isClosed_support_of_isCoherent F
  have hTd : topologicalKrullDim F.support ≤ (d : WithBot ℕ∞) := hd.le
  refine Scheme.Modules.coherent_devissage_of_support_subset F.support (Stacks0ben.Good k X L d)
    ?_ ?_ ?_ F subset_rfl
  · -- zero objects
    intro G hG hz
    exact Stacks0ben.good_of_isZero k hX L d G hz
  · -- two out of three
    intro S hS h1 h2 h3 hs1 hs2 hs3
    have hadd : ∀ n, Stacks0ben.defect k X L d S.X₂ n
        = Stacks0ben.defect k X L d S.X₁ n + Stacks0ben.defect k X L d S.X₃ n :=
      Stacks0ben.defect_add k hX L d S hS hTc hTd hs1 hs3
    refine ⟨fun ⟨Q₁, hQ₁, e₁⟩ ⟨Q₂, hQ₂, e₂⟩ => ⟨Q₂ - Q₁, Stacks0ben.isLowDegree_sub hQ₂ hQ₁, fun n => ?_⟩,
      fun ⟨Q₁, hQ₁, e₁⟩ ⟨Q₃, hQ₃, e₃⟩ => ⟨Q₁ + Q₃, Stacks0ben.isLowDegree_add hQ₁ hQ₃, fun n => ?_⟩,
      fun ⟨Q₂, hQ₂, e₂⟩ ⟨Q₃, hQ₃, e₃⟩ => ⟨Q₂ - Q₃, Stacks0ben.isLowDegree_sub hQ₂ hQ₃, fun n => ?_⟩⟩
    · rw [MvPolynomial.eval_sub, ← e₁ n, ← e₂ n, hadd n]; ring
    · rw [MvPolynomial.eval_add, ← e₁ n, ← e₃ n, hadd n]
    · rw [MvPolynomial.eval_sub, ← e₂ n, ← e₃ n, hadd n]; ring
  · -- generators
    intro ξ hξT
    obtain ⟨hann, hlen⟩ := Scheme.Modules.pushforward_unit_pointClosure_stalk (X := X) ξ
    refine ⟨Scheme.Modules.pointClosureUnitPushforward ξ,
      Scheme.Modules.pointClosureUnitPushforward_isCoherent ξ,
      Scheme.Modules.pointClosureUnitPushforward_support ξ, hann, hlen, ?_⟩
    have hGcoh := Scheme.Modules.pointClosureUnitPushforward_isCoherent (X := X) ξ
    have hGsupp := Scheme.Modules.pointClosureUnitPushforward_support (X := X) ξ
    -- `dim closure{ξ} ≤ d`
    have hξsub : (closure {ξ} : Set X) ⊆ F.support :=
      hTc.closure_subset_iff.mpr (Set.singleton_subset_iff.mpr hξT)
    have hξle : topologicalKrullDim (closure {ξ} : Set X) ≤ (d : WithBot ℕ∞) :=
      le_trans (Stacks0ben.topologicalKrullDim_mono hξsub) hTd
    -- multiplicities of `G` vanish at points outside `closure {ξ}`
    have hmult0 : ∀ η, η ∉ (closure {ξ} : Set X) →
        Stacks0ben.mult X (Scheme.Modules.pointClosureUnitPushforward ξ) η = 0 := fun η hη =>
      Stacks0ben.mult_eq_zero_of_notMem_support _ (hGsupp ▸ hη)
    rcases lt_or_eq_of_le hξle with hlt | heq
    · -- `dim closure{ξ} < d`: Snapper's theorem 0BEM with `e = dim closure{ξ}`
      have hh : topologicalKrullDim (closure {ξ} : Set X) = ((Order.height ξ : ℕ∞) : WithBot ℕ∞) :=
        (AlgebraicGeometry.Intersection.pointClosureDimension_eq_topologicalKrullDim_closure X ξ).symm
      have hlt' : ((Order.height ξ : ℕ∞) : WithBot ℕ∞) < (d : WithBot ℕ∞) := hh ▸ hlt
      have hlt'' : Order.height ξ < (d : ℕ∞) := by exact_mod_cast hlt'
      have hne : Order.height ξ ≠ ⊤ := ne_top_of_lt hlt''
      set e : ℕ := (Order.height ξ).toNat with he
      have hecoe : (e : ℕ∞) = Order.height ξ := ENat.natCast_toNat hne
      have hed : e < d := by
        have : (e : ℕ∞) < (d : ℕ∞) := hecoe ▸ hlt''
        exact_mod_cast this
      have hdimG : topologicalKrullDim (Scheme.Modules.pointClosureUnitPushforward ξ).support
          ≤ (e : WithBot ℕ∞) := by
        rw [hGsupp, hh, ← hecoe]
        norm_cast
      obtain ⟨P, hPdeg, hP⟩ := AlgebraicGeometry.exists_snapper_mvPolynomial X hX
        (Scheme.Modules.pointClosureUnitPushforward ξ) L e hdimG
      refine ⟨P, Stacks0ben.isLowDegree_of_totalDegree_le hPdeg hed, fun n => ?_⟩
      -- no `d`-dimensional point lies in `closure {ξ}`
      have hvanish : ∀ η, topologicalKrullDim (closure {η} : Set X) = (d : WithBot ℕ∞) →
          Stacks0ben.mult X (Scheme.Modules.pointClosureUnitPushforward ξ) η
            * Stacks0ben.componentChi k X L η n = 0 := by
        intro η hη
        rw [hmult0 η, zero_mul]
        intro hmem
        have : topologicalKrullDim (closure {η} : Set X) ≤ topologicalKrullDim (closure {ξ} : Set X) :=
          Stacks0ben.topologicalKrullDim_mono
            (isClosed_closure.closure_subset_iff.mpr (Set.singleton_subset_iff.mpr hmem))
        exact absurd (lt_of_le_of_lt (hη ▸ this) hlt) (lt_irrefl _)
      have hzero := Stacks0ben.finsum_dim_eq_zero (X := X) (d := d)
        (fun η => Stacks0ben.mult X (Scheme.Modules.pointClosureUnitPushforward ξ) η
          * Stacks0ben.componentChi k X L η n) hvanish
      unfold Stacks0ben.defect
      rw [hzero, sub_zero]
      exact hP n
    · -- `dim closure{ξ} = d`: `E(i_* O_{Z_ξ}) = 0`
      refine ⟨0, Stacks0ben.isLowDegree_zero d, fun n => ?_⟩
      rw [map_zero]
      set Z := AlgebraicGeometry.Scheme.pointClosure ξ with hZ
      set i := AlgebraicGeometry.Scheme.pointClosureι ξ with hi
      letI : Z.Over (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
        ⟨i ≫ (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩
      haveI : i.IsOver (AlgebraicGeometry.Spec (CommRingCat.of k)) := ⟨rfl⟩
      -- the sum has the single term `ξ`, with multiplicity `1`
      have hsum : (∑ᶠ (η : X) (_ : topologicalKrullDim (closure {η} : Set X) = (d : WithBot ℕ∞)),
          Stacks0ben.mult X (Scheme.Modules.pointClosureUnitPushforward ξ) η
            * Stacks0ben.componentChi k X L η n)
          = Stacks0ben.componentChi k X L ξ n := by
        rw [Stacks0ben.finsum_dim_eq_single _ ξ heq]
        · unfold Stacks0ben.mult
          rw [hlen]
          simp
        · intro η hηξ hηd
          -- a `d`-dimensional point of `closure {ξ}` is `ξ` itself
          by_cases hmem : η ∈ (closure {ξ} : Set X)
          · exact absurd (Stacks0ben.eq_of_mem_closure_of_dim_closure_eq heq hηd hmem) hηξ
          · rw [hmult0 η hmem, zero_mul]
      -- `χ(X, i_* O_Z ⊗ L^n) = χ(Z, (i^*L)^n)`
      have hχ : (AlgebraicGeometry.sheafEulerCharacteristic (k := k) X
          (Scheme.Modules.twistList (fun j => L j ^ n j) (List.finRange r)
            (Scheme.Modules.pointClosureUnitPushforward ξ)) : ℚ)
          = Stacks0ben.componentChi k X L ξ n := by
        unfold Stacks0ben.componentChi
        congr 1
        rw [AlgebraicGeometry.sheafEulerCharacteristic_eq_of_iso
            (Scheme.Modules.twistList_pushforward_iso i (fun j => L j ^ n j) (List.finRange r)
              (SheafOfModules.unit Z.ringCatSheaf)),
          ← AlgebraicGeometry.sheafEulerCharacteristic_closedImmersion i]
        exact AlgebraicGeometry.sheafEulerCharacteristic_eq_of_iso
          (Stacks0ben.twistListFamilyIso
            (fun j => (AlgebraicGeometry.Scheme.Modules.pullback_linePow i (L j) (n j)).2.some)
            (List.finRange r) (SheafOfModules.unit Z.ringCatSheaf))
      unfold Stacks0ben.defect
      rw [hsum, hχ, sub_self]

end
