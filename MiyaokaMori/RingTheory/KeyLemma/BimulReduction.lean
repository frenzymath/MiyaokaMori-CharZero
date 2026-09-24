import MiyaokaMori.Prelude

/-! # Bimultiplicative reduction for the Key Lemma

The abstract bimultiplicative reduction (the whole content of the proof of Stacks 0EAX): if
`Φ_q : G × G → M` is multiplicative in both variables and pointwise of finite support, and `S ⊂ G` is
such that every `f ∈ G` can be written as `s/s′` (`s, s′ ∈ S`), then `∏_q Φ_q(s, s′) = 1` for all
`s, s′ ∈ S` implies `∏_q Φ_q(f, g) = 1` for all `f, g ∈ G`.

Reference: the proof of Stacks 0EAX ("bilinear … additive … suffices to prove the formula when f and
g are elements of A").
-/

set_option autoImplicit false

universe u v w

namespace KeyLemma

theorem finprod_eq_one_of_bimul {ι : Type u} {G : Type v} {M : Type w} [CommGroup G] [CommMonoid M]
    (Φ : ι → G → G → M)
    (hl : ∀ q f f' g, Φ q (f * f') g = Φ q f g * Φ q f' g)
    (hr : ∀ q f g g', Φ q f (g * g') = Φ q f g * Φ q f g')
    (hfin : ∀ f g, (Function.mulSupport fun q => Φ q f g).Finite)
    (S : Set G) (hS : ∀ f : G, ∃ s ∈ S, ∃ s' ∈ S, f * s' = s)
    (h1 : ∀ s ∈ S, ∀ s' ∈ S, ∏ᶠ q, Φ q s s' = 1) (f g : G) : ∏ᶠ q, Φ q f g = 1 := by
  have Pl : ∀ f f' g, ∏ᶠ q, Φ q (f * f') g = (∏ᶠ q, Φ q f g) * ∏ᶠ q, Φ q f' g := fun f f' g => by
    rw [← finprod_mul_distrib (hfin f g) (hfin f' g)]
    exact finprod_congr fun q => hl q f f' g
  have Pr : ∀ f g g', ∏ᶠ q, Φ q f (g * g') = (∏ᶠ q, Φ q f g) * ∏ᶠ q, Φ q f g' := fun f g g' => by
    rw [← finprod_mul_distrib (hfin f g) (hfin f g')]
    exact finprod_congr fun q => hr q f g g'
  -- first fix `s ∈ S` and free the second variable
  have hs : ∀ s ∈ S, ∀ g, ∏ᶠ q, Φ q s g = 1 := fun s hs g => by
    obtain ⟨t, ht, t', ht', e⟩ := hS g
    have := Pr s g t'
    rw [e, h1 s hs t ht, h1 s hs t' ht', mul_one] at this
    exact this.symm
  obtain ⟨s, hsS, s', hs'S, e⟩ := hS f
  have := Pl f s' g
  rw [e, hs s hsS g, hs s' hs'S g, mul_one] at this
  exact this.symm

end KeyLemma
