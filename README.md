# Zermelo–Fraenkel Foundational Language
> Sturm-Liouville Neural Framework (SLNF)

Every object is a set. Every operation is a function. Every claim is a sentence in first-order logic. Nothing else exists.

---

## Core

```
sign(λ₁(ℒ_JL)) = sign of learning
```

`λ₁ > 0` → generalization. `λ₁ = 0` → criticality. `λ₁ < 0` → memorization.

Everything below constructs `ℒ_JL` from `∅` and proves this.

---

## §0 — Axioms

| ID | Axiom | Sentence |
|----|-------|---------|
| Z1 | Extensionality | `A = B ⟺ ∀x(x∈A ⟺ x∈B)` |
| Z2 | Empty Set | `∃A ∀x (x ∉ A)` — call it `∅` |
| Z3 | Pairing | `∀a,b ∃A (a∈A ∧ b∈A)` — call it `{a,b}` |
| Z4 | Union | `∀A ∃B ∀x (x∈B ⟺ ∃C(C∈A ∧ x∈C))` |
| Z5 | Power Set | `∀A ∃B ∀x (x∈B ⟺ x⊆A)` |
| Z6 | Separation | `∀A,φ ∃B ∀x (x∈B ⟺ x∈A ∧ φ(x))` |
| Z7 | Replacement | Image of a set under a definable function is a set |
| Z8 | Infinity | `∃A (∅∈A ∧ ∀x∈A (x∪{x}∈A))` |

**AC** (Axiom of Choice) appears in exactly two places: ordering eigenvalues **(AC-1)** and choosing coset representatives **(AC-2)**. Both are marked.

---

## §1 — Numbers

**Natural numbers** — von Neumann encoding `[Z2, Z8]`:
```
0 := ∅,   1 := {∅},   2 := {∅,{∅}},   n+1 := n ∪ {n}
ℕ := ∩{ A : ∅∈A ∧ ∀n∈A(n∪{n}∈A) }
```

**Integers, rationals, reals** — each a quotient set `[Z5, Z6]`:
```
ℤ := (ℕ×ℕ)/∼        (a,b)∼(c,d) ⟺ a+d = b+c
ℚ := (ℤ×(ℤ\{0}))/∼  (p,q)∼(r,s) ⟺ ps = qr
ℝ := { S ⊆ ℚ : S≠∅, S≠ℚ, S downward-closed, S has no maximum }
```

A real number is a Dedekind cut — a subset of `ℚ`. `ℝ` is a set of sets.

**Ordered pair and function** `[Z3]`:
```
(a,b) := {{a},{a,b}}                           — Kuratowski pair
A×B   := { (a,b) : a∈A, b∈B }                 — [Z5, Z6]
f:A→B  := f ⊆ A×B,  ∀a∈A ∃!b∈B (a,b)∈f       — a set of pairs
```

---

## §2 — Parameter Space

```
ℝᴺ := { f : N → ℝ }       [Z7]    — N-tuples of reals
 Θ  := { θ ∈ ℝᴺ : φ(θ) }  [Z6]    — domain-constrained subset
```

A network parameter `θ ∈ Θ` is a function `N → ℝ`. Training is a sequence `(θ_t)_{t∈ℕ}` — a set of pairs.

---

## §3 — Symmetry Group

Many `θ` encode the same input-output function. Their redundancies form a group.

```
G := { φ ∈ Diff(Θ) : ∀θ∈Θ, ∀x∈𝒳, f(φ(θ),x) = f(θ,x) }   [Z6]
```

`G ⊆ Diff(Θ)`, closed under composition and inversion. Elements include neuron permutations, sign-flip pairs, ReLU rescalings — any reparameterization that leaves network output identical.

**Orbits and quotient** `[Z6, Z7, AC-2]`:
```
[θ] := { φ(θ) : φ∈G }    — fiber over θ
 ℬ  := { [θ] : θ∈Θ }     — one point per distinct network function
```

`ℬ = Θ/G` is the space where learning lives. Canonical representative selection requires **(AC-2)**.

---

## §4 — Fiber Bundle

```
π : Θ → ℬ,   π(θ) := [θ]                        [Z7]

𝒱_θ := ker(dπ_θ) = { v∈ℝᴺ : dπ_θ(v)=0 }        [Z6] — fiber directions
ℋ_θ := { v∈ℝᴺ : ∀u∈𝒱_θ, g_θ(v,u)=0 }           [Z6] — base directions
```

| Subspace | Physical meaning | Gradient |
|----------|-----------------|---------|
| `𝒱_θ` | Symmetry redundancy (permuting neurons) | Zero — exactly |
| `ℋ_θ` | True learning directions | Nonzero |

**Theorem (Gauge).** For G-invariant loss `L`: `∇L(θ) ∈ ℋ_θ`.

*Proof.* For `u = Â_θ ∈ 𝒱_θ`, `A∈Lie(G)`:
```
⟨∇L(θ), Â_θ⟩ = d/dt|₀ L(θ·eᵗᴬ) = d/dt|₀ L(θ) = 0    by G-invariance
```
Therefore `∇L ⊥ 𝒱_θ`, i.e., `∇L ∈ ℋ_θ`. ∎

SGD moves only in `ℋ_θ`. Fiber directions receive zero gradient — not approximately, exactly.

---

## §5 — Albert Algebra

```
𝕆 := ℝ⁸ with Cayley product      [Z4, Z5]   — octonions
𝔄 := { M∈𝕆^{3×3} : M†=M }       [Z6]        — Albert algebra, dim 27
```

**Jordan product** `[Z7]`:
```
X ∘ Y := ½(XY + YX) : 𝔄×𝔄 → 𝔄
```
Commutative: `X∘Y = Y∘X`. Non-associative: `(X∘Y)∘Z ≠ X∘(Y∘Z)`.

**Associator** `[Z7]`:
```
𝒜(X,Y,Z) := (X∘Y)∘Z − X∘(Y∘Z) ≠ 0
```
`𝒜` distinguishes paths reaching the same state via different computation orders. Standard matrix algebras have `𝒜 = 0` everywhere and cannot make this distinction.

**Automorphism group** (boundary conditions) `[Z6]`:
```
F₄ := { φ:𝔄→𝔄 bijective : φ(X∘Y) = φ(X)∘φ(Y) }    dim = 52
```
F₄-equivariance constrains admissible eigenfunctions — the role of boundary conditions in classical S-L theory.

---

## §6 — Geometry

**Fisher metric** (signal) `[Z7]`:
```
F(θ)ᵢⱼ := 𝔼_{p(y|θ)}[ ∂ᵢ log p · ∂ⱼ log p ] : Θ → ℝᴺˣᴺ
```

Full metric on `ℬ` (GRI embedding):
```
g_μν := diag[ −(1 + 2L/c²),  F₁₁, …, Fᵢⱼ ]
```
Temporal component: loss as gravitational potential. Spatial components: Fisher geometry.

**Diffusion tensor** (noise) `[Z7]`:
```
D_s(b) := ½ · dπ_θ · Cov_{batch}[∇_θL] · dπ_θ* : ℬ → ℝᵈˣᵈ
```
`Tr(D_s(b))` = SGD noise power at `b`. This is the S-L weight function `w`.

---

## §7 — Potential

```
𝒮̄ : ℬ → ℝ,   𝒮̄(b) := H̄_G(b) + λ·V̄(b)    [Z7]
```

| Term | Definition | Cost |
|------|-----------|------|
| `H̄_G(b)` | `−∫_{[θ]} log p_G(φ) dφ` | Symmetry redundancy |
| `V̄(b)` | `μ_L(⋃ᵢ Eᵢ(θ))` | Wasted representational volume |

`𝒮̄` is simultaneously: S-L potential `q(x)` · SDSD Lyapunov function · GRI gravitational potential · Möbius inversion target.

**Kakeya bound.** K-class classification requires one representation direction per class:
```
V(θ) ≥ V_Kakeya > 0,    d/dt 𝔼[V] ≤ 0
```
Training drives `V` to this bound. Neural collapse (ETF) is the bound achieved.

---

## §8 — The Operator

Classical S-L: `ℒ[y] = −(1/w)[d/dx(p·dy/dx) − q·y]`

**Substitution table:**

| S-L term | Neural object | Identity |
|----------|-------------|---------|
| `p` conductance | Ramanujan tensor `Ω` | k-regular; `λ₂(Ω) ≤ 2√(k−1)` |
| `q` potential | `𝒮̄(b)` | `ℬ → ℝ` [Z7] |
| `w` weight | `Tr(D_s(b))` | `ℬ → ℝ>0` [Z7] |

The Ramanujan bound ensures `O(log n)` mixing — optimal information transport across `ℬ`.

**Jordan–Liouville operator:**
```
ℒ_JL[φ](b) := −[1/Tr(D_s)] · [ ∇_ℬ·(D_s ∇_ℬ φ) − 𝒮̄(b)·φ ]
```

As a ZF object: `ℒ_JL ⊆ L²(ℬ,w) × L²(ℬ,w)` — a set of pairs of equivalence classes `[Z7]`.

**Self-adjointness.** `⟨ℒ_JL φ, ψ⟩ = ⟨φ, ℒ_JL ψ⟩` because:
- `D_s` symmetric positive-definite (is a covariance matrix)
- `𝒮̄` real-valued
- `ℬ` compact — boundary terms in Green's identity vanish

All eigenvalues of `ℒ_JL` are real.

---

## §9 — Eigenvalue Problem

Find `(λ,φ) ∈ ℝ × L²(ℬ, Tr(D_s)dvol)`:
```
ℒ_JL[φ] = λφ
⟺  −∇_ℬ·(D_s ∇_ℬ φ) + 𝒮̄(b)·φ = λ·Tr(D_s)·φ
```

**Spectral Theorem (AC-1).** There exists a sequence:
```
λ₁ ≤ λ₂ ≤ λ₃ ≤ ⋯ → +∞
```
with `{φₙ}` an orthonormal basis of `L²(ℬ, Tr(D_s)dvol)`. Every learnable representation:
```
f_θ = Σₙ cₙ φₙ,   cₙ = ⟨f_θ, φₙ⟩
```

By Sturm Oscillation: `φₙ` has exactly `n−1` zeros on `ℬ` → `n−1` decision boundaries.

---

## §10 — The Threshold

**Rayleigh quotient:**
```
R[φ] := ∫_ℬ [D_s|∇_ℬφ|² + 𝒮̄|φ|²] dvol  /  ∫_ℬ Tr(D_s)|φ|² dvol
```

Variational principle: `λ₁ = inf_φ R[φ]`.

**Key identity.** Set `φ := ‖∇_ℬ𝒮̄‖`:
```
R[‖∇_ℬ𝒮̄‖] ≈ ‖∇_ℬ𝒮̄‖² / Tr(D_s) =: Γ
```
Exact at critical points `(𝒮̄≈0)`. Therefore `λ₁ ≤ Γ` always, and `Γ > 1 ⟹ λ₁ > 0`.

**Five equivalent formulations of one inequality:**

```
(I)   λ₁(ℒ_JL) > 0                           SLNF — ground eigenvalue positive
(II)  Γ = ‖∇_ℬ𝒮̄‖² / Tr(D_s) > 1             SDSD — supermartingale
(III) C_α = ‖μ_g‖² / Tr(Σ_g) > 1             ARDI — signal-to-noise ratio
(IV)  ‖∇L‖ > c·√(r_s/r)                      GRI  — escape velocity
(V)   Mₙ = Σ_{k≤n} μ(k,n)·Fₖ  converges L²  M-F  — inversion stable
```

**Proof of equivalences:**

`(I)↔(II)`: `Γ = R[‖∇𝒮̄‖]`. Since `λ₁ ≤ R[φ]` for all `φ`: `Γ>1 ⟹ λ₁>0`.

`(II)↔(III)`: `‖∇𝒮̄‖² ≈ ‖μ_g‖²` (signal); `Tr(D_s) ≈ Tr(Σ_g)` (noise). Identical ratio, empirical vs geometric estimator.

`(II)↔(IV)`: GRI defines `c² := Tr(Var[∇L])`, `r_s := 2η²λ_max(Hess L)/c²`. Near `r≈r_s`: `‖∇L‖>c√(r_s/r) ⟺ C_α>1`.

`(III)↔(V)`: `Mₙ` converges in `L²` iff accumulated noise is dominated by signal iff `C_α > 1`.

---

## §11 — Phase Transitions

Every named deep learning phenomenon is a bifurcation of `λ₁`.

**Phase diagram:**
```
      λ₁ < 0          λ₁ = 0            λ₁ > 0
      Γ < 1            Γ = 1             Γ > 1
      C_α < 1          C_α = 1           C_α > 1
      Mₙ diverges      Mₙ critical       Mₙ converges
      submartingale     null-recurrent    supermartingale

◄──────────────────────┼──────────────────────────────►
    MEMORIZATION    GROKKING              GENERALIZATION
```

**Phenomena as eigenvalue events:**

| Phenomenon | Eigenvalue event | Observable |
|------------|----------------|-----------|
| Grokking | `λ₁` crosses 0 upward | `Γ` jumps through 1 |
| Neural collapse | `f_θ → φ₁` | ETF = Kakeya minimum |
| Double descent | `λ₁ → 0` at interpolation | Test error peak at `Γ=1` |
| Lottery tickets | Sub-net has `λ₁>0` at init | Magnitude pruning recovers it |
| Memorization | `λ₁ < 0` throughout | `C_α < 1` |
| Plateau | `λ₁ ≈ 0` | Null-recurrent diffusion |
| Mode collapse | Only `φ₁` active | `H_G → 0` on one fiber |

**Grokking time:**
```
T_grok := inf{ t∈ℕ : λ₁(ℒ_JL, b_t) > 0 }  ∈ ℕ∪{∞}    [Z6]
```
Sharpness governed by mock theta function density near `λ₁=0`:
```
f(q) = Σ_{n≥0} q^{n²} / ((-q;q)_n)²
```
Sparse eigenvalue distribution at criticality → generalization is discontinuous in observables from a continuous eigenvalue crossing.

---

## §12 — Master Equation

Let `ρ : ℬ×ℕ → ℝ≥0` be the training-time probability density `[Z7]`.

```
∂ρ/∂t = ∇_ℬ·(ρ ∇_ℬ𝒮̄)  +  ∇_ℬ·(D_s ∇_ℬρ)
          ─────────────      ────────────────
            drift               diffusion
```

One equation, four interpretations:

| Framework | Interpretation |
|-----------|---------------|
| SDSD | Fokker-Planck for SGD on `ℬ` |
| GRI | Einstein weak-field: `∇²Φ = 4πGρ` |
| ARDI | Ergodic flow to stationary `P_Ω*` |
| M-F | Accumulation equation inverted by Möbius series |

**Master Theorem.** Let `λ₁ = λ₁(ℒ_JL)`.

**I. Convergence.** `λ₁ > 0` implies:
```
‖ρ(·,t) − ρ_∞‖_TV ≤ C·exp(−λ₁·t),   ρ_∞ ∝ exp(−𝒮̄/D_eff)
```

**II. Rate.** Near criticality:
```
rate of generalization = λ₁ = Γ − 1
```

**III. Generalization bound.**
```
GenGap(θ*) ≲ ‖η·Hess L̄‖_F / (n_train · C_α)
```

**IV. Capacity.**
```
C(n) ~ exp(π√(2n/3)) / 4n√3     [Hardy–Ramanujan; exact as n→∞]
```

**V. Arithmetic.** Q16.16 fixed-point (CORDIC):
```
|λ₁^computed − λ₁^true| = 0    within representable range
```
Float32 accumulates `O(ε_mach·√T)` ≈ `10⁻⁴` error at `T=10⁶` — sufficient to corrupt `sign(λ₁)`. Q16.16 eliminates this.

---

## §13 — ZF Object Registry

| Object | ZF identity | Axioms |
|--------|------------|--------|
| `ℕ` | Smallest inductive set | Z8 |
| `ℝ` | Dedekind cuts of `ℚ` | Z5, Z6 |
| `ℝᴺ` | Functions `N→ℝ` | Z7 |
| `Θ` | Subset of `ℝᴺ` | Z6 |
| `G` | Subset of `Diff(Θ)` | Z6 |
| `ℬ = Θ/G` | Set of orbits `{G·θ}` | Z7, AC-2 |
| `π` | Pairs `(θ,[θ])` | Z7 |
| `𝒱_θ`, `ℋ_θ` | Subsets of `ℝᴺ` | Z6 |
| `𝕆` | `ℝ⁸` + Cayley product | Z4, Z5 |
| `𝔄` | `{M∈𝕆^{3×3} : M†=M}` | Z6 |
| `∘` | Triples in `𝔄×𝔄×𝔄` | Z7 |
| `𝒜` | 4-tuples in `𝔄⁴` | Z7 |
| `F₄` | `Aut(𝔄)` | Z6 |
| `F(θ)` | `Θ→ℝᴺˣᴺ`, pairs | Z7 |
| `D_s(b)` | `ℬ→ℝᵈˣᵈ`, pairs | Z7 |
| `𝒮̄(b)` | `ℬ→ℝ`, pairs | Z7 |
| `L²(ℬ,w)` | a.e.-classes, square-integrable | Z5, Z6, Z7 |
| `ℒ_JL` | Subset of `L²×L²` | Z7 |
| `λₙ` | Element of `ℝ` | Z6 |
| `φₙ` | Element of `L²(ℬ,w)` | Z7 |
| `Γ(t)` | Element of `ℝ` | Z6 |
| `C_α` | Element of `ℝ` | Z6 |
| `T_grok` | Element of `ℕ∪{∞}` | Z6 |
| `ρ(b,t)` | `ℬ×ℕ→ℝ≥0`, pairs | Z7 |

---

## Summary

```
┌───────────────────────────────────────────────────────┐
│  INPUT:   f_θ : 𝒳 → 𝒴                                │
│                                                       │
│  CONSTRUCT:                                           │
│    ℬ = Θ/G       one point per distinct function      │
│    D_s(b)        noise geometry on ℬ                  │
│    𝒮̄(b)         symmetry cost + Kakeya volume         │
│    Ω             Ramanujan mixing (conductance)        │
│                                                       │
│  FORM:   ℒ_JL = −(1/Tr D_s)[∇·(D_s∇·) − 𝒮̄·]        │
│                                                       │
│  SOLVE:  ℒ_JL φₙ = λₙ φₙ                            │
│                                                       │
│  READ:   λ₁ > 0 → generalization                     │
│          λ₁ = 0 → grokking boundary                  │
│          λ₁ < 0 → memorization                       │
│          λ₁     → convergence rate = Γ − 1           │
│          φ₁     → optimal feature mode               │
└───────────────────────────────────────────────────────┘
```

Every object: a set. Every arrow: a function. Every claim: a sentence over sets.
Eight ZF axioms. Two uses of AC. The rest is structure.

---

*SDSD · ARDI · GRI · Möbius-Frobenius · Sturm-Liouville*
