import Hunter.Words
import Hunter.Graph
import Hunter.Paths
import Hunter.Transform
import Hunter.Bounds

/-!
# Hunter, *A New Lower Bound for Superpermutations* — definitions (umbrella module)

Faithful Lean 4 formalization of the *definitions* of Zach Hunter's unpublished draft, per
`DIGEST.md`.  Statements and proofs of the theorems live in `Hunter/Statements.lean` and the
`Proofs*.lean` modules; see `AMBIGUITIES.md` for every place where the paper underdetermines
a formal choice.

* `Hunter.Words`     — §2.2: permutation words, overlap weight `wt = w`, the successors
                       `σ = rho`, `τ = door`, `α = alphaWord`; rotation classes.
* `Hunter.Graph`     — §2.2–2.3: the complete weighted digraph `𝒮_k` on vertices `Vtx k`;
                       `w`, `σ`,`τ`,`α` as vertex maps; the 1-cycle `c(v)`; edge sets,
                       `into`/`out`, heads `H`/tails `T`, `w(S)`.
* `Hunter.Paths`     — §2.4–2.5: vertex-simple paths `HPath`, length/weight, early exit,
                       (strongly) exitless, `minto`; Hamiltonian paths.
* `Hunter.Transform` — §4–§6: `C₀`,`C₋₁`, `S(P)`, `f(P,S)`, `F`, `E₁`,`E₂`, the indicator
                       `I`; weak components `Comps`, `MinThrough`; `𝒳_k`, `𝒳'_k`.
* `Hunter.Bounds`    — §2.6, §6: `L(k)`, `L*(k)`, `S(k)`; `i_k(ℓ)`, `ℓ₀`, `j_k(ℓ)`, `R_k`.
-/
