# climber

A reasonable-reflection artifact in the Beklemishev shape: a system
whose **logical strength climbs under proposer/gate control**, with
each rung kernel-blessed by an independent metalanguage soundness
certificate.

The proposer (an LLM, in the full version) does not propose theorems
or tactics. It proposes **new derivation rules** — soundness
extensions to the active theory — and supplies a soundness proof in
the metalanguage. The kernel checks the proof. If it type-checks,
the rule enters the theory and new theorems become derivable. If
not, refused.

This is the LCF discipline, applied not to proof construction but
to **proof-system construction**.

## What lives here

- **`Climber/Object.lean`** — the object theory T₀.
  - `Formula`: ⊥, atom, imp.
  - `interp`: standard truth-functional interpretation in Lean's
    metalanguage.
  - `Derivable₀`: minimal Hilbert system — K, S, ⊥-elim, MP.
    The implicational fragment of intuitionistic propositional
    logic plus ex falso quodlibet.
  - `soundness₀`: every Derivable₀ formula is metalanguage-true.
- **`Climber/Climb.lean`** — the climb infrastructure.
  - `SoundExtension`: a schema (predicate on formulas) + a soundness
    certificate (a Lean term of the soundness type). The certificate
    is what the kernel checks at admission.
  - `Theory`: list of admitted extensions on top of T₀.
  - `derives T`: closure of T₀ + admitted schemas under MP.
  - `climb_sound`: **headline metatheorem.** Every theory built by
    climbing preserves metalanguage truth. By induction over the
    derivation, with each admitted-extension case discharged by the
    extension's own `sound` field. Fully proved, no sorry.
  - `climb_consistent`: corollary — no climbed theory derives ⊥.
- **`Climber/Demo.lean`** — one rung, end-to-end.
  - `peirceFormula`: Peirce's law `((p → q) → p) → p`.
  - `peirceSound`: classical truth of Peirce by `Classical.em`. This
    is the certificate the kernel checks.
  - `peirceExtension`: the proposed `SoundExtension`.
  - `T₁ := T₀.extend peirceExtension`.
  - `T₁_derives_peirce`: T₁ derives any instance of Peirce's law.
  - `T₁_sound`: corollary of `climb_sound`.
- **`Climber/Counter.lean`** — countermodel showing T₀ does not
  derive Peirce.
  - `H3`: 3-element linear Heyting algebra `{bot < mid < top}`.
  - `Formula.heyting`: interpretation into H3.
  - `Derivable₀.h3Valid`: every T₀-derivable formula evaluates to
    top under any H3 environment. K, S, ⊥-elim valid; MP preserves.
  - `counterEnv`: the assignment `p ↦ mid, _ ↦ bot`.
  - `peirce_h3_value`: Peirce evaluates to `mid` under `counterEnv`.
  - `peirce_not_derivable_in_T₀`: corollary — `¬ Derivable₀ peirce`.
- **`Smoke.lean`** — `lake exe smoke`. Reports the load-bearing
  facts at runtime; the kernel did the verification at compile
  time.

## Status

- **Builds clean** on `leanprover/lean4:v4.29.1`. `lake build`
  finishes in seconds.
- **Zero sorries.** `climb_sound`, `climb_consistent`,
  `T₁_derives_peirce`, `T₁_sound`, `peirceSound`, `soundness₀`,
  `Derivable₀.h3Valid`, `peirce_not_derivable_in_T₀` are all fully
  proved.
- **The climb crosses an unreachable line.** The countermodel
  proves T₀ provably cannot reach Peirce; the admitted Peirce
  extension makes T₁ derive it; `climb_sound` keeps T₁ sound.

## What this demonstrates

**The climb crosses a provably unreachable line, and stays sound.**
T₀ is shown by the H3 countermodel to be incapable of deriving
Peirce's law (`peirce_not_derivable_in_T₀`). The proposer offers
Peirce as a `SoundExtension` with a kernel-checked classical truth
certificate; T₁ now derives it (`T₁_derives_peirce`); the headline
`climb_sound` carries T₀'s metalanguage truth across to T₁
(`T₁_sound`). Three theorems, one rung — the system's logical
strength has provably grown without leaving the metalanguage's
truth.

The architecture: **proposer/gate-controlled extension of a formal
system's derivation calculus, with metalanguage soundness preserved
across the climb.**

- Smith's reflective tower could mutate the evaluator but had no
  way to verify the mutation. The climber's analogue is `derives`,
  and the gate is the kernel's check on each `SoundExtension`'s
  certificate.
- LCF tactics produce theorems gated by a kernel; the climber
  produces *theories* gated by the same kernel.
- Beklemishev's hierarchy is a *theorem* about which extensions of
  PA are conservative / sound. The climber is an *artifact* that
  navigates such hierarchies — with a proposer choosing which
  extension to add and a kernel checking the navigation step.

## Path to genuine reflection-principle climbing

The present artifact instantiates the architecture at its simplest
mode: admit a new sound *axiom schema*. The keynote-grade story is
the *Beklemishev-shaped* climb: at each rung, admit `RFN(T_n)`
where `T_n` is the previous theory.

To get there, the gaps are:

1. **Internal provability predicate.** The current `Derivable₀` is
   a Lean inductive `Prop` — fine for the metalanguage, but RFN(T_n)
   in the standard sense quantifies over an *internal* `Prov_T_n`
   predicate encoded as a formula of the object language. This
   requires a Gödel encoding of `Derivable_n` derivations as terms.
   ~200–400 LOC depending on how aggressively engineered.

2. **Object-language reflection schema.** Once `Prov_T_n(⌜φ⌝)` is
   a formula, the schema `Prov_T_n(⌜φ⌝) → φ` can be admitted as a
   `SoundExtension` whose `sound` field is the metalanguage soundness
   theorem of T_n. This is exactly what we have now — just at the
   internal-provability level rather than the metalanguage-level.

3. **Iterating the climb.** T_2 needs `Prov_T_1`, which mentions
   the rules admitted at rung 1. The standard Beklemishev trick —
   stratification by formula complexity (Π_n reflection) — keeps
   this finite at each rung.

Each of these is a finite engineering task, not a research problem.
The core architectural claim — that a kernel-checked metalanguage
soundness certificate is the right gate for theory extension — is
already demonstrated by `climb_sound` in the present development.

## Relationship to the rest of the keynote portfolio

- **lean-grey** governs reflective modifications via a parametric
  policy table; `installPolicy` is itself reflective. Climber is
  in the same architectural family — both are proposer/gate
  systems with kernel-checked admission — but the modified object
  is different. lean-grey modifies the apply rule of an evaluator;
  climber modifies the rule set of a derivation calculus.
- **lean-green** realizes Smith's "meta-level is data" via real
  heap mutation. Climber's analogue is the `Theory.extras` list,
  which grows by `extend`; the `SoundExtension` admitted at each
  step is the `set!`-equivalent.
- **LeanDisco** discovers theorems and heuristics with kernel
  verification. Climber discovers *derivation rules* — a deeper
  reflective layer.
- **sc-mini** is the proposer/gate pattern in a non-reflective
  substrate. Climber is the pattern at the deepest reflective
  layer — modifying the system's idea of what counts as a proof.

The climber is the artifact that puts *self-governance with
monotone soundness* on the table as a working system, not a
research wish.

## Build

```bash
lake build       # builds the library
lake build smoke # builds the smoke executable
lake exe smoke   # runs it
```

## References

- Feferman 1962, *Transfinite Recursive Progressions of Axiomatic
  Theories.* The original construction of climbing theories by
  iterated reflection.
- Beklemishev 2005, *Provability Algebras and Proof-Theoretic
  Ordinals.* The modern proof-theoretic account of the hierarchy
  the climber walks.
- Smith 1984, *Reflection and Semantics in LISP.* The reflective
  architecture climber's `Theory` extends.
- Milner 1972 / LCF lineage. The kernel discipline climber's
  admission gate instantiates.
- Heyting 1930. The 3-element linear Heyting algebra used in
  `Counter.lean` to separate intuitionistic from classical
  implicational logic.
