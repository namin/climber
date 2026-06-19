# climber

A reasonable-reflection artifact in the Beklemishev shape: a system
whose **logical strength climbs under proposer/gate control**, with
each rung kernel-blessed by an independent metalanguage soundness
certificate.

> **LCF checks theorem construction; climber checks theory
> construction.**

The proposer (an LLM, in the full version) does not propose theorems
or tactics. It proposes **new sound axiom-schema extensions** —
schemas with soundness certificates — and the kernel admits or
refuses based on whether the certificate type-checks against the
metalanguage interp. Admitted extensions enter the theory; new
theorems become derivable; the system has climbed.

This is the LCF discipline, applied not to proof construction but
to **proof-system construction**. In the keynote portfolio:

| artifact | what the gate governs |
|---|---|
| lean-grey | evaluator modification |
| lean-green | causal `set!` on a heap cell |
| LeanDisco | discovery of theorems and heuristics |
| sc-mini | program-transformation rewrites |
| **climber** | **the right to extend the proof system itself** |

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
  - `Formula.heyting`: interpretation into H3, parameterized over
    a `provVal` assignment for `prov φ` atoms.
  - `Derivable₀.h3Valid`: every T₀-derivable formula evaluates to
    top under any H3 environment and any `provVal`. K, S, ⊥-elim
    valid; MP preserves.
  - `counterEnv`, `counterProvVal`: the assignment used for Peirce.
  - `peirce_h3_value`: Peirce evaluates to `mid`.
  - `peirce_not_derivable_in_T₀`: corollary — `¬ Derivable₀ peirce`.
- **`Climber/Reflection.lean`** — internal RFN(T₀) and Con(T₀).
  - `rfn0Schema`: the Beklemishev-shape schema admitting any
    formula of the form `prov φ → φ`.
  - `rfn0Extension`: the SoundExtension whose certificate is
    `soundness₀` itself — RFN(T₀) is sound iff T₀ is sound.
  - `T₁_rfn`: T₀ extended with RFN(T₀).
  - `consistencyFormula`: `prov ⊥ → ⊥`, i.e., Con(T₀).
  - `T₁_rfn_derives_con`: T₁_rfn derives Con(T₀) via the RFN
    instance at φ = ⊥.
  - `T₁_rfn_sound`: corollary of `climb_sound`.
  - `con_not_derivable_in_T₀`: H3 countermodel shows T₀ provably
    cannot reach Con(T₀). The Beklemishev rung made formal.
- **`Climber/Bedrock.lean`** — AWS Bedrock invoke wrapper for the
  LLM proposer. Defaults to `claude-sonnet-4-6` in `us-east-1`.
- **`Climber/Elab.lean`** — splices an LLM `SoundExtension` term
  into a wrapper file. Outcomes: `ADMITTED` (the kernel verified
  the `sound` field type-checks against the metalanguage interp;
  the schema enters the climbed theory) or `ELAB-ERROR`
  (compilation failed; the diagnostic is fed back).
- **`Climber/Runner.lean`** — orchestrates the cascade. Each
  round prompts Claude for an EXTENSION, classifies, retries on
  elab errors. After each non-error round the runner regenerates
  `Climbed.lean` containing the accumulated extensions and a
  composite theory `T_climbed`, then verifies that `Climbed.lean`
  elaborates. Unreachable-line claims are *not* part of the
  cascade verdict — they live in the static artifact
  (`peirce_not_derivable_in_T₀`, `con_not_derivable_in_T₀`).
- **`Smoke.lean`** — `lake exe smoke`. Reports the load-bearing
  facts at runtime; the kernel did the verification at compile
  time.
- **`BedrockSmoke.lean`** — `lake exe bedrock-smoke`. One-shot
  Bedrock connectivity check.
- **`RunnerMain.lean`** — `lake exe runner [N]`. Runs `N` rounds
  of the LLM/Lean cascade (default 3). Each admitted extension
  enters the accumulated `T_climbed` as a kernel-blessed sound
  axiom-schema; after each round, `Climbed.lean` is regenerated
  and verified.
- **`Climbed.lean`** — *generated*. The accumulated kernel-blessed
  composite theory written by the runner across rounds. A
  committed snapshot serves as evidence of a particular run; any
  fresh run will overwrite it.

## Status

- **Builds clean** on `leanprover/lean4:v4.30.0`. `lake build`
  finishes in seconds.
- **Zero sorries.** All headline results — `climb_sound`,
  `climb_consistent`, `T₁_derives_peirce`, `T₁_sound`, `peirceSound`,
  `soundness₀`, `Derivable₀.h3Valid`, `peirce_not_derivable_in_T₀`,
  `T₁_rfn_derives_con`, `T₁_rfn_sound`, `con_not_derivable_in_T₀` —
  are fully proved.
- **The climb crosses an unreachable line, twice.** The Peirce
  rung shows the architecture works for sound axiom-schema
  extension. The RFN rung shows it works for *internal reflection*:
  T₁_rfn derives Con(T₀), T₀ provably cannot.
- **The cascade is interactive.** `lake exe runner` runs the
  proposer/gate loop end-to-end against AWS Bedrock; the LLM
  proposes `SoundExtension` terms; the kernel checks the
  soundness certificate; admitted extensions accumulate into
  `Climbed.lean` (regenerated and re-verified after every round).
  The unreachable-line claims live in the static artifact, not in
  the cascade verdict.
- **Honest scope.** This is the *propositional, one-rung skeleton*
  of a reflection progression — not a formalization of Beklemishev's
  full hierarchy. The architecture is right; the engineering to
  iterate (level-indexed `prov`, stratified Π_n reflection,
  ordinal analysis) is sketched in the *Path to iterated
  reflection-principle climbing* section below.

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

### A note on the H3 separating model

`Counter.lean`'s 3-element Heyting algebra is used in two ways
that are worth distinguishing.

The `prov` constructor has an **intended interpretation** — under
`interp`, `prov φ` reduces to the metalanguage proposition
`Derivable₀ φ`. This is the interpretation under which `soundness₀`
holds and under which RFN(T₀) is sound.

The H3 model uses an **arbitrary `provVal` assignment**. This is
*not* an intended interpretation; it is a *separating model* for
T₀'s syntactic proof calculus. Since T₀ has no rule introducing
`prov`, every T₀-derivable formula is H3-valid for *any* `provVal`,
which is what makes the model a separator: any single `provVal`
that makes a target formula H3-invalid is enough to rule out
T₀-derivability.

The asymmetry is not a defect. It is the architecture: the gate
connects the inert object-level `prov` to its intended metalanguage
meaning (for soundness), while the H3 separator certifies syntactic
non-derivability without committing to any single interpretation
(for the unreachable-line claims). Different jobs, different
models, both kernel-checked.

## Path to iterated reflection-principle climbing

The present artifact has the Beklemishev rung at level 1: T₁_rfn
derives Con(T₀) via an internal RFN(T₀) schema with soundness₀ as
the certificate. The path forward is *iteration* — admitting
RFN(T₁_rfn) at level 2, RFN(T₂) at level 3, and so on, climbing
through the Beklemishev hierarchy.

The remaining gaps:

1. **Internal provability predicate per rung.** At level 1, the
   `prov` constructor in `Formula` is hard-coded to T₀ via
   `interp env (.prov φ) := Derivable₀ φ`. To climb past T₁_rfn we
   need `prov` to be indexed by a level — `prov (n : Nat) (φ : Formula)`
   — and the interpretation parameterized over a sequence of theories.
   ~50 LOC of refactoring.

2. **Soundness lemma per rung.** Each rung n+1's RFN extension
   needs the soundness theorem of T_n. For T₀ this is `soundness₀`.
   For T₁_rfn it's `T₁_rfn_sound` (already proved as a corollary of
   `climb_sound`). General: each rung's soundness comes free from
   `climb_sound` once `prov` and `interp` are level-indexed.

3. **Stratification (Π_n reflection).** The full Beklemishev
   hierarchy stratifies reflection by formula complexity, giving
   finite presentations at each level. Required for transfinite
   ordinals; not required for finite-rung demos. Engineering, not
   research.

Each of these is finite work. The architectural claim — that a
kernel-checked metalanguage soundness certificate is the right gate
for theory extension, including for internal reflection principles —
is already demonstrated by `climb_sound` together with
`T₁_rfn_derives_con` and `con_not_derivable_in_T₀`.

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

## Running the cascade

The LLM/Lean cascade requires the `aws` CLI on PATH with
Bedrock-enabled credentials. With those in place:

```bash
lake exe bedrock-smoke    # one-shot connectivity check
lake exe runner           # 3 rounds (default)
lake exe runner 10        # 10 rounds
```

Each round, Claude proposes an **EXTENSION** — a `SoundExtension`
term (schema + soundness certificate). One gate runs: the
extension must elaborate. On success, `ADMITTED` — the kernel
verified the soundness certificate, the schema enters the
accumulated climbed theory. On failure, `ELAB-ERROR` with Lean's
diagnostic fed back for one retry.

After every non-error round, the runner regenerates `Climbed.lean`
containing all admitted extensions as `round_0`, `round_1`, … and
a composite theory
`T_climbed := Theory.base.extend round_0.extend round_1…`, plus
`T_climbed_sound` as a corollary of `climb_sound`. The runner
verifies `Climbed.lean` elaborates after writing it. The file is
**replayable evidence** that the cascade-built theory is sound:
the accumulated `SoundExtension`s and the soundness corollary
survive `lake env lean Climbed.lean`.

A typical run admits classical schemas like Peirce's law
`((φ → ψ) → φ) → φ`, double-negation elimination
`((φ → ⊥) → ⊥) → φ`, or consequentia mirabilis
`((φ → ⊥) → φ) → φ`.

**Where the unreachable-line claims live.** The cascade does not
verdict on T₀-non-derivability. Those claims are in the static
artifact: `peirce_not_derivable_in_T₀` (in `Counter.lean`) and
`con_not_derivable_in_T₀` (in `Reflection.lean`) prove the climb
crossed unreachable lines via H3 separating models — kernel-
checked, independent of any cascade run. The cascade is the same
proposer/gate soundness loop made interactive; the headline
"unreachable line crossed" sentences in the talk are anchored by
the static theorems, not by cascade verdicts.

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
