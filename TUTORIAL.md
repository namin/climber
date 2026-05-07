# climber — tutorial

A hands-on walkthrough. Start at zero, end with a kernel-blessed
climbed theory you've extended yourself. ~30 minutes if you don't
get distracted by the literature.

The README explains *why*. This file explains *how* — what to type,
what to look at, what each step proves.

## What you'll learn

By the end you'll be able to:

- Build the artifact and run the smoke test.
- Read the four headline theorems (`soundness₀`, `climb_sound`,
  `peirce_not_derivable_in_T₀`, `T₁_rfn_derives_con`) and say
  what each one buys you.
- Walk a single climbing rung end-to-end: a sound extension, a
  schema, an admitted theorem, a corollary.
- Optionally run the live LLM/Lean cascade against AWS Bedrock and
  inspect the kernel-buildable composite theory it leaves behind.
- Add your own climbing rung — a new `SoundExtension` admitted at
  compile time.

## Prerequisites

- Lean 4 toolchain via `elan`. The artifact pins
  `leanprover/lean4:v4.29.1` in `lean-toolchain`; first
  `lake build` will fetch it automatically.
- (Optional, for the cascade) `aws` CLI on PATH, Bedrock-enabled
  AWS credentials in the standard chain.

You do not need to know Beklemishev's hierarchy to follow this
tutorial. You should know enough Lean to read structure literals
and inductive types. If you can read the climber source, you can
do every exercise here.

---

## 1. Build and smoke

```bash
cd climber
lake build
lake exe smoke
```

Expected output:

```
climber — smoke test
====================

T₀: minimal implicational logic with ⊥-elim (K, S, bot_e, MP).
    soundness₀ : ∀ φ env, Derivable₀ φ → interp env φ  ✓
... etc ...
The Beklemishev rung: T₀ ⊬ Con(T₀), T₁_rfn ⊢ Con(T₀).
```

Every `✓` is a theorem the kernel checked at compile time. The
executable is just reporting their existence; the verification
already happened during `lake build`.

If you want to confirm there are no `sorry`s lurking:

```bash
grep -rn "sorry" Climber/ | grep -v "\\-\\-"
```

You should see only doc-comment prose ("admit a rule," etc.), no
actual proof gaps.

---

## 2. The base theory T₀

Open `Climber/Object.lean`.

```lean
inductive Formula where
  | bot
  | atom (a : String)
  | imp (φ ψ : Formula)
  | prov (φ : Formula)
```

This is the object language. Four constructors — `⊥`, atoms,
implication, and an internal *provability* predicate `prov` whose
purpose we'll explain in §5.

```lean
inductive Derivable₀ : Formula → Prop where
  | k     : ...
  | s     : ...
  | bot_e : ...
  | mp    : ...
```

Four rules: K (`φ → ψ → φ`), S
(`(φ → ψ → χ) → (φ → ψ) → φ → χ`), ex falso quodlibet
(`⊥ → φ`), and modus ponens. This is the implicational fragment
of intuitionistic propositional logic plus ⊥-elim.

```lean
def Formula.interp (env : String → Prop) : Formula → Prop
  | .bot     => False
  | .atom a  => env a
  | .imp φ ψ => interp env φ → interp env ψ
  | .prov φ  => Derivable₀ φ
```

The interpretation. Atoms get truth values from `env`; `prov φ`
gets the metalanguage proposition `Derivable₀ φ` (recursive
reference to the object theory).

The headline of this file:

```lean
theorem soundness₀ {φ : Formula} {env : String → Prop}
    (h : Derivable₀ φ) : Formula.interp env φ
```

Every T₀-derivable formula is true under any environment. This
is the metalanguage truth lemma for T₀ — a textbook induction over
`Derivable₀`.

**Takeaway.** T₀ is small and sound. We have a kernel-checked
proof that everything T₀ proves is metalanguage-true.

---

## 3. The growth mechanism

Open `Climber/Climb.lean`.

```lean
structure SoundExtension where
  schema : Formula → Prop
  sound  : ∀ φ env, schema φ → Formula.interp env φ
```

This is the unit of climbing. A `SoundExtension` carries a *schema*
(predicate over formulas saying which ones the extension admits)
and a *soundness certificate* (a Lean term of the soundness type).
The certificate is what the kernel checks at admission.

```lean
structure Theory where
  extras : List SoundExtension

def Theory.base : Theory := { extras := [] }
def Theory.extend (T : Theory) (se : SoundExtension) : Theory := ...
```

A theory is just a list of admitted extensions on top of T₀. The
empty theory is the base.

```lean
inductive derives (T : Theory) : Formula → Prop where
  | base   : Derivable₀ φ → derives T φ
  | extra  : (se : SoundExtension) → se ∈ T.extras →
             se.schema φ → derives T φ
  | mp     : derives T (.imp φ ψ) → derives T φ → derives T ψ
```

Three constructors: any T₀-theorem; any instance admitted by any
extension; modus ponens. This is the climbed proof system — base
plus admitted schemas, closed under MP.

The headline of this file:

```lean
theorem climb_sound {T : Theory} {φ env}
    (h : derives T φ) : Formula.interp env φ
```

**Every theory built by climbing preserves metalanguage truth.**
By induction on the derivation: `base` cases discharge by
`soundness₀`; `extra` cases discharge by the extension's own
`sound` field (kernel-checked at admission); `mp` is standard.

This is the architectural floor. Once you understand `climb_sound`,
you understand climber.

**Takeaway.** A theory grows by admitting extensions. Each
extension carries its own soundness proof. The metatheorem
guarantees the climb stays inside metalanguage truth — for any
list of admitted extensions, regardless of who proposed them.

---

## 4. The Peirce rung — a climb end-to-end

Open `Climber/Demo.lean`. This is one rung made entirely concrete.

Peirce's law is `((p → q) → p) → p`. Classically valid, not
intuitionistically valid — so T₀ cannot derive it.

```lean
def peirceFormula (p q : String) : Formula :=
  .imp (.imp (.imp (.atom p) (.atom q)) (.atom p)) (.atom p)
```

The proposer's certificate that Peirce's law is sound under any
environment uses classical case-analysis (`by_cases`):

```lean
theorem peirceSound (p q : String) (env : String → Prop) :
    Formula.interp env (peirceFormula p q) := by
  simp only [peirceFormula, Formula.interp_imp, Formula.interp_atom]
  intro h
  by_cases hp : env p
  · exact hp
  · exact h (fun hp' => absurd hp' hp)
```

The proposed extension bundles the schema (any Peirce instance
over any pair of atoms) with this certificate:

```lean
def peirceExtension : SoundExtension where
  schema := fun φ => ∃ p q : String, φ = peirceFormula p q
  sound := by
    rintro φ env ⟨p, q, rfl⟩
    exact peirceSound p q env

def T₁ : Theory := Theory.base.extend peirceExtension

theorem T₁_derives_peirce (p q : String) :
    derives T₁ (peirceFormula p q) := ...

theorem T₁_sound {φ env} (h : derives T₁ φ) :
    Formula.interp env φ := climb_sound h
```

**The two halves of the rung.** From above: `peirceSound` proves
the soundness certificate, the kernel admits, T₁ derives Peirce.
From below: `peirce_not_derivable_in_T₀` (in `Counter.lean`) proves
the climb crossed an unreachable line.

Open `Climber/Counter.lean` to see how the unreachable-line claim
is established. The argument uses a 3-element Heyting algebra
`H3 := { bot, mid, top }`:

```lean
def counterEnv : String → H3
  | "p" => H3.mid
  | _   => H3.bot

theorem peirce_h3_value :
    Formula.heyting counterEnv counterProvVal (peirceFormula "p" "q")
      = H3.mid := ...

theorem peirce_not_derivable_in_T₀ :
    ¬ Derivable₀ (peirceFormula "p" "q") := by
  intro h
  have hval := h.h3Valid counterEnv counterProvVal
  rw [peirce_h3_value] at hval
  exact H3.noConfusion hval
```

The model satisfies T₀'s axioms (K, S, ⊥-elim) and preserves MP,
but Peirce's law evaluates to `mid` (not `top`). Anything T₀
derives must be `top`. Therefore Peirce isn't derivable.

**Takeaway.** The Peirce rung is complete: a soundness certificate
gets the formula admitted into T₁; a separating model proves T₀
couldn't have reached it on its own. The climb crossed an
unreachable line, and stayed sound.

---

## 5. The Beklemishev rung

The Peirce rung shows the architecture works. The Beklemishev rung
shows what makes it interesting.

Open `Climber/Reflection.lean`.

The internal provability predicate `prov φ` (introduced in §2) has
no rule in T₀ — T₀ can't say anything about its own provability.
The reflection schema RFN(T₀) admits any formula of the form
`prov φ → φ`:

```lean
def rfn0Schema (ψ : Formula) : Prop :=
  ∃ φ : Formula, ψ = .imp (.prov φ) φ
```

The soundness certificate for this schema is exactly `soundness₀`
itself:

```lean
def rfn0Extension : SoundExtension where
  schema := rfn0Schema
  sound  := by
    rintro ψ env ⟨φ, rfl⟩
    simp only [Formula.interp_imp, Formula.interp_prov]
    exact fun h => soundness₀ h
```

`interp env (prov φ → φ)` unfolds to `Derivable₀ φ → interp env φ`,
which is *exactly* `soundness₀ φ`. The metalanguage truth lemma for
T₀ becomes the certificate that admits RFN(T₀) at the next rung.
This is the Feferman/Beklemishev move made into a Lean term.

```lean
def T₁_rfn : Theory := Theory.base.extend rfn0Extension

def consistencyFormula : Formula := .imp (.prov .bot) .bot

theorem T₁_rfn_derives_con :
    derives T₁_rfn consistencyFormula
```

`consistencyFormula` is `prov ⊥ → ⊥` — semantically, "T₀ does not
derive ⊥." Con(T₀). The RFN schema admits it directly (instantiate
the schema at φ = ⊥).

The matching unreachable-line claim:

```lean
theorem con_not_derivable_in_T₀ :
    ¬ Derivable₀ consistencyFormula := ...
```

Same H3 trick as Peirce, but now we use the `provVal` parameter:
assign `prov ⊥` the value `mid`, then `imp (prov ⊥) ⊥` evaluates
to `imp mid bot = bot`. T₀ couldn't have derived this; T₁_rfn does.

**Takeaway.** A theory's metalanguage soundness lemma becomes the
certificate that admits its reflection principle at the next rung.
The system's logical strength climbs in a kernel-blessed way. T₀
can't prove its own consistency; T₁_rfn can. This is the
architecturally deepest claim climber makes.

---

## 6. The live cascade (optional)

If you have AWS Bedrock access, you can run the proposer/gate loop
interactively.

```bash
lake exe bedrock-smoke   # connectivity check; prints OK: READY
lake exe runner          # 3 rounds (default)
lake exe runner 5        # 5 rounds
```

Each round, Claude proposes an **EXTENSION** — a `SoundExtension`
term. The runner writes a wrapper, runs `lake env lean --run`,
classifies, retries on elab errors. Verdicts:

- `ADMITTED` — the kernel verified the soundness certificate; the
  schema enters the accumulated climbed theory.
- `ELAB-ERROR` — the kernel refused; Lean's diagnostic is fed back
  to the LLM for one retry.

After every non-error round, the runner regenerates `Climbed.lean`:

```lean
import Climber

namespace Climber.Climbed

def round_0 : SoundExtension := ...
def round_1 : SoundExtension := ...
-- ...

def T_climbed : Theory :=
  Theory.base.extend round_0 |>.extend round_1 -- ...

theorem T_climbed_sound {φ env}
    (h : derives T_climbed φ) : Formula.interp env φ :=
  climb_sound h

end Climber.Climbed
```

This is **replayable evidence** that the cascade-built theory is
sound. Verify it standalone:

```bash
lake env lean Climbed.lean
```

If it elaborates without errors, you have a kernel-blessed theory
the cascade built.

**Where the unreachable-line claims live.** The cascade verdicts
do not certify T₀-non-derivability. Those claims are in the static
artifact: `peirce_not_derivable_in_T₀` (in §4) and
`con_not_derivable_in_T₀` (in §5). The cascade is the same
proposer/gate soundness loop made interactive; the on-stage
"unreachable line crossed" sentence is anchored by the static
theorems, not by cascade verdicts.

**Takeaway.** The architecture is interactive. The proposer is
unbounded; the gate is narrow; the system leaves behind a
kernel-buildable composite theory each round.

---

## 7. Exercise — propose your own extension

Time to climb a rung yourself. Goal: admit double-negation
elimination `((φ → ⊥) → ⊥) → φ` as a sound extension.

Open `Climber/Demo.lean`. Below the existing definitions, add:

```lean
/-- Double-negation elimination instantiated at φ. -/
def dneFormula (φ : Formula) : Formula :=
  .imp (.imp (.imp φ .bot) .bot) φ

/-- Soundness of DNE: classical case-analysis on `interp env φ`. -/
theorem dneSound (φ : Formula) (env : String → Prop) :
    Formula.interp env (dneFormula φ) := by
  simp only [dneFormula, Formula.interp_imp, Formula.interp_bot]
  intro h
  by_cases hφ : Formula.interp env φ
  · exact hφ
  · exact (h hφ).elim

/-- The DNE extension. Schema admits any DNE instance. -/
def dneExtension : SoundExtension where
  schema := fun ψ => ∃ φ : Formula, ψ = dneFormula φ
  sound := by
    rintro ψ env ⟨φ, rfl⟩
    exact dneSound φ env

/-- T₁_dne — T₀ extended with DNE. -/
def T₁_dne : Theory := Theory.base.extend dneExtension

/-- T₁_dne derives any DNE instance. -/
theorem T₁_dne_derives_dne (φ : Formula) :
    derives T₁_dne (dneFormula φ) :=
  derives.extra dneExtension (dneFormula φ)
    (by simp [T₁_dne, Theory.extend, Theory.base])
    ⟨φ, rfl⟩
```

Now build:

```bash
lake build
```

If it succeeds, you have a fourth-and-a-half admitted extension to
T₀ (alongside Peirce). The kernel checked `dneSound` and accepted
the schema. `T₁_dne_derives_dne` derives any DNE instance in one
step.

**Try breaking it.** Edit `dneSound` to remove the `by_cases`
line, replacing it with `exact h.elim` or something else
intuitionistic. The proof will fail — DNE genuinely *requires*
classical reasoning. The kernel won't admit it without a real
classical certificate.

**Try a non-tautology.** Add an extension whose schema admits
`atom "p"` directly. The soundness proof will fail — `env "p"`
isn't always true. The kernel correctly refuses.

**Takeaway.** You've climbed a rung. The architecture handled it
in 5 lines of new code. Adding a different rung is the same
five-line pattern with a different formula and a different
classical-truth proof.

---

## 8. Where to go next

- The **README** has the full design, the keynote portfolio
  positioning, and the path to iterated reflection-principle
  climbing past one rung.
- **`Reflection.lean`** is the deepest piece; understanding why
  `soundness₀` is the certificate for RFN(T₀) is most of the
  Beklemishev story in fifteen lines of Lean.
- **`Counter.lean`**'s H3 separating model is generic — you can
  adapt it to prove non-derivability of other classical-only
  formulas in T₀.
- The **References** section of the README points at Feferman
  1962, Beklemishev 2005, Smith 1984, and the LCF lineage.

If you want to extend the artifact rather than just read it:

- Sharper exercise: build out a full *iterated* reflection climb.
  Index `prov` by level, parameterize the interpretation over a
  sequence of theories, and admit RFN(T_n) at each rung. The
  README's *Path to iterated reflection-principle climbing*
  sketches the engineering.
- Adapt `Counter.lean`'s H3 separating model to prove non-
  derivability of other classical-only formulas in T₀ (DNE,
  consequentia mirabilis, …) and pair each one with its admitted
  extension for a richer set of unreachable-line theorems.

Welcome to the climb.
