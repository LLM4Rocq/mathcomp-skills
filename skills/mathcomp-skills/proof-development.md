# Proof Development — filling an `Admitted.` / a stuck subgoal

> A Rocq-native workflow for **discharging an open obligation** (an
> `Admitted.`, an `admit.`, or a `give_up` left by `gen have` / `near`)
> and for unsticking a subgoal that won't close. It mirrors a
> disciplined sorry-filling loop: inspect, search, try, commit, verify.
>
> This is **guidance for a human or agent debugging a proof**, not an
> auto-prover. Every step is a thing *you* decide and check; the
> rocq-mcp `rocq_step_multi` battery only *reports* which candidate
> tactics close a goal — it never advances the session or picks for
> you. You still author the script and own its hygiene.

## How to use this file

Work the numbered loop top to bottom. Each step names the rocq-mcp
tool to drive it (short names; prefix `mcp__rocq-mcp__`) and the
`reference.md` / `phrasebook.md` rule that governs the *style* of the
result. The tool signatures are authoritative in `SKILL.md`
§ "rocq-mcp integration"; the load-bearing fact is that **`from_state`
is a required `int`** on both `rocq_check` and `rocq_step_multi` —
always thread the `state_id` you got from `rocq_start` or the prior
`rocq_check`.

If rocq-mcp is not configured, the same loop runs in an IDE: read the
goal in the goal pane, `Search` in the editor, try candidates by hand,
`Qed`, then `Print Assumptions`. The discipline is identical; only the
tooling differs.

---

## The loop

### 1. Locate the open obligation

Find the `Admitted.`, `admit.`, or `give_up` you are closing. In a
file, `rocq_toc file=<path>` outlines the lemmas; grep for `admit`,
`Admitted`, `give_up`, `Abort`. Note the lemma name — you will need it
for the hygiene check in step 6.

A lemma left on `Admitted.` is *axiom-shaped*: it pollutes every
downstream `Print Assumptions`. The goal of this loop is to replace it
with a `Qed.`-closed script that introduces **no** new axiom (§36.4).

### 2. Inspect the goal state FIRST

Never guess a tactic before you have read the goal. Open the state:

```
# anchored on the real file, at the obligation
rocq_start theorem=<lemma> file=<path>
# or position mode: 0-indexed, point at the whitespace just BEFORE
# the first character of the tactic whose pre-state you want
rocq_start file=<path> line=<L> character=<C>
# or, for scratch iteration, warm imports only and paste the goal
rocq_start preamble="From mathcomp Require Import all_ssreflect ssralg."
```

Read the returned goals and **capture the `state_id`** — it threads
through every later call. Position mode rounds *forward* to a sentence
boundary: a cursor inside a sentence (or on its period) yields the
state *after* it. To see the goal *before* a tactic, point at the
whitespace before its first character (see `SKILL.md` § "Warm-import
iteration").

Squint at the goal's *shape* and match it to a skeleton in
`templates.md` (filter / convergence / bigop / set-extensionality /
classical-choice / …). The shape tells you which lemma family to
search and which battery subset to try.

### 3. `Search` for a finishing lemma BEFORE guessing

The library almost certainly already has the lemma. Search before you
invent. With `from_state`, `Search` sees the **live** hypotheses and
open scopes mid-proof:

```
rocq_query command="Search (?h (?u + ?v))." from_state=<state_id>
rocq_query command="Search _ (_ <= _) inside Order.TotalTheory." \
           from_state=<state_id>
```

Apply the §37 search discipline: lead with the head symbol of what is
in your goal (the LHS for an equational rewrite, §37.2), add salient
secondary symbols, strip over-matching wrappers with `-is_true`
`-reflect` (§37.1, §37.11). Pick the intent-to-idiom row in
`phrasebook.md` that matches what you want to *do* (close, decide,
rewrite-under-binder, forward a fact) and follow its `(§N)`.

If `Search` returns nothing, broaden one axis at a time (drop a
pattern constraint, widen the module) rather than firing a blind
tactic.

### 4. Generate 2–3 candidate tactics and TEST them

From the goal shape (step 2) and the lemma you found (step 3), write
**2–3 concrete candidates** — not a wall of guesses. Test them in one
shot with the battery, which evaluates each against the *same* state
and **does not advance it**:

```
rocq_step_multi from_state=<state_id> \
  tactics=["exact: lem.", "by rewrite lem.", "apply: lem; by []."]
```

Each result entry carries `success`, the resulting `goals`, and
`proof_finished`. Read them to see which candidate *closes* the goal
(`proof_finished: True`) versus which merely *progresses* it.

Keep the list focused and keyed to the goal shape; cap at 20 entries.
Useful battery subsets (see `SKILL.md` § "`rocq_step_multi` battery"):

```
# close-out          "by [].", "done.", "exact: H.", "reflexivity.",
#                    "assumption.", "trivial."
# arithmetic         "lia.", "nia."          (zify first; §45.5)
# ring / field       "ring.", "field.", "lra.", "nra."   (§45.3-§45.4)
# structure          "case: n.", "elim: n.", "move=> *."
```

`lia` / `lra` / `ring` / `field` need the matching `Require Import`
warmed into the session first (cross-ref `domains/45_algebra_tactics.md`).

### 5. Commit the winner with `rocq_check`

The battery never advances state. Re-run the winning tactic through
`rocq_check`, which moves the session to a **new** `state_id`:

```
rocq_check from_state=<state_id> body="exact: lem."
```

If the goal had several pieces, loop back to step 2 on the new
`state_id` and discharge the next one. When a `rocq_check` returns
`proof_finished: True`, it also returns **`proof_tactics`** (the
ordered root→current tactic list) and `proof_hint` (how to assemble
the `.v`). Paste `proof_tactics` into the file in place of the
`Admitted.`.

If the response *omits* `proof_tactics` and instead carries
`proof_tactics_status`, an ancestor `state_id` was evicted and the
chain is broken — restart from step 2 and re-walk to rebuild it.

### 6. Re-verify hygiene with `rocq_assumptions`

A closed proof is not a *clean* proof until you confirm it added no
axiom. After the file compiles:

```
rocq_assumptions name=<lemma> file=<path>
```

Confirm you stayed inside the expected axiom budget (§36.4). For an
**analysis** proof the boolp trio is expected and only it:

- `functional_extensionality_dep` (funext)
- `propositional_extensionality` (propext)
- `constructive_indefinite_description` (cid)

`pselect` / `EM` / `classic` are *derived* from these and are fine. A
plain **mathcomp** (non-analysis) proof should ideally list *nothing*.
Anything else — a stray `Axiom`, a leftover `Admitted`, an unexpected
`admit` — is a red flag (§36.4: reviewers block PRs that silently add
axioms). For a sandboxed admit-free check of a candidate before it
touches the tree, use `rocq_verify` (whole-file `problem_statement` +
`proof`).

### 7. Prefer the SHORTEST passing script

A passing script is a draft, not the deliverable. Tighten it to the
minimal-tactic form (§22.5) before you `Qed`:

- Collapse a bookkeeping line that just discharges triviality to
  `by [].` or `done.` (§22.1; `phrasebook.md` §12).
- Fold intermediate trivial subgoals into the chain with `//` / `//=`
  instead of separate lines (§26.4, §29.3).
- Drop useless arguments to `exact:` / `apply:` (§22.2) and useless
  scope delimiters `%R` / `%E` inside an already-open scope (§22.3).
- Replace `move=> H; rewrite H` with `move=> ->`, and a named-then-
  consumed hypothesis with `->` / `<-` / `?` / `_` (§27).
- Prefer `exact: t` when a term closes the goal; never let a bare
  `apply:` be the closing line (§26.2).

Re-run the tightened script through `rocq_check` / `rocq_compile_file`
to confirm it still closes, then commit it.

---

## Worked example

Obligation: a `nat` summation identity left admitted.

```coq
Lemma sum_const_admitted n : \sum_(i < n) 1 = n.
Proof. Admitted.
```

**1–2. Locate + inspect.** Warm the imports and read the goal.

```
rocq_start preamble="From mathcomp Require Import all_ssreflect."
# paste the lemma; capture state_id = 7. Goal: \sum_(i < n) 1 = n
```

Shape: a `\big[+%R/0]_(i < n) F i = X` bigop identity (templates.md §6).

**3. Search** for the constant-summand lemma, head symbol `\sum`:

```
rocq_query command="Search (\sum_(_ < _) _) (_ * _)." from_state=7
rocq_query command="Search sum1_card." from_state=7
# -> big_const, card_ord, sum1_card, ...
```

**4. Try 2–3 candidates** against the same state, no advance:

```
rocq_step_multi from_state=7 tactics=[
  "by rewrite sum1_card card_ord.",
  "by rewrite big_const_ord iter_addn_0 muln1.",
  "by elim: n => // n IHn; rewrite big_ord_recr IHn."]
```

The first entry reports `proof_finished: True` — the winner.

**5. Commit + extract.**

```
rocq_check from_state=7 body="by rewrite sum1_card card_ord."
# proof_finished: True; proof_tactics = ["by rewrite sum1_card card_ord."]
```

Replace `Admitted.` with `Proof. by rewrite sum1_card card_ord. Qed.`

**6. Hygiene.** `rocq_assumptions name=sum_const_admitted file=<path>`
→ *Closed under the global context* (no axioms). Clean.

**7. Shortest form.** Already one line, already `by`-closed; nothing
to trim. Done.

---

## Reminders

- This loop **debugs**; it does not autonomously prove. You read every
  goal, choose every search, and own the final script's hygiene.
- `rocq_step_multi` is a *reporter*: it tells you which candidate
  closes a goal without touching the session. Always commit the winner
  separately with `rocq_check`.
- Stop and think when the battery closes *nothing*: the goal usually
  needs a `rewrite` / `have` / `case:` to reshape it first (steps 2–3),
  not a bigger battery.
- A proof that compiles but adds an axiom is **not done** (step 6).
