# Errors — Rocq / coqc message → cause → mathcomp fix

> A lookup table from the **error message you see** to its **likely
> cause** and a **concrete ssreflect/mathcomp fix**. This is the
> reusable debugging asset: when `coqc` (or `rocq_compile_file`) prints
> something, find the row, apply the fix, re-check.
>
> Read-only guidance. It tells *you* what to try; it does not auto-fix.
> Seeded from `reference.md` §35.10 (HB/canonical-structure errors) and
> expanded with the unification, rewrite, application, scope and
> universe families.

## How to use this file

1. Match the error to a **family** (section heading) by its keyword:
   *infer placeholder*, *unify*, *not a subterm*, *illegal
   application*, *scope / notation*, *HB / universe*.
2. Read the row: **message (abbreviated) → likely cause → fix →
   cross-ref**.
3. Follow the `(§N)` for the full rule (`N ≤ 37` → `reference.md`;
   `N ≥ 38` → `domains/<N>_<topic>.md`; `templates.md §k` spelled out).

When rocq-mcp is available, `rocq_compile_file` returns a structured
`errors` list plus a reusable `state_id` + goals at the error position
— inspect that state (read the goal, `rocq_query` the offending symbol)
before editing. All idioms below are current mathcomp 2.5 /
analysis 1.16.

A general first move for *any* inference/unification failure: turn on
implicits to see what Rocq actually wrote.

```coq
Set Printing All.            (* or: Set Printing Coercions. *)
About <symbol>.  Check <term>.  Locate "<notation>".
```

---

## 1. "Cannot infer this placeholder" / canonical-structure / HB

The unifier could not fill a `_` — usually a **missing instance** so
the canonical-structure / HB resolution found nothing to plug in.

| Message (abbrev.) | Likely cause | Fix | Ref |
|---|---|---|---|
| `Cannot infer this placeholder of type "T"` | No canonical instance makes the carrier a `<Struct>Type` | Declare the missing `HB.instance Definition _ := …Build T …` *before* the use site; confirm with `HB.about T` / `HB.howto T <Struct>` | §15, §35.7 |
| `Cannot infer the implicit parameter X` | Implicit not determined by the explicit args; structure not in scope | Make the arg explicit at the call, or supply `[the X of T]` / `@lemma`; or `Import` the module providing the instance (import order) | §3, §24.1, §25.2 |
| `Could not unify "Foo X" and "Bar Y"` inside `HB.instance` | Missing **parent** instance for the carrier | Provide the parent instance first, or pick the factory whose `of`-context matches what is already declared | §15, §35.1 |
| `ambiguous canonical projection` | A diamond is unresolved at the join | Add an explicit combined `HB.instance Definition _ : <Mixin> … := …`; if a parent was enriched after descendants, `HB.saturate` | §35.4, §35.7 |
| `abbreviation "Foo.Build" is not applied enough` | A factory/mixin `Build` needs more positional `of`-context args | `HB.about Foo` / `Print Foo.Build` to see the arity; supply the `of`-context explicitly when invoked outside a builders block | §15, §35.2 |

What to check, in order, when a placeholder won't infer:

1. Is the instance **declared** at all? `HB.about T`. If not, build it
   (§15). If yes but unreachable, check **import order** (§3) — the
   `HB.instance` lives in a module you forgot to `Import`.
2. Is a **parent** missing? `HB.howto T <Struct>` prints the factory
   chain that closes the gap (§35.7).
3. Is it a **diamond**? `ambiguous canonical projection` ⇒ add the
   explicit join (§35.4).
4. Only as a last resort, annotate with `[the X of T]` (§24.1) — and
   delete it again once the instance is in place; the annotation is
   noise when resolution works (§24.1, §22.4).

---

## 2. "Unable to unify "X" with "Y""

The two sides are *almost* the same — the mismatch is usually a
**display / scope** difference or an **implicit-argument** difference,
not a real type error. `Set Printing All` makes it visible.

| Message (abbrev.) | Likely cause | Fix | Ref |
|---|---|---|---|
| `Unable to unify "x%R" with "x%:E"` (or `…%E`) | Ring vs extended-real scope: an `R` value where an `\bar R` is expected (or vice versa) | Insert / drop the coercion: `x%:E` to lift `R`→`\bar R`; keep one scope open and let `%:E` mark the boundary (don't sprinkle `%R`/`%E`) | §6.2, §19, §22.3 |
| `Unable to unify` where the terms print identically | Hidden implicit / display arg differs | `Set Printing All`; pin the differing implicit (`@lemma …` or `(x : R)`), or pass the display as `_` rather than a named display | §24.4, §25.2 |
| `Unable to unify` after a `rewrite` | The lemma's LHS instantiates a *different* occurrence than intended | Pin the spot with `[in RHS]` / `[LHS]` / `[in X in _]` (see §3 below) | §29.2 |
| `Unable to unify "0" with "0%:R"` (numerals) | A literal `0`/`1` parsed in the wrong scope | Disambiguate with `0 :> R` (the one annotation §24.5 keeps), or open the right `ring_scope` locally | §24.5, §6 |

Rule of thumb: if the two terms *look* identical, it is implicits or
scope (§24.4); if they look different in a `%R`/`%E`/`%:E` way, it is
the ereal boundary (§19).

---

## 3. "not a subterm of the goal" (failed `rewrite`)

The rewrite pattern did not match where you expected — either the
**occurrence** is wrong, or the term lives **under a binder** the bare
`rewrite` can't reach.

| Message (abbrev.) | Likely cause | Fix | Ref |
|---|---|---|---|
| `The LHS of … is not a subterm of the goal` | Pattern matches a *different* occurrence, or none | Pin the location: `rewrite [in RHS]L`, `rewrite [LHS]L`, `rewrite [in X in _ + X]L` | §29.2 |
| `not a subterm` on a `\sum` / `\prod` / `\int` / `lim` | The redex is **under a binder**; bare `rewrite` won't enter it | Use `under eq_bigr => i Pi do rewrite L` (or `eq_integral` / `eq_cvg`); close with `over.` if no `do` | §29.1, §34.3, §43.6 |
| `rewrite … found nothing` / `nothing to rewrite` | Wrong direction, or the redex is already gone | Try `-L` (right-to-left); use `rewrite ?L` to make it non-failing in a chain; never use `inE` with `-` | §29.3, §29.4 |
| `not a subterm` after `Set`-rewriting by hand | Hand-rolled set equality | Prefer `rewrite predeqE` for `setX = setY`, or `apply/seteqP; split=> x` | §29.5, templates.md §9 |

If the redex appears several times and you want one of them, *always*
pin with a pattern rather than relying on default selection — explicit
patterns also document intent and parse faster (§29.2).

---

## 4. "Illegal application (Non-functional construction)"

You applied something that is **not a function** to an argument —
typically an **over- or under-applied** term, or a **missing
coercion** so a structure was used where its carrier was meant.

| Message (abbrev.) | Likely cause | Fix | Ref |
|---|---|---|---|
| `Illegal application (Non-functional construction)` | Term over-applied: extra argument past its arity | `About f` / `Check f` to see the real arity; drop the surplus arg | §16, §31 |
| `Illegal application … expected N arguments` | Under-applied lemma fed to `apply:`/`exact:` | Supply the missing args, or let `apply:` unify them (often the explicit args are useless — §22.2) | §22.2, §26.2 |
| `… is not a function; it cannot be applied` | A structure used where its **carrier** (the coercion target) was meant | Rely on the coercion (write `T`, not `[the … of T]`); if the coercion is missing on a legacy export, add it | §35.10 (Coercion), §24.1 |
| `Non-functional construction` after `@` | `@` forced *all* args explicit, mis-counting the `of`-context | Drop `@` and let HB infer the `of`-context positions; keep `@` only where one position is truly ambiguous | §25.1, §35.11 |

---

## 5. Scope / notation: "Unknown interpretation", "not found in scope"

A notation didn't parse, or printed back oddly, because the **scope**
isn't open or the **module** providing it isn't imported.

| Message (abbrev.) | Likely cause | Fix | Ref |
|---|---|---|---|
| `Unknown interpretation for notation "…"` | The notation's scope is not open here | Add the matching `Local Open Scope` (e.g. `ring_scope`, `ereal_scope`, `classical_set_scope`); never plain `Open Scope` | §6 |
| `The reference X was not found in the current environment` | The module defining `X` is not imported | `From mathcomp Require Import <module>` in the correct group/order; avoid path-qualified names like `mathcomp.classical` | §3, §23 |
| `Syntax error` / notation parses wrong | Scope precedence or ordering changed a parse tree | Restore the established scope ordering; tweak `Bind Scope` / precedence only with care and a full re-test | §6.2, §6.3 |
| `X is not a head symbol` / `Search` returns nothing | Wrong scope ⇒ wrong head symbol in your query | Open the scope first; then `Search` by the head symbol of the LHS | §6, §37.2 |
| convergence notation prints unexpanded / won't parse | Missing the bundled `--> ` import or wrong scope | Import the `topology` / `normedtype` layer; use the bundled `_ --> _` form, not hand-unfolded filters | §3, §23.4, §30.6 |

Diagnostic: `Locate "notation".` shows which scope a notation lives in;
`Print Scopes.` lists what is open. If a name resolves only when
fully-qualified, the real fix is an `Import` (§23), not the qualifier.

---

## 6. HB `_subproof` / anomaly / "Universe inconsistency"

Lower-frequency, higher-confusion. Usually a structural problem, not a
typo — read where it points before editing.

| Message (abbrev.) | Likely cause | Fix | Ref |
|---|---|---|---|
| `Anomaly … HB …` / error citing a `_subproof` / `_mixin_` name | HB elaboration failed on a generated obligation | Re-run the `HB.instance` with `#[verbose]` (or `#[log]`) to see what HB elaborated; usually a missing parent or a wrong `Build` arity upstream | §35.2, §35.7 |
| `Universe inconsistency … cannot enforce …` | A definition forced a universe ordering that clashes (often `Type`-level data stored where `Prop` / a lower universe was expected) | Lower the offending field's universe (store `bool`/`Prop` content, not `Type`); avoid packing large `Type`s into a mixin; sometimes an explicit `: Type@{i}` annotation, but prefer restructuring | §36.7, §35.1 |
| `HB.howto` finds no chain / "missing instance" though mixins present | A join was declared after its descendants and not recomputed | `HB.saturate.` (use sparingly — slow), or add the explicit join `HB.instance` | §35.7, §35.11 |
| reviewer flag: "this breaks forgetful inheritance" | A `Definition` aliased an HB-equipped type | Replace the alias by `Notation`, wrap in a `Module`, or use `<Struct>.copy` | §35.5, §35.10 |
| `… is not applied enough` from a builders block | A reusable lemma was put *inside* `HB.builders` (anonymous, uncallable) | Factor the lemma out *before* `HB.builders` and call it from inside | §35.11 |

For HB specifically: `HB.about <name>` (what's attached + where),
`HB.locate <name>` (which file generated a synthesized constant), and
`HB.graph "out.dot"` (visualize missing joins) localize the problem
fast (§35.7).

---

## Quick triage

| The message mentions… | Go to | First check |
|---|---|---|
| infer / placeholder / canonical | §1 | `HB.about T`; import order (§3) |
| unify "X" with "Y" | §2 | `Set Printing All`; `%R`/`%E` (§19) |
| not a subterm (rewrite) | §3 | pattern / `under` (§29) |
| Illegal / Non-functional | §4 | `About f` arity; coercion |
| Unknown / not found / scope | §5 | `Local Open Scope`; `Import` (§3) |
| anomaly / `_subproof` / universe | §6 | `#[verbose] HB.instance`; `HB.howto` |

When in doubt, inspect the live state at the error with
`rocq_compile_file` (it hands back goals + a `state_id` at the error
position) and read the goal before changing the script.
