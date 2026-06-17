#!/usr/bin/env bash
# PostToolUse hook: after an Edit/Write to a *.v file, run the mechanical
# style auditor (scripts/audit-quick.sh) on JUST that file and surface any
# findings as advisory additionalContext.
#
# Contract: this hook is READ-ONLY and ADVISORY. It must NEVER block or fail
# the edit. It always exits 0, even when findings exist. No findings -> silent
# (no output object), so it adds zero noise on clean edits.
#
# Input  (stdin): the PostToolUse hook JSON, which carries the tool name and
#                 tool_input (with the edited file_path).
# Output (stdout): on findings, a JSON object of the documented PostToolUse
#                 shape with hookSpecificOutput.additionalContext.
#
# Pure bash + POSIX coreutils + python3 (for robust JSON in/out). If python3
# is absent, degrade to silent exit 0.

set -u

# Resolve the plugin root: hooks.json passes ${CLAUDE_PLUGIN_ROOT}; fall back
# to the script's own location so a direct invocation still works.
ROOT="${CLAUDE_PLUGIN_ROOT:-}"
if [ -z "$ROOT" ]; then
  ROOT="$(cd "$(dirname "$0")/.." 2>/dev/null && pwd)"
fi
AUDIT="$ROOT/scripts/audit-quick.sh"

# Read the hook payload from stdin.
PAYLOAD="$(cat 2>/dev/null || true)"

PY="$(command -v python3 || command -v python || true)"
if [ -z "$PY" ]; then
  exit 0   # cannot parse JSON safely -> stay silent
fi

# Extract the edited file path from the tool_input (Edit/Write use file_path).
FILE="$(printf '%s' "$PAYLOAD" | "$PY" -c '
import json, sys
try:
    d = json.load(sys.stdin)
except Exception:
    sys.exit(0)
ti = d.get("tool_input") or {}
p = ti.get("file_path") or ti.get("path") or ""
sys.stdout.write(p)
' 2>/dev/null)"

# Only act on .v files that exist and that we can audit.
case "$FILE" in
  *.v) ;;
  *) exit 0 ;;
esac
[ -n "$FILE" ] && [ -r "$FILE" ] || exit 0
[ -x "$AUDIT" ] || [ -r "$AUDIT" ] || exit 0

# Run the auditor (advisory; never let its exit status escape).
FINDINGS="$(sh "$AUDIT" "$FILE" 2>/dev/null || true)"

# No findings -> silent.
if [ -z "$(printf '%s' "$FINDINGS" | tr -d '[:space:]')" ]; then
  exit 0
fi

# Emit the PostToolUse advisory shape with additionalContext.
printf '%s' "$FINDINGS" | "$PY" -c '
import json, sys
findings = sys.stdin.read().rstrip("\n")
ctx = ("mathcomp-skills audit-quick findings (advisory; verify before "
       "applying — keyed to reference.md sections):\n" + findings)
out = {
    "hookSpecificOutput": {
        "hookEventName": "PostToolUse",
        "additionalContext": ctx,
    }
}
json.dump(out, sys.stdout)
sys.stdout.write("\n")
' 2>/dev/null || true

exit 0
