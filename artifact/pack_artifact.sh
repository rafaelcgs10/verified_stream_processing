#!/usr/bin/env bash
# Pack the Isabelle theories of this repository into an anonymous artifact zip.
#
# Contents of the zip (all under a top-level folder timely_dataflow_isabelle/):
#   - ROOT, README.md, LICENSE   from artifact/, replacing the repository ones.
#     The repository ROOT does not build the local theories of the Dataplane
#     session, and the repository LICENSE names its authors, so the artifact
#     ships the anonymous versions kept next to this script.
#   - dataplane/                  every theory reachable from the ROOT entry
#     points, which is everything under dataplane/ except the tooling in Tools/
#   - nondeterministic_dataflow/  only the base theories that the parent session
#     needs, not the tables of the earlier paper
#
# Never included: .git and every other git trace, .claude, ai/, dataplane/Tools,
# editor backups, scratch files, and anything unreachable from ROOT. The script
# aborts if an identifying string survives into the staged tree, and warns about
# unproved lemmas.
#
# Portability: POSIX tools plus bash 3.2, so it runs on Linux and on macOS
# without installing anything. Requires: bash, awk, sed, grep, find, zip, unzip.
#
# Usage: artifact/pack_artifact.sh [output.zip]
#        (default: timely_dataflow_isabelle.zip in the repository root)
set -eu

for tool in awk sed grep find zip unzip; do
  command -v "$tool" >/dev/null 2>&1 || { echo "missing required tool: $tool" >&2; exit 1; }
done

HERE=$(cd "$(dirname "$0")" && pwd)
cd "$HERE/.."
REPO=$PWD

NAME=timely_dataflow_isabelle
OUT=${1:-$NAME.zip}
case "$OUT" in /*) ;; *) OUT="$REPO/$OUT" ;; esac

STAGE=$(mktemp -d 2>/dev/null || mktemp -d -t artifact)
trap 'rm -rf "$STAGE"' EXIT
DEST="$STAGE/$NAME"
mkdir -p "$DEST"

RED=$(printf '\033[31m'); YELLOW=$(printf '\033[33m'); RESET=$(printf '\033[0m')
NL=$(printf '\nx'); NL=${NL%x}

# --- theories to ship -------------------------------------------------------
# Theories listed under a given session in artifact/ROOT, as repository paths,
# so that the script and the shipped ROOT can never drift apart.
root_theories() {
  awk -v want="$1" -v dir="$2" '
    /^session / { cur = $2; mode = 0 }
    cur == want && /^  theories/ { mode = 1; next }
    cur == want && /^  [a-z]/ { mode = 0 }
    mode && /^    / { gsub(/[[:space:]"]/, ""); print dir "/" $0 ".thy" }
  ' "$HERE/ROOT"
}

# Lexically resolve . and .. in a path, without touching the file system.
# BSD realpath has no --relative-to, so this replaces it.
norm_path() {
  awk -v p="$1" 'BEGIN {
    n = split(p, part, "/"); out = ""
    for (i = 1; i <= n; i++) {
      if (part[i] == "" || part[i] == ".") continue
      if (part[i] == "..") { sub(/\/?[^\/]*$/, "", out); continue }
      out = (out == "") ? part[i] : out "/" part[i]
    }
    print out
  }'
}

# Imports of a theory: unqualified names, relative paths such as ../Lib/Bots,
# and Nondeterministic_Dataflow.X references.
theory_imports() {
  awk 'BEGIN{p=0} /^[[:space:]]*imports/{p=1} p{print} /^[[:space:]]*begin([[:space:]]|$)/{exit}' "$1" \
    | sed 's/(\*.*\*)//g' | sed 's/^[[:space:]]*imports//' | tr -d '"' \
    | tr ' \t' '\n\n' | grep -v '^$' \
    | grep -v -x -e begin -e keywords -e abbrevs || true
}

# Resolve one import of a theory in directory $1 to a repository-relative path,
# if it denotes a file we ship. Imports of external sessions resolve to nothing.
resolve_import() {
  imp_dir=$1; imp=$2
  case "$imp" in
    Nondeterministic_Dataflow.*)
      p="nondeterministic_dataflow/${imp#Nondeterministic_Dataflow.}.thy" ;;
    */*)
      p=$(norm_path "$imp_dir/$imp.thy") ;;
    *.*) return 0 ;;
    *)  p="$imp_dir/$imp.thy" ;;
  esac
  [ -n "$p" ] && [ -f "$REPO/$p" ] && printf '%s\n' "$p"
  return 0
}

# Worklist over a newline separated string, so no bash arrays are needed.
PENDING=$(root_theories Dataplane dataplane; root_theories Nondeterministic_Dataflow nondeterministic_dataflow)
[ -n "$PENDING" ] || { echo "no theories listed in artifact/ROOT" >&2; exit 1; }
SEEN=""

while [ -n "$PENDING" ]; do
  f=${PENDING%%"$NL"*}
  case "$PENDING" in *"$NL"*) PENDING=${PENDING#*"$NL"} ;; *) PENDING="" ;; esac
  [ -n "$f" ] || continue
  case "$SEEN" in *"|$f|"*) continue ;; esac
  [ -f "$f" ] || { echo "missing theory: $f" >&2; exit 1; }
  SEEN="$SEEN|$f|"
  dir=$(dirname "$f")
  deps=$(theory_imports "$f" | while IFS= read -r imp; do
           [ -n "$imp" ] && resolve_import "$dir" "$imp"
         done)
  [ -n "$deps" ] && PENDING="$deps${PENDING:+$NL$PENDING}"
done

THEORIES=$(printf '%s' "$SEEN" | tr '|' '\n' | grep -v '^$' | sort)

for f in $THEORIES; do
  case "$f" in
    dataplane/Tools/*)
      echo "closure reaches the excluded tooling: $f" >&2; exit 1 ;;
    nondeterministic_dataflow/table_*|nondeterministic_dataflow/Lifted*|nondeterministic_dataflow/Wstep*)
      echo "closure reaches an unshipped theory: $f" >&2; exit 1 ;;
  esac
  mkdir -p "$DEST/$(dirname "$f")"
  cp "$f" "$DEST/$f"
done

# Every theory under dataplane/, except the tooling, must be in the closure:
# an unreachable one would ship without ever being checked by the build.
unreached=""
for f in $(find dataplane -name '*.thy' ! -name '*~' ! -path 'dataplane/Tools/*' | sort); do
  case "$SEEN" in *"|$f|"*) ;; *) unreached="$unreached $f" ;; esac
done
if [ -n "$unreached" ]; then
  echo "theories not reachable from artifact/ROOT, they would ship unchecked:" >&2
  for f in $unreached; do echo "  $f" >&2; done
  exit 1
fi

# --- session setup, README and license --------------------------------------
cp "$HERE/ROOT" "$HERE/README.md" "$HERE/LICENSE" "$DEST/"

# --- anonymity and hygiene checks -------------------------------------------
hidden=$(find "$DEST" -name '.*' | head -1)
[ -z "$hidden" ] || { echo "hidden file slipped into the artifact: $hidden" >&2; exit 1; }

leftover=$(find "$DEST" \( -name '*~' -o -name '#*#' -o -name '*.marks' \) | head -1)
[ -z "$leftover" ] || { echo "editor leftover in the artifact: $leftover" >&2; exit 1; }

git_trace=$(find "$DEST" \( -name '.git*' -o -name '*.orig' -o -name '*.rej' \
  -o -name '*.patch' -o -name '*.diff' \) | head -1)
[ -z "$git_trace" ] || { echo "git trace in the artifact: $git_trace" >&2; exit 1; }

PATTERNS='Rafael|rafael|Traytel|Dmitriy|Gon.alves|rafaelcgs|Amazon|AWS|IQ_AUTH|MY_TOKEN'
PATTERNS="$PATTERNS"'|iq_plugin|Isar_Explore|AutoCorrode|opencode|/home/'
PATTERNS="$PATTERNS"'|@[A-Za-z0-9.-]+\.(com|dk|de|org|net)'
hits=$(grep -rInE "$PATTERNS" "$DEST" || true)
if [ -n "$hits" ]; then
  echo "${RED}identifying or environment specific string in the artifact:${RESET}" >&2
  printf '%s\n' "$hits" | sed "s|^$DEST/||" | head -20 >&2
  exit 1
fi

# The build flattens the session directories, so theory names must be unique.
dupes=$(for f in $THEORIES; do basename "$f"; done | sort | uniq -d)
if [ -n "$dupes" ]; then
  echo "duplicate theory names in the artifact:" >&2
  printf '%s\n' "$dupes" >&2
  exit 1
fi

# --- report incomplete proofs -----------------------------------------------
sorries=$(grep -rn --include='*.thy' -E '(^|[^A-Za-z_])sorry([^A-Za-z_]|$)' "$DEST" || true)
if [ -n "$sorries" ]; then
  echo "${RED}WARNING: the artifact contains unproved lemmas (sorry):${RESET}" >&2
  printf '%s\n' "$sorries" | sed "s|^$DEST/||" | while IFS= read -r line; do
    echo "${RED}  $line${RESET}" >&2
  done
fi

oopses=$(grep -rn --include='*.thy' -E '(^|[^A-Za-z_])oops([^A-Za-z_]|$)' "$DEST" || true)
if [ -n "$oopses" ]; then
  echo "${YELLOW}note: abandoned proofs (oops), which yield no theorem:${RESET}"
  printf '%s\n' "$oopses" | sed "s|^$DEST/||" | while IFS= read -r line; do
    echo "${YELLOW}  $line${RESET}"
  done
fi

# --- zip --------------------------------------------------------------------
# A fixed timestamp keeps the zip reproducible and drops the working mtimes.
rm -f "$OUT"
cd "$STAGE"
find "$NAME" -exec touch -t 202601010000 {} +
zip -r -X -q "$OUT" "$NAME"
count=$(printf '%s\n' $THEORIES | grep -c . || true)
files=$(unzip -Z1 "$OUT" | grep -vc '/$' || true)
echo "wrote $OUT"
echo "  $files files, of which $count theories, $(du -h "$OUT" | awk '{print $1}')"
