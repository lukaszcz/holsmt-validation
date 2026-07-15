#!/usr/bin/env bash

set -euo pipefail

script_dir=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)
validation_root=$(cd "$script_dir/.." && pwd)

holsmt_root=${HOLSMT_ROOT:-}
cvc5=${HOL4_CVC_EXECUTABLE:-${CVC5:-cvc5}}
out=/tmp/cvc5-cpc-matrix.json
timeout_seconds=60
input_list=
inputs=()

usage() {
  cat <<'EOF'
Usage: tools/run_cvc5_cpc_gate.sh [options] INPUT.smt2 ...

Build the checked HOL cvc5/CPC driver, replay every supplied SMT-LIB query,
and fail unless every query reports CVC_CPC_TAC_PASS.

Options:
  --holsmt-root DIR  HOL checkout containing bin/Holmake and src/HolSmt
                     (default: HOLSMT_ROOT)
  --cvc5 PATH        cvc5 executable (default: HOL4_CVC_EXECUTABLE, CVC5,
                     then cvc5 from PATH)
  --input-list FILE  Newline-separated SMT-LIB query paths
  --out FILE         JSON matrix report (default: /tmp/cvc5-cpc-matrix.json)
  --timeout SECONDS  Per-query timeout (default: 60)
  -h, --help         Show this help

The generated holsmt-cvc-cpc-tac launcher is removed on exit if this command
created it. Existing launchers are preserved.
EOF
}

die() {
  printf 'run_cvc5_cpc_gate.sh: %s\n' "$*" >&2
  exit 2
}

resolve_executable() {
  local value=$1
  if [[ "$value" == */* ]]; then
    [ -x "$value" ] || die "cvc5 is not executable: $value"
    (cd "$(dirname "$value")" && printf '%s/%s\n' "$PWD" "$(basename "$value")")
  else
    command -v "$value" || die "cvc5 is not on PATH: $value"
  fi
}

while [ "$#" -gt 0 ]; do
  case "$1" in
    --holsmt-root)
      [ "$#" -ge 2 ] || die "--holsmt-root requires a directory"
      holsmt_root=$2
      shift 2
      ;;
    --cvc5)
      [ "$#" -ge 2 ] || die "--cvc5 requires an executable"
      cvc5=$2
      shift 2
      ;;
    --input-list)
      [ "$#" -ge 2 ] || die "--input-list requires a file"
      input_list=$2
      shift 2
      ;;
    --out)
      [ "$#" -ge 2 ] || die "--out requires a file"
      out=$2
      shift 2
      ;;
    --timeout)
      [ "$#" -ge 2 ] || die "--timeout requires a number of seconds"
      timeout_seconds=$2
      shift 2
      ;;
    -h|--help)
      usage
      exit 0
      ;;
    --)
      shift
      inputs+=("$@")
      break
      ;;
    -*)
      die "unknown option: $1"
      ;;
    *)
      inputs+=("$1")
      shift
      ;;
  esac
done

[ -n "$holsmt_root" ] || die "set HOLSMT_ROOT or pass --holsmt-root"
[ -d "$holsmt_root/src/HolSmt" ] ||
  die "HOL checkout does not contain src/HolSmt: $holsmt_root"
holsmt_root=$(cd "$holsmt_root" && pwd)

[[ "$timeout_seconds" =~ ^[0-9]+$ ]] && [ "$timeout_seconds" -gt 0 ] ||
  die "--timeout must be a positive integer"
[ -z "$input_list" ] || [ -f "$input_list" ] ||
  die "input list does not exist: $input_list"
if [ -z "$input_list" ] && [ "${#inputs[@]}" -eq 0 ]; then
  die "supply one or more SMT-LIB inputs or --input-list"
fi

holmake="$holsmt_root/bin/Holmake"
[ -x "$holmake" ] || die "Holmake is missing or not executable: $holmake"
cvc5=$(resolve_executable "$cvc5")

export HOLSMT_ROOT="$holsmt_root"
export HOLSMT_VALIDATION_DIR="$validation_root"
export HOL4_CVC_EXECUTABLE="$cvc5"

driver="$holsmt_root/src/HolSmt/holsmt-cvc-cpc-tac"
driver_existed=false
[ -e "$driver" ] && driver_existed=true
cleanup() {
  if ! "$driver_existed"; then
    rm -f "$driver"
  fi
}
trap cleanup EXIT

printf 'HOLSMT_ROOT=%s\n' "$HOLSMT_ROOT"
printf 'HOLSMT_VALIDATION_DIR=%s\n' "$HOLSMT_VALIDATION_DIR"
printf 'HOL4_CVC_EXECUTABLE=%s\n' "$HOL4_CVC_EXECUTABLE"
printf 'matrix_report=%s\n' "$out"

"$holmake" -C "$holsmt_root/src/HolSmt" smtheap holsmt-cvc-cpc-tac

matrix_args=(
  --driver "$driver"
  --cvc5 "$cvc5"
  --out "$out"
  --timeout "$timeout_seconds"
)
[ -z "$input_list" ] || matrix_args+=(--input-list "$input_list")
matrix_args+=("${inputs[@]}")

python3 "$script_dir/run_cvc5_cpc_matrix.py" "${matrix_args[@]}"
