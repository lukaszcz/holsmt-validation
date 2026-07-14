#!/bin/sh
# Run a validation command against a HolSmt source checkout.
set -eu

validation_root=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
holsmt_root=${HOLSMT_ROOT:-}

if [ -z "$holsmt_root" ] || [ ! -d "$holsmt_root/src/HolSmt" ]; then
  echo "Set HOLSMT_ROOT to a HolSmt checkout containing src/HolSmt." >&2
  exit 2
fi

export HOLSMT_ROOT="$(CDPATH= cd -- "$holsmt_root" && pwd)"
export HOLSMT_VALIDATION_DIR="$validation_root"
exec "$@"
