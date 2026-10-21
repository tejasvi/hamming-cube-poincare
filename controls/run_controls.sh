#!/bin/sh
# Runs both checkers on every control made by make_controls.py; each line should end with "exit 1".
# usage: sh run_controls.sh OUTDIR        (run from the controls directory)
for f in "$1"/*.json; do
  for prog in ../checker/check11a_mom.py ../independent/check11a_indep.py; do
    python3 -I "$prog" "$f" > /dev/null 2>&1
    rc=$?
    echo "$(basename "$prog") $(basename "$f") exit $rc"
  done
done
