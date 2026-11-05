#!/bin/bash
# Re-run / re-check the 9 staged WP-G differential rows. Plain Python + (optionally) one Xcelium run.
#   ./run.sh                check the committed Xcelium output (xrun5.out) against the reference rules, offline
#   ./run.sh --xcelium      regenerate the testbench, run it on the Xcelium host $XCELIUM_HOST (ONE run, own scratch
#                           dir /tmp/wpg-rows, removed afterwards), then check the fresh output
set -e
cd "$(dirname "$0")"
python3 runrows.py                       # rows_tb.sv from cases_wpg.json and the row sources
out=xrun11.out
if [ "$1" = "--xcelium" ]; then
  out=xrun_fresh.out
  H="${XCELIUM_HOST:?set XCELIUM_HOST to a host with Xcelium}"
  ssh -o BatchMode=yes "$H" 'mkdir -p /tmp/wpg-rows'
  scp -q rows_tb.sv "$H":/tmp/wpg-rows/
  ssh -o BatchMode=yes "$H" 'cd /tmp/wpg-rows && xrun -sv -q -timescale 1ns/1ns -xmlibdirname xcelium.d rows_tb.sv' > "$out"
  ssh -o BatchMode=yes "$H" 'rm -rf /tmp/wpg-rows'
fi
python3 checkrows.py "$out"
