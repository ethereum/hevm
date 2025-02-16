#!/usr/bin/env bash
set -euxo pipefail

num=$(awk 'END{print NR}' "$1")
awk -v ll="$num" 'BEGIN {print "{\"trace\": [" } {if (NR!=ll) {print $0; if (NR!=ll-1) {print ","}} else {print "], \"output\":" $0}} END{print "}"}' "$1" > "$1.json"
