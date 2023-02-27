#!/usr/bin/env bash

num=$(wc -l "$1" | cut -d " " -f 1)
awk -v ll="$num" 'BEGIN {print "{\"trace\": [" } {if (NR!=ll) {print $0; if (NR!=ll-1) {print ","}} else {print "], \"output\":" $0}} END{print "}"}' "$1" > "$1.json"
