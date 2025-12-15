#!/bin/bash

# Output file
OUTPUT_FILE="QuantumSystem.lean"

# Find all .lean files in QuantumSystem directory, sort them, and format as imports
find QuantumSystem -name "*.lean" | sort | sed 's/\//./g' | sed 's/\.lean//g' | sed 's/^/import /' > "$OUTPUT_FILE"

echo "Updated $OUTPUT_FILE with all imports from QuantumSystem/"
