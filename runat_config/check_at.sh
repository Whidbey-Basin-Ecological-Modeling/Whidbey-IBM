#!/bin/bash

# Define paths
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
RUNAT_SCRIPT="$SCRIPT_DIR/runat.sh"
BASELINE="$SCRIPT_DIR/baseline.txt"
TEMP_OUTPUT=$(mktemp)

# Build the project
echo "Building project..."
if ! cmake --build "$PROJECT_ROOT"/build/debug-hack --target headless --verbose; then
    echo "BUILD FAILED"
    exit 1
fi

# Run the acceptance test and capture output
echo "Running acceptance test..."
if ! "$RUNAT_SCRIPT" > "$TEMP_OUTPUT" 2>&1; then
    echo "EXECUTION FAILED"
    rm "$TEMP_OUTPUT"
    exit 1
fi

# Compare with baseline
if diff "$TEMP_OUTPUT" "$BASELINE" > /dev/null; then
    echo "AT OK"
else
    echo "AT FAILED: Output differs from baseline"
    # Filter out differences in the "Nearshore connector nodes" lines which might be reordered
    # But wait, the user wants a SIMPLE DIFF. If I have to filter, it's not a simple diff.
    # I'll just keep it simple for now and see if it stays deterministic.
    diff -u "$BASELINE" "$TEMP_OUTPUT"
fi

# Cleanup
rm "$TEMP_OUTPUT"
