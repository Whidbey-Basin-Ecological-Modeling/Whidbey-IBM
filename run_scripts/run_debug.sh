#!/bin/bash

REPO_ROOT="${HOME}/code/Whidbey-IBM"

set -e

# use --verbose on the build to see everything
cmake --build "${REPO_ROOT}/build/debug-hack" --target headless; \
cd "${REPO_ROOT}"; \
cp run_scripts/troy_run_listings_template.csv run_scripts/troy_run_listings.csv; \
date; \
"${REPO_ROOT}/bin/Debug/headless" "run_scripts/troy_run_listings.csv" "${REPO_ROOT}/data/whidbey/output" \
  "${REPO_ROOT}/data/whidbey/config/config_small_deterministic.json"; \
date

#cmake --build ./build/debug-hack --target headless; cp troy_run_listings_template.csv \
#  troy_run_listings.csv; date; ./bin/Debug/headless "troy_run_listings.csv" "data/whidbey/output" \
#  "data/whidbey/config/config_map_2000_data_2014_deterministic.json"; date