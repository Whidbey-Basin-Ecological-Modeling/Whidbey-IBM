#!/bin/bash

# this script needs to be run from the root of the repository, since paths are relative to that

set -e

# use --verbose on the build to see everything
cmake --build ./build/debug-hack --target headless; cp troy_run_listings_template.csv \
  troy_run_listings.csv; date; ./bin/Debug/headless "troy_run_listings.csv" "data/whidbey/output" \
  "data/whidbey/config/config_map_2000_data_2014_deterministic.json"; date