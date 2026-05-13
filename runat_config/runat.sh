#!/bin/bash
set -e
cd ~troy.frever/code/Whidbey-IBM
cp troy_run_listings_template.csv troy_run_listings.csv
./bin/Debug/headless "troy_run_listings.csv" "run32/map2000d2014" \
"runat_config/at_config.json"