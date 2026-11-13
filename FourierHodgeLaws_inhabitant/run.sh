#!/usr/bin/env bash
set -euo pipefail
cd -- "$(dirname -- "${BASH_SOURCE[0]}")"
python3 ci/stage.py --package .work/package
python3 ci/runner.py --package .work/package --phase all
