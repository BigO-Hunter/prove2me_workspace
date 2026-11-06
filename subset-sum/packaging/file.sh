#!/bin/bash
# Shim: file.py is the canonical pipeline (body-native, single source of truth).
# Kept so muscle memory and old riders/docs referencing file.sh keep working.
exec python3 "$(dirname "$0")/file.py" "$@"
