#!/bin/bash
# WP-RB0 corpus fetch: re-fetches EXACTLY the third-party files of the census by pinned commit and verifies
# their sha256 (files.tsv). The files are NOT vendored in this repository: their licences differ (see CENSUS.md),
# and they are untrusted data -- read them, never execute them; run Python on them with `-I`.
#
#   fetch.sh [DEST]        DEST defaults to ./fetched next to this script; layout DEST/<project>/<path-in-repo>
#
# Needs curl and shasum. Exit status 0 only if every file was fetched and matches.
set -u
HERE="$(cd "$(dirname "$0")" && pwd)"
DEST="${1:-$HERE/fetched}"
bad=0; n=0
while IFS=$'\t' read -r proj repo commit path sha bytes lines; do
  case "$proj" in \#*|"") continue;; esac
  out="$DEST/$proj/$path"
  mkdir -p "$(dirname "$out")"
  if ! curl -fsSL --retry 3 -o "$out" "https://raw.githubusercontent.com/$repo/$commit/$path"; then
    echo "FETCH FAILED  $repo@$commit:$path" >&2; bad=$((bad+1)); continue
  fi
  got="$(shasum -a 256 "$out" | cut -d' ' -f1)"
  if [ "$got" != "$sha" ]; then
    echo "SHA MISMATCH  $repo@$commit:$path  expected $sha got $got" >&2; bad=$((bad+1))
  fi
  n=$((n+1))
done < "$HERE/files.tsv"
echo "fetched $n files into $DEST, $bad problem(s)"
[ "$bad" -eq 0 ]
