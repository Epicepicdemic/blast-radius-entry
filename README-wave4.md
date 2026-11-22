# Wave-4 SQLGlot test selector

Extract the overlay into the root of a clean team entry at `5d6d8aa`. It expects the team's locked dependencies, coverage maps and original selector sources from that commit.

```sh
git archive 5d6d8aa | tar -x -C "$ENTRY"
tar -xzf blast-entry-wave4.tar.gz -C "$ENTRY"
docker build --platform linux/amd64 -t blast-entry-wave4 "$ENTRY"
docker run --rm --platform linux/amd64 --network none --read-only \
  --user 65534:65534 --cpus 2 --memory 4g --pids-limit 256 \
  --tmpfs /tmp:rw,size=64m,mode=1777 --cap-drop ALL \
  -v "$DATA:/data:ro" blast-entry-wave4
```

Set `ENTRY` to an empty directory and `DATA` to a contest input directory containing `tests.json` and `commits/*.patch`. The image's default command emits one JSON worker plan per input patch on stdout. The planner associates pin observations with test identities and maps them to the supplied inventory numbers. `W3_TRACE=1` adds static and live routing records to stderr.

The Dockerfile pins SQLGlot at `eb11aec4be8cb2122afe713a4816662c3f0fb2fa` and uses the base entry's locked Python distribution. Its build installs the Wave-3 selector and links the supplementary Wave-4 profiles to its coverage index. `w4/profile/` contains the collectors and compressed observations of the unmodified pin. The build checks the test identities when linking each test-indexed profile. Historical patch identifiers and outcome labels are used only by the external evaluation harness.

The selector analyzes changes on both sides of an edit. It tracks executed statement boundaries, owners of fresh containers, inherited scalar fields, reflective namespace readers, value lookups and whole-map readers in parser dispatch and tokenizer keyword tables, pool workers and integration-query rows. A control-flow bound that replaces a universal shared-state obligation keeps its entire reader set through live verification. Only closed leaf dispatch tables use the supplemental key bound. Parent tables and directly exported class tables keep the broader family rules. Private method deletions retain the pin’s parser resource-limit tests. Proven local bounds can be used without executing the changed project. For eligible expensive plans the inherited verifier can execute targeted tests in an isolated subprocess. It prices the available narrowing against irrevocable obligations, with a shorter limit for paired writer checks. Source observers, ambiguous import state, opaque workers, unmatched inventories and unresolved shared effects can require broader plans or the full suite.

The accompanying evaluation report documents observed costs, the remaining fallbacks, and the scope of the reference evidence.
