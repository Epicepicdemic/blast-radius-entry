# Wave-3 Blast Radius entry

Extract this overlay at the root of a clean team entry checkout at `5d6d8aa`. The installation checks the original selector, verifier and heavy-reach module digests before applying the integration patches.

```sh
docker build --platform linux/amd64 -t blast-entry-wave3 .
docker run --rm --platform linux/amd64 --network none --read-only \
  --tmpfs /tmp:rw,size=64m,mode=1777 --user 65534:65534 --cpus 2 --memory 4g \
  -v "$PWD/data:/data:ro" blast-entry-wave3
```

Supply the contest `tests.json` and `commits/*.patch` in the mounted data directory. The image writes one JSON plan per patch to standard output. Set `W3_TRACE=1` to record static prices and measured live charges on standard error.

The published Dockerfile uses the team's original immutable SQLGlot pin, Python base and requirements lock. The archive includes the default `Dockerfile` and `.dockerignore`.

The compressed profiles in `w3/profile/` contain observations of the unchanged pin. The build links them to source digests, inventory identities, call sites and the release's existing verification data. Full-suite plans remain available whenever a proof or a verifier deadline fails.
