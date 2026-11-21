FROM alpine/git:v2.49.1@sha256:c0280cf9572316299b08544065d3bf35db65043d5e3963982ec50647d2746e26 AS source
WORKDIR /sqlglot
RUN set -eu; rev=eb11aec4be8cb2122afe713a4816662c3f0fb2fa; \
    git init -q; \
    git fetch --no-tags --depth=1 --no-recurse-submodules https://github.com/tobymao/sqlglot.git "$rev"; \
    git checkout --quiet --detach FETCH_HEAD; \
    test "$(git rev-parse --verify 'HEAD^{commit}')" = "$rev"; \
    rm -rf .git

FROM python:3.13-slim@sha256:e48f59cdba69a3cbd9ed2cf0f348d90d45a8d350d98134cf1070bc106ee9ed90 AS base
COPY --from=source /sqlglot /sqlglot

FROM base AS tracer
COPY builder/requirements.lock /builder/
RUN pip install --no-deps --no-cache-dir -r /builder/requirements.lock && pip check
COPY builder/ /builder/
WORKDIR /sqlglot
ENV PYTHONPATH=/builder:/sqlglot SKIP_INTEGRATION=0 OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 PYTHON_CPU_COUNT=4
CMD ["python", "/builder/collect.py"]

FROM base AS entry
WORKDIR /app
COPY maps.json selector.py patching.py packing.py proofs.py shared_writes.py ./
RUN python -m compileall -q /app
CMD ["python", "/app/selector.py"]
