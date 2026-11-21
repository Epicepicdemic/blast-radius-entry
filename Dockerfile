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

FROM base AS dependencies
COPY builder/requirements.lock /builder/
RUN pip install --no-deps --no-cache-dir -r /builder/requirements.lock && pip check

FROM dependencies AS tracer
COPY builder/ /builder/
WORKDIR /sqlglot
ENV PYTHONPATH=/builder:/sqlglot SKIP_INTEGRATION=0 OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 PYTHON_CPU_COUNT=4
CMD ["python", "/builder/collect.py"]

FROM dependencies AS entry
ARG ISOLATION_DROP=1
ARG ENGINE_SKIP=1
ARG NARROW_SHARED_ARGS=1
ARG CLASS_TABLE_ENTRIES=1
ARG FUNCTION_INSERTIONS=1
ARG TOUCHED_ARGUMENTS=1
ARG LOCAL_SCOPE_CHANGES=1
ARG UNUSED_IMPORTS=1
ARG FAST_ANALYSIS=1
ARG IDENTITY_EQUIVALENCE=1
ENV FAST_ANALYSIS=$FAST_ANALYSIS \
    UNUSED_IMPORTS=$UNUSED_IMPORTS \
    LOCAL_SCOPE_CHANGES=$LOCAL_SCOPE_CHANGES \
    TOUCHED_ARGUMENTS=$TOUCHED_ARGUMENTS \
    FUNCTION_INSERTIONS=$FUNCTION_INSERTIONS \
    CLASS_TABLE_ENTRIES=$CLASS_TABLE_ENTRIES \
    ISOLATION_DROP=$ISOLATION_DROP \
    ENGINE_SKIP=$ENGINE_SKIP \
    NARROW_SHARED_ARGS=$NARROW_SHARED_ARGS \
    IDENTITY_EQUIVALENCE=$IDENTITY_EQUIVALENCE
WORKDIR /app
COPY maps.json selector.py patching.py packing.py proofs.py shared_writes.py mutation_summaries.py bounded_batch.py runner.py change_shapes.py table_readers.py import_readers.py pinned_data.py ./
RUN python import_readers.py /sqlglot /app/maps.json /app/import_readers.json && python table_readers.py /sqlglot /app/maps.json /app/table_readers.json && python mutation_summaries.py /sqlglot /app/mutations.json && python proofs.py /sqlglot /app/proof_facts.json && python pinned_data.py maps.json mutations.json && python -m compileall -q /app
CMD ["python", "/app/selector.py"]
