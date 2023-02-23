# Compile
FROM    rust:bullseye AS compiler

WORKDIR /meilisearch

ARG     COMMIT_SHA
ARG     COMMIT_DATE
ARG     GIT_TAG
ENV     VERGEN_GIT_SHA=${COMMIT_SHA} VERGEN_GIT_COMMIT_TIMESTAMP=${COMMIT_DATE} VERGEN_GIT_SEMVER_LIGHTWEIGHT=${GIT_TAG}
ENV     RUSTFLAGS="-C target-feature=-crt-static"

COPY    . .
RUN     set -eux; \
        arch="$(dpkg --print-architecture)"; \
        if [ "$arch" = "arm64" ]; then \
            export JEMALLOC_SYS_WITH_LG_PAGE=16; \
        fi && \
        cargo build --release

# Run
FROM    debian:11.6

ENV     MEILI_HTTP_ADDR 0.0.0.0:7700
ENV     MEILI_SERVER_PROVIDER docker

RUN     apt update -q \
        && apt install -q -y tini

# add meilisearch to the `/bin` so you can run it from anywhere and it's easy
# to find.
COPY    --from=compiler /meilisearch/target/release/meilisearch /bin/meilisearch
# To stay compatible with the older version of the container (pre v0.27.0) we're
# going to symlink the meilisearch binary in the path to `/meilisearch`
RUN     ln -s /bin/meilisearch /meilisearch

# This directory should hold all the data related to meilisearch so we're going
# to move our PWD in there.
# We don't want to put the meilisearch binary
WORKDIR /meili_data


EXPOSE  7700/tcp

ENTRYPOINT ["tini", "--"]
CMD     /bin/meilisearch
