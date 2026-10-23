# The msapi server as a static binary on an empty image, for Cloudflare
# Containers (linux/amd64). Build from the repository root.
FROM --platform=linux/amd64 rust:1-alpine AS build
RUN apk add --no-cache musl-dev
WORKDIR /src
COPY Cargo.toml Cargo.lock ./
COPY crates crates
COPY docs docs
RUN cargo build --release --locked -p msapi-server --bin msapi \
    && mkdir -p /out/data /out/tmp \
    && cp target/release/msapi /out/msapi

FROM --platform=linux/amd64 scratch
COPY --from=build /out /
ENV MSAPI_ADDR=0.0.0.0:8080 MSAPI_DB=/data/msapi.db MSAPI_TRUST_PROXY=1 TMPDIR=/tmp
EXPOSE 8080
ENTRYPOINT ["/msapi", "serve"]
