FROM mcr.microsoft.com/devcontainers/base:ubuntu-24.04@sha256:d94c97dd9cacf183d0a6fd12a8e87b526e9e928307674ae9c94139139c0c6eae AS development

USER root
RUN apt-get update && apt-get install -y --no-install-recommends \
    clang make pkg-config python3 zlib1g-dev xz-utils \
    && rm -rf /var/lib/apt/lists/*
COPY .devcontainer/install-tools.sh /tmp/install-tools.sh
RUN sh /tmp/install-tools.sh base
COPY lean-toolchain /tmp/silmaril-lean-toolchain

USER vscode
ENV PATH="/home/vscode/.elan/bin:${PATH}"
RUN elan-init -y --no-modify-path --default-toolchain none \
    && elan toolchain install "$(cat /tmp/silmaril-lean-toolchain)"
WORKDIR /workspaces/silmaril

FROM development AS cross-test
USER root
RUN sh /tmp/install-tools.sh cross-test
ENV PATH="/opt/binaryen/bin:/opt/wasmtime:${PATH}"
ENV BINARYEN_ROOT="/opt/binaryen"
USER vscode
