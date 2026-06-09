FROM mcr.microsoft.com/devcontainers/base:jammy

USER vscode
WORKDIR /home/vscode

RUN curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh -s -- -y --default-toolchain none

ENV PATH="/home/vscode/.elan/bin:${PATH}"

# Pre-install the Lean toolchain so users don't wait for it on first open
COPY lean-toolchain .
RUN elan toolchain install $(cat lean-toolchain) && rm lean-toolchain