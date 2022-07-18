FROM gitpod/workspace-full

# Install Stack
RUN curl -sSL https://get.haskellstack.org/ | sh

# Add ghcup to PATH
ENV GHCUP_INSTALL_BASE_PREFIX=/workspace
ENV CABAL_DIR=/workspace/.cabal
ENV PATH="/workspace/.local/bin:/workspace/.cabal/bin:/workspace/.ghcup/bin:${PATH}"

# Install GHCup
RUN curl --proto '=https' --tlsv1.2 -sSf https://get-ghcup.haskell.org | BOOTSTRAP_HASKELL_NONINTERACTIVE=1 BOOTSTRAP_HASKELL_MINIMAL=1 sh

# Build once to get compiler and libs
RUN stack setup --resolver=lts-16.31
