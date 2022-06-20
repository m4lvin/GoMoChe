FROM gitpod/workspace-full

# Install Stack
RUN curl -sSL https://get.haskellstack.org/ | sh

# Build once to get compiler and libs
RUN stack setup --resolver=lts-16.31
