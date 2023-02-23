#!/bin/bash
set -eux -o pipefail

## The following script builds and installs libff to ~/.local/lib

INSTALL_VERSION=v0.2.1

if [[ "$(uname -s)" =~ ^MSYS_NT.* ]]; then
    echo "This script is only meant to run on Windows under MSYS2"
    exit 1
fi

if [ -d libff ]; then
  echo "$(pwd)/libff" already exists! Using it instead of re-cloning the repo.
else
  git clone https://github.com/scipr-lab/libff -b "$INSTALL_VERSION" --recursive
fi
cd libff
git checkout "$INSTALL_VERSION" && git submodule init && git submodule update

sed -i 's/find_library(GMP_LIBRARY gmp)/find_library(GMP_LIBRARY NAMES libgmp.a)/' CMakeLists.txt
PREFIX="$HOME/.local"
ARGS=("-DCMAKE_INSTALL_PREFIX=$PREFIX" "-DWITH_PROCPS=OFF" "-G" "Ninja")
CXXFLAGS="-fPIC"

mkdir -p build
cd build
CXXFLAGS="$CXXFLAGS" cmake "${ARGS[@]}" ..
cmake --build . && cmake --install .
