#!/bin/bash
set -eux -o pipefail

## The following script builds and installs libff to ~/.local/lib

if [[ "$(uname -s)" =~ ^MSYS_NT.* ]]; then
    echo "This script is only meant to run on Windows under MSYS2"
    exit 1
fi

if [ -f "$HOME/.local/lib/libff.a" ]; then
  echo "libff exists, exiting..."
  exit 0
fi

if [ -d libff ]; then
  echo "$(pwd)/libff" already exists! Using it instead of re-cloning the repo.
else
  git clone https://github.com/scipr-lab/libff -b v0.2.1 --recursive
fi
cd libff
git checkout v0.2.1 && git submodule init && git submodule update

sed -i 's/find_library(GMP_LIBRARY gmp)/find_library(GMP_LIBRARY NAMES libgmp.a)/' CMakeLists.txt
PREFIX="$HOME/.local"
ARGS=("-DCMAKE_INSTALL_PREFIX=$PREFIX" "-DWITH_PROCPS=OFF" "-G" "Ninja")
CXXFLAGS="-fPIC"

mkdir -p build
cd build
CXXFLAGS="$CXXFLAGS" cmake "${ARGS[@]}" ..
cmake --build . && cmake --install .