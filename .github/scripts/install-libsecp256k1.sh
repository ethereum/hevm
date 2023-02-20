#!/bin/bash
set -eux -o pipefail

## The following script builds and installs libsecp256k1 to ~/.local/lib

if [[ "$(uname -s)" =~ ^MSYS_NT.* ]]; then
    echo "This script is only meant to run on Windows under MSYS2"
    exit 1
fi

if [ -f "$HOME/.local/lib/libsecp256k1.a" ]; then
  echo "libsecp256k1 exists, exiting..."
  exit 0
fi

PREFIX="$HOME/.local"
GIT_REF="21ffe4b22a9683cf24ae0763359e401d1284cc7a"
curl -LO "https://github.com/bitcoin-core/secp256k1/archive/$GIT_REF.zip"

unzip "$GIT_REF.zip" && rm "$GIT_REF.zip"
cd "secp256k1-$GIT_REF"

./autogen.sh
# hevm needs reecovery module
# enable pic so static library can link against dynamic correctly
./configure --prefix=$PREFIX --enable-module-recovery --disable-benchmark --disable-tests --with-pic

make install

# Delete file that causes failure to link
find "$PREFIX" -name libsecp256k1.dll.a -delete
