#!/bin/bash
set -eux -o pipefail

## The following script builds and installs libsecp256k1 to ~/.local/lib

INSTALL_VERSION=5dcc6f8dbdb1850570919fc9942d22f728dbc0af

if [[ "$(uname -s)" =~ ^MSYS_NT.* ]]; then
    echo "This script is only meant to run on Windows under MSYS2"
    exit 1
fi

PREFIX="$HOME/.local"
curl -LO "https://github.com/bitcoin-core/secp256k1/archive/$INSTALL_VERSION.zip"

unzip "$INSTALL_VERSION.zip" && rm "$INSTALL_VERSION.zip"
cd "secp256k1-$INSTALL_VERSION"

./autogen.sh
# hevm needs reecovery module
# enable pic so static library can link against dynamic correctly
./configure --prefix=$PREFIX --enable-module-recovery --disable-benchmark --disable-tests --with-pic

make install

# Delete file that causes failure to link
find "$PREFIX" -name libsecp256k1.dll.a -delete
