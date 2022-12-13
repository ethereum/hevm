# `hevm rlp`

```
Usage: hevm rlp --decode TEXT

Available options:
  -h,--help                Show this help text
  --decode TEXT            RLP encoded hexstring
```

Decodes an [rlp](https://ethereum.org/en/developers/docs/data-structures-and-encoding/rlp/) encoded hexstring

```
$ hevm rlp --decode \
0xf86b808509502f900082520894423163e58aabec\
5daa3dd1130b759d24bef0f6ea8711c37937e08000\
8025a0434f6d9df411bfe4fbd0fcaf68ac2259a3d5\
eba91cb77797bdf249a22920c44fa06cf49be63274\
22ffa714bdcd5f627a85696720db855756057536fc\
5e867a725c

[ 0x
,0x09502f9000
,0x5208
,0x423163e58aabec5daa3dd1130b759d24bef0f6ea
,0x11c37937e08000
,0x
,0x25
,0x434f6d9df411bfe4fbd0fcaf68ac2259a3d5eba91cb77797bdf249a22920c44f
,0x6cf49be6327422ffa714bdcd5f627a85696720db855756057536fc5e867a725c
]
```
