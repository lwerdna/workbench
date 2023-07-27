Examine a VBMETA partition implementing [Android Verified Boot](https://source.android.com/docs/security/features/verifiedboot/avb).

[./vbmeta.img](./vbmeta_a.bin) - example vbmeta partition

[./annotated.txt](./annotated.txt) - annotated hex dump of the example vbmeta partition

[./verify.py](./verify.py) - python script to exercise the cryptography

[./helpers.py](./helpers.py) - helper module for above

A rough illustration of what's going on in this partition is:

![](./assets/vbmeta-diagram.png)

I got the VBMETA partition from a Pixel 5 image

https://developers.google.com/android/images search for SHA256 "c3ea1715"
https://dl.google.com/dl/android/aosp/redfin-rd1a.200810.020-factory-c3ea1715.zip

Unzipping extracts the file `image-redfin-rd1a.200810.020.zip` which, when unzipped, extracts `vbmeta.bin`.