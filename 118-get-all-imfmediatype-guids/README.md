---
title: Get all GUIDs from Media Foundation
tags: #IDA
---

NOTICE! This project ended early because I found https://github.com/gix/media-types (published at https://gix.github.io/media-types/) (mirrored at: [./assets/media-types-master.zip](./assets/media-types-master.zip)) which makes this obsolete and incomplete.

https://learn.microsoft.com/en-us/windows/win32/medfound/mf-mt-major-type-attribute says:

> The GUID constant for this attribute is exported from mfuuid.lib.

Now:

* find an mfuuid.lib, like: https://github.com/tpn/winsdk-7/blob/master/v7.1A/Lib/x64/mfuuid.lib
* extract guids.obj
* open in IDA
* run idascript.py
