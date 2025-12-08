Command Saleae's "Logic 2" software to take a capture (w/ glitch filter and trigger):
  `./go.py capture`
Saves the resulting .sal and .bin files.
Parses the resulting .bin files to yield multi-channel data:
  `./go.py parse`

  with output like:

  t=-0.000007 [0, 0, 1, 0, 0, 0]
  t=-0.000006 [0, 1, 1, 0, 0, 0]
  t=-0.000004 [0, 1, 1, 0, 0, 1]
  t=-0.000002 [0, 1, 1, 1, 0, 1]
  t=0.000000 [1, 1, 1, 1, 0, 1]
  t=0.000006 [1, 1, 1, 1, 1, 1]
  t=0.000017 [1, 0, 1, 1, 1, 1]

Enable all this with "Logic 2" settings -> automation -> enable automation server.

How to parse the saved .bin files:
  https://support.saleae.com/getting-help/troubleshooting/technical-faq/binary-export-format-logic-2
  https://support.saleae.com/getting-help/troubleshooting/technical-faq/binary-and-csv-export-formats-2025-update

How to interface with "Logic 2":
  https://support.saleae.com/product/user-guide/extensions-apis-and-sdks

  Extensions
    High-Level Analyzers (Python)
    Analog Measurements (Python)
    Digital Measurements (Python)
  SDK
    Protocol Analyzers SDK (C++)
  API
    Logic 2 Automation (Python)      <-- HERE
    Logic MSO Automation (Python)

