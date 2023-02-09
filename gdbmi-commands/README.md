All GDB/MI commands, as of the last time I read the docs:

```
-ada-task-info
-add-inferior
-break-after
-break-commands
-break-condition
-break-delete
-break-disable
-break-enable
-break-info
-break-insert
-break-list
-break-passcount
-break-watch
-complete
-data-disassemble
-data-evaluate-expression
-data-list-changed-registers
-data-list-register-names
-data-list-register-values
-data-read-memory
-data-read-memory-bytes
-data-write-memory-bytes
-dprintf-insert
-enable-frame-filters
-enable-pretty-printing
-enable-timings
-environment-cd
-environment-directory
-environment-path
-environment-pwd
-exec-arguments
-exec-continue
-exec-finish
-exec-interrupt
-exec-jump
-exec-next
-exec-next-instruction
-exec-return
-exec-run
-exec-step
-exec-step-instruction
-exec-until
-file-exec-and-symbols
-file-exec-file
-file-list-exec-source-file
-file-list-exec-source-files
-file-list-shared-libraries
-file-symbol-file
-gdb-exit
-gdb-set
-gdb-show
-gdb-version
-inferior-tty-set
-inferior-tty-show
-info-ada-exceptions
-info-gdb-mi-command
-info-os
-interpreter-exec
-list-features
-list-target-features
-list-thread-groups
-stack-info-depth
-stack-info-frame
-stack-list-arguments
-stack-list-frames
-stack-list-locals
-stack-list-variables
-stack-select-frame
-symbol-info-functions
-symbol-info-module-functions
-symbol-info-module-variables
-symbol-info-modules
-symbol-info-types
-symbol-info-variables
-symbol-list-lines
-target-attach
-target-detach
-target-disconnect
-target-download
-target-file-delete
-target-file-get
-target-file-put
-target-flash-erase
-target-select
-thread-info
-thread-list-ids
-thread-select
-trace-find
-trace-frame-collected
-var-assign
-var-create
-var-delete
-var-evaluate-expression
-var-info-expression
-var-info-num-children
-var-info-path-expression
-var-info-type
-var-list-children
-var-set-format
-var-set-frozen
-var-show-attributes
-var-show-format
-var-update
```

It's frustrating how you can't simply get all these in a list from the GDB/MI documentation.

**How were they produced?**

Get the webpages:

`wget --no-parent --page-requisites --convert-links --recursive --level=1 --no-host-directories --no-directories --span-hosts --accept html https://sourceware.org/gdb/onlinedocs/gdb/GDB_002fMI.html`

Grep them for commands:

`ag 'The <code>.*<\/code> Command'`

Then clean up that output.