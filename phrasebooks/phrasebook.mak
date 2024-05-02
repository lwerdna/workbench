# detect if environment variable is set
ifeq ($(origin DEBUG), undefined)
$(info DEBUG UNDEFINED)
else
PROBE_FLAGS += -DDEBUG
$(info DEBUG DEFINED)
endif


.PHONY: error

# default target if listed first, displays error message
error:
	@echo "available targets: install, uninstall"
	@exit -1

# install/uninstall via link

.PHONY: install uninstall

install:
	@if [ -L "$(BN_PLUGINS)/Z80" ]; then \
		echo "already installed"; \
	else \
		echo "installing"; \
		ln -s "$(PWD)" "$(BN_PLUGINS)/Z80"; \
	fi

uninstall:
	@if [ -L "$(BN_PLUGINS)/Z80" ]; then \
		echo "uninstalling"; \
		rm "$(BN_PLUGINS)/Z80"; \
	else \
		echo "not installed"; \
	fi

# detect machine and operating system
MACHINE =
OS =
ifeq ($(OS),Windows_NT)
    CCFLAGS += -D WIN32
    ifeq ($(PROCESSOR_ARCHITECTURE),AMD64)
        MACHINE = x64
    else
        ifeq ($(PROCESSOR_ARCHITECTURE),AMD64)
            MACHINE = x64
        endif
        ifeq ($(PROCESSOR_ARCHITECTURE),x86)
            MACHINE = x86
        endif
    endif
else
	# os
    UNAME_S := $(shell uname -s)
    ifeq ($(UNAME_S),Linux)
        OS = linux
    endif
    ifeq ($(UNAME_S),Darwin)
        OS = macos
    endif
    # machine
    UNAME_P := $(shell uname -p)
    ifeq ($(UNAME_P),x86_64)
        MACHINE = x64
    endif
    ifneq ($(filter %86,$(UNAME_P)),)
        MACHINE = x86
    endif
    ifneq ($(filter arm%,$(UNAME_P)),)
        MACHINE = arm
    endif
endif

# error/warning/info
$(error    blah)
$(warning  blah)
$(info MACHINE: $(MACHINE))
$(info      OS: $(OS))



all:

