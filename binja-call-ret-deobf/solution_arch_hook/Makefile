.PHONY: error install uninstall

ifndef BN_PLUGINS
	$(error BN_PLUGINS is undefined)
	@exit -1
endif

error:
	@echo "available targets: install, uninstall"
	@exit -1

install:
	@if [ -L "$(BN_PLUGINS)/deobfuscate.py" ]; then \
		echo "already installed"; \
	else \
		echo "installing"; \
		ln -s "$(PWD)/deobfuscate.py" "$(BN_PLUGINS)/deobfuscate.py"; \
	fi

uninstall:
	@if [ -L "$(BN_PLUGINS)/deobfuscate.py" ]; then \
		echo "uninstalling"; \
		rm "$(BN_PLUGINS)/deobfuscate.py"; \
	else \
		echo "not installed"; \
	fi


