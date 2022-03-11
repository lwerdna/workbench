.PHONY: error install uninstall

ifndef BN_PLUGINS
	$(error BN_PLUGINS is undefined)
	@exit -1
endif

error:
	@echo "available targets: install, uninstall"
	@exit -1

install:
	@if [ -L "$(BN_PLUGINS)/handle-blx-lr.py" ]; then \
		echo "already installed"; \
	else \
		echo "installing"; \
		ln -s "$(PWD)/handle-blx-lr.py" "$(BN_PLUGINS)/handle-blx-lr.py"; \
	fi

uninstall:
	@if [ -L "$(BN_PLUGINS)/handle-blx-lr.py" ]; then \
		echo "uninstalling"; \
		rm "$(BN_PLUGINS)/handle-blx-lr.py"; \
	else \
		echo "not installed"; \
	fi


