# run:
#   make compile && make upload
#
PORT ?= /dev/ttyUSB0
FQBN ?= esp32:esp32:esp32
SKETCH_DIR ?= .

BUILD_DIR ?= build

.PHONY: all compile upload monitor clean fqbn boards

all: compile

boards:
	arduino-cli board list

fqbn:
	arduino-cli board listall | sed -n '1,200p'

compile:
	arduino-cli compile --fqbn $(FQBN) --output-dir $(BUILD_DIR) $(SKETCH_DIR)

upload:
	arduino-cli upload --fqbn $(FQBN) -p $(PORT) $(SKETCH_DIR)

monitor:
	echo "use minicom instead"
	#arduino-cli monitor -p $(PORT) -c baudrate=115200

clean:
	rm -rf $(BUILD_DIR)

