#include <Arduino.h>

/*
	ESP32 MDIO/MDC bit-bang controller (IEEE 802.3 Clause 22),
	plus Clause 45 MMD access via Clause 22 registers (0x0D/0x0E).

	Serial commands:
		r <phy> <reg>
		w <phy> <reg> <value>
		mmdr <phy> <devad> <reg>
		mmdw <phy> <devad> <reg> <value>
		scan
		help

	Values can be decimal or hex (0x....).
*/

// ====== PIN CONFIG ======
static const int PIN_MDC	= 18;	 // Change to your wiring
static const int PIN_MDIO = 19;	 // Change to your wiring

// ====== TIMING ======
// Slower = more forgiving. Clause 22 allows MDC up to 2.5 MHz.
// We’ll run much slower (~100-200 kHz depending on delay).
static const uint32_t MDC_HALF_PERIOD_US = 2; // try 1-5 if needed

//----------------------------------------------------------------
// MD CLOCK functions
//----------------------------------------------------------------

static inline void mdc_low()
{
	digitalWrite(PIN_MDC, LOW);
}

static void mdc_high()
{
	digitalWrite(PIN_MDC, HIGH);
}

static inline void mdc_pulse()
{
	mdc_high();
	delayMicroseconds(1);
	mdc_low();
	delayMicroseconds(1);
}

//----------------------------------------------------------------
// MD I/O functions
//----------------------------------------------------------------

static bool IS_OUTPUT;

static void mdio_set_input()
{
	if (IS_OUTPUT) {
		Serial.print("setting PIN_MDIO to INPUT\n");
		pinMode(PIN_MDIO, INPUT);
		IS_OUTPUT = false;
	}
}

static void mdio_set_output()
{
	if (!IS_OUTPUT) {
		// Open drain so:
		// setting to 1/HIGH means "release to High-Z"
		// setting to 0/LOW means "drive low".
		Serial.print("setting PIN_MDIO to OUTPUT_OPEN_DRAIN\n");
		pinMode(PIN_MDIO, OUTPUT_OPEN_DRAIN);
		IS_OUTPUT = true;
	}
}

static void mdio_set_high_z()
{
	mdio_set_output();
	digitalWrite(PIN_MDIO, HIGH);
}

static int mdio_sample()
{
	return digitalRead(PIN_MDIO);
}

// Send one bit on MDIO, sampled by PHY on rising edge of MDC
static void mdio_write_bit(bool bit)
{
	digitalWrite(PIN_MDIO, bit ? HIGH : LOW);
	mdc_pulse();
}

// Read one bit from MDIO (PHY drives), sampled on rising edge (we sample after rising)
static bool mdio_read_bit()
{
	mdc_high();
	delayMicroseconds(1);
	bool b = mdio_sample();
	mdc_low();
	delayMicroseconds(1);
	return b;
}

static void mdio_write_bits(uint32_t data, int nbits)
{
	for (int i = nbits - 1; i >= 0; --i) {
		mdio_write_bit((data >> i) & 1U);
	}
}

static uint32_t mdio_read_bits(int nbits)
{
	uint32_t v = 0;
	for (int i = 0; i < nbits; ++i) {
		v = (v << 1) | (mdio_read_bit() ? 1U : 0U);
	}
	return v;
}

// Clause 22 frame:
// Preamble: 32x '1' (optional but safest)
// Start:		01
// Op:			 10 read, 01 write
// PHYAD:		5 bits
// REGAD:		5 bits
// TA:			 write=10, read=Z0 (first bit is tristate)
// DATA:		 16 bits

static void mdio_preamble()
{
	mdio_write_bits(0xFFFFFFFF, 32);
}

bool mdio_c22_write(uint8_t phy, uint8_t reg, uint16_t val)
{
	Serial.printf("mdio_c22_write(phy=%d, reg=%d, val=0x%04X)\r\n", phy, reg, val);

	mdio_set_output();

	mdio_preamble();

	// ST (start of frame)
	mdio_write_bits(0b01, 2);
	// OP (operation code)
	mdio_write_bits(0b01, 2);

	mdio_write_bits(phy & 0x1F, 5);
	mdio_write_bits(reg & 0x1F, 5);

	// During a write transaction, the STA shall drive a one bit for the first
	// bit time of the turnaround and a zero bit for the second bit time of the
	// turnaround.
	mdio_write_bits(0b10, 2);

	// write the actual data
	mdio_write_bits(val, 16);

	return true;
}

bool mdio_c22_read(uint8_t phy, uint8_t reg, uint16_t &outVal) {
	mdio_set_output();

	mdio_preamble();

	// ST (start of frame)
	mdio_write_bits(0b01, 2);
	
	// OP (operation code) 0b10 for write
	mdio_write_bits(0b10, 2);

	// PHYAD
	mdio_write_bits(phy & 0x1F, 5);
	
	// REGAD
	mdio_write_bits(reg & 0x1F, 5);

	// Turnaround for read: Z then 0 driven by PHY
	mdio_set_high_z();
	delayMicroseconds(1);
	
	// First TA bit: tristate, just clock it
	bool ta1 = mdio_sample();
	//Serial.printf("ta1: %d\r\n", ta1);

	mdc_pulse();
	
	// Second TA bit: should be 0
	bool ta2 = mdio_sample();
	//Serial.printf("ta2: %d\r\n", ta2);

	mdc_pulse();

	// DATA
	uint16_t data = 0;
	for (int i=0; i<16; i++) {
		data = (data << 1) | mdio_sample();
		mdc_pulse();
	}

	// Some PHYs might not strictly drive TA2=0 when absent; we can still return data.
	// But if TA2 is 1, it often means no device responded.
	outVal = data;
	return (ta2 == 0);
}

// ====== Clause 45 MMD access via Clause 22 regs 0x0D/0x0E ======
// Standard method:
// 1) Write 0x0D = (devad & 0x1F) | 0x0000	(addr mode)
// 2) Write 0x0E = reg
// 3) Write 0x0D = (devad & 0x1F) | 0x4000	(data mode, no post-inc)
// 4) Read/Write 0x0E for data
static bool mdio_mmd_write(uint8_t phy, uint8_t devad, uint16_t reg, uint16_t val) {
	if (!mdio_c22_write(phy, 0x0D, (uint16_t)(devad & 0x1F))) return false;
	if (!mdio_c22_write(phy, 0x0E, reg)) return false;
	if (!mdio_c22_write(phy, 0x0D, (uint16_t)((devad & 0x1F) | 0x4000))) return false;
	if (!mdio_c22_write(phy, 0x0E, val)) return false;
	return true;
}

static bool mdio_mmd_read(uint8_t phy, uint8_t devad, uint16_t reg, uint16_t &outVal) {
	if (!mdio_c22_write(phy, 0x0D, (uint16_t)(devad & 0x1F))) return false;
	if (!mdio_c22_write(phy, 0x0E, reg)) return false;
	if (!mdio_c22_write(phy, 0x0D, (uint16_t)((devad & 0x1F) | 0x4000))) return false;
	uint16_t v = 0;
	bool ok = mdio_c22_read(phy, 0x0E, v);
	outVal = v;
	return ok;
}

// ====== SERIAL PARSING ======

static bool parse_u32(const char *s, uint32_t &out)
{
	//Serial.printf("parse_u32(\"%s\", 0x%X);\r\n", s, out);
	
	if (!s || !*s) {
		Serial.println("ERROR: parsing, string is NULL or empty");
		return false;
	}

	char *endp = nullptr;
	unsigned long v = strtoul(s, &endp, 0); // base 0 supports 0x

	if (endp == s) {
		Serial.println("ERROR: strtoul() messed up");
		return false;
	}

	out = (uint32_t)v;
	return true;
}

static void print_help() {
	Serial.println("MDIO Serial Commands:");
	Serial.println("	r <phy> <reg>							Read Clause22 reg");
	Serial.println("	w <phy> <reg> <value>			Write Clause22 reg");
	Serial.println("	mmdr <phy> <devad> <reg>	 Read MMD (Clause45 via 0x0D/0x0E)");
	Serial.println("	mmdw <phy> <devad> <reg> <value>	Write MMD");
	Serial.println("	scan											 Scan PHY addrs 0..31 (reads reg1)");
	Serial.println("	help");
	Serial.println("Notes: numbers can be decimal or hex (0x....).");
}

static void do_scan()
{
	Serial.println("Scanning PHY addresses (reading reg 1 / BMSR)...");
	for (int phy = 0; phy < 32; ++phy) {
		uint16_t v = 0;
		bool ok;

		// Heuristic: if no response, often you get 0xFFFF or TA not ok.
		ok = mdio_c22_read((uint8_t)phy, 0, v);
		if (ok && v != 0xFFFF) {
			Serial.printf("	PHY %d: REG0: 0x%04X\r\n", phy, v);
		}
		ok = mdio_c22_read((uint8_t)phy, 0, v);
		if (ok && v != 0xFFFF) {
			Serial.printf("	PHY %d: REG0: 0x%04X\r\n", phy, v);
		}
		
		ok = mdio_c22_read((uint8_t)phy, 1, v);
		if (ok && v != 0xFFFF) {
			Serial.printf("	PHY %d: REG1: 0x%04X\r\n", phy, v);
		}
		ok = mdio_c22_read((uint8_t)phy, 1, v);
		if (ok && v != 0xFFFF) {
			Serial.printf("	PHY %d: REG1: 0x%04X\r\n", phy, v);
		}

		ok = mdio_c22_read((uint8_t)phy, 2, v);
		if (ok && v != 0xFFFF) {
			Serial.printf("	PHY %d: REG2: 0x%04X\r\n", phy, v);
		}
		ok = mdio_c22_read((uint8_t)phy, 2, v);
		if (ok && v != 0xFFFF) {
			Serial.printf("	PHY %d: REG2: 0x%04X\r\n", phy, v);
		}

		ok = mdio_c22_read((uint8_t)phy, 3, v);
		if (ok && v != 0xFFFF) {
			Serial.printf("	PHY %d: REG3: 0x%04X\r\n", phy, v);
		}
		ok = mdio_c22_read((uint8_t)phy, 3, v);
		if (ok && v != 0xFFFF) {
			Serial.printf("	PHY %d: REG3: 0x%04X\r\n", phy, v);
		}
	}
	Serial.println("Done.");
}

static void handle_line(char *line) {
	// Tokenize
	const int MAXTOK = 6;
	char *tok[MAXTOK] = {0};
	int n = 0;

	for (char *p = strtok(line, " \t\r\n"); p && n < MAXTOK; p = strtok(nullptr, " \t\r\n")) {
		tok[n++] = p;
	}
	if (n == 0) return;

	if (!strcmp(tok[0], "help") || !strcmp(tok[0], "?")) {
		print_help();
		return;
	}
	
	if (!strcmp(tok[0], "scan")) {
		do_scan();
		return;
	}

	if (!strcmp(tok[0], "input")) {
		Serial.println("calling mdio_set_input()");
		mdio_set_input();
		return;
	}

	if (!strcmp(tok[0], "output")) {
		Serial.println("calling mdio_set_output()");
		mdio_set_output();
		digitalWrite(PIN_MDIO, HIGH);
		return;
	}

	if (!strcmp(tok[0], "r") && n >= 3) {
		uint32_t phy, reg;
		if (!parse_u32(tok[1], phy) || !parse_u32(tok[2], reg)) {
			Serial.println("ERR parse");
			return;
		}
		uint16_t v = 0;
		bool ok = mdio_c22_read((uint8_t)phy, (uint8_t)reg, v);
		//Serial.printf("RD phy=%u reg=%u -> 0x%04X %s\n", phy, reg, v, ok ? "OK" : "NOACK");
		Serial.printf("%04X\r\n", v);
		return;
	}

	if (!strcmp(tok[0], "w") && n >= 4) {
		uint32_t phy=0, reg=0, val=0;
		if (!parse_u32(tok[1], phy) || !parse_u32(tok[2], reg) || !parse_u32(tok[3], val)) {
			Serial.println("ERR parse");
			return;
		}
		
		Serial.printf("phy=%u reg=%u val=0x%04X\r\n", phy, reg, val);

		bool ok = mdio_c22_write(phy, reg, val);

		Serial.printf("WR phy=%u reg=%u val=0x%04X -> %s\r\n", phy, reg, (uint16_t)val, ok ? "OK" : "FAIL");
		return;
	}

	if (!strcmp(tok[0], "mmdr") && n >= 4) {
		uint32_t phy, devad, reg;
		if (!parse_u32(tok[1], phy) || !parse_u32(tok[2], devad) || !parse_u32(tok[3], reg)) {
			Serial.println("ERR parse");
			return;
		}
		uint16_t v = 0;
		bool ok = mdio_mmd_read((uint8_t)phy, (uint8_t)devad, (uint16_t)reg, v);
		Serial.printf("MMDR phy=%u dev=%u reg=0x%04X -> 0x%04X %s\r\n", phy, devad, (uint16_t)reg, v, ok ? "OK" : "NOACK");
		return;
	}

	if (!strcmp(tok[0], "mmdw") && n >= 5) {
		uint32_t phy, devad, reg, val;
		if (!parse_u32(tok[1], phy) || !parse_u32(tok[2], devad) || !parse_u32(tok[3], reg) || !parse_u32(tok[4], val)) {
			Serial.println("ERR parse");
			return;
		}
		bool ok = mdio_mmd_write((uint8_t)phy, (uint8_t)devad, (uint16_t)reg, (uint16_t)val);
		Serial.printf("MMDW phy=%u dev=%u reg=0x%04X val=0x%04X -> %s\r\n", phy, devad, (uint16_t)reg, (uint16_t)val, ok ? "OK" : "FAIL");
		return;
	}

	Serial.println("ERR unknown cmd. Type 'help'. B");
}

// Simple line buffer
static char linebuf[128];
static size_t linelen = 0;

void setup()
{
	Serial.begin(115200);
	delay(200);

	while (Serial.available()) {
		Serial.read();
	}

	Serial.print("setup entry\n");

	// clock starts low
	pinMode(PIN_MDC, OUTPUT);
	mdc_low();

	// IO starts high-z (should be pulled up)
	IS_OUTPUT = false;
	mdio_set_output();
	digitalWrite(PIN_MDIO, HIGH);

	Serial.println("");
	Serial.println("ESP32 MDIO controller ready. Type 'help'. A");
}

static bool prompt_needed = true;

void loop()
{
	//Serial.print("loop entry\n");
	
	if (prompt_needed) {
		Serial.print("TOOL>");
		prompt_needed = false;
	}

	if (Serial.available()) {	
		char c = (char)Serial.read();
		if (c == '\n' || c == '\r') {
			if (linelen > 0) {
				linebuf[linelen] = 0;

				//sprintf(buf, "calling handle_line(\"%s\");\n", linebuf);
				//Serial.print(buf);

				handle_line(linebuf);
				prompt_needed = true;
				linelen = 0;
			}
		} else {
			if (linelen + 1 < sizeof(linebuf)) {
				linebuf[linelen++] = c;
			} else {
				// overflow: reset
				linelen = 0;
			}
		}
	}

	//Serial.print("loop exit\n");
}
