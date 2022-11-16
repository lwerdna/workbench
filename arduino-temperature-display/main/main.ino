#include "DHT.h"

DHT dht(14, DHT11);

int segA = 2;
int segB = 3;
int segC = 4;
int segD = 5;
int segE = 6;
int segF = 7;
int segG = 8;
int segPt = 9;

int d1 = 10;
int d2 = 11;
int d3 = 12;
int d4 = 13;

int hundreds(float x)
{
	return (int) (x / 100.0);
}

int tens(float x)
{
	int result = ((int) (x/10.0)) % 10;
	Serial.print("tens: ");
	Serial.println(result);
	return result;
}

int ones(float x)
{
	int result = ((int) x) % 10;
	Serial.print("ones: ");
	Serial.println(result);
	return result;
}

int tenths(float x)
{
	int result = ((int) (x * 10)) % 10;
	Serial.print("tenths: ");
	Serial.println(result);
	return result;
}

int hundredths(float x)
{
	int result = ((int) (x * 10)) % 10;
	Serial.print("hundredths: ");
	Serial.println(result);
	return result;
}

int points(float x)
{
	float divided = x - (10.0 * tens(x)) - ones(x);
	divided *= 10;
	return (int)divided;
}

byte current_data[4] = {0, 0, 0, 0};
int position = 0;
byte pins_seg[8] = { segA, segB, segC, segD, segE, segF, segG, segPt };
byte pins_dig[4] = { d1, d2, d3, d4 };
byte patterns[16] = {
	0b00111111, 0b00000110, 0b01011011, 0b01001111, /* 0, 1, 2, 3 */
	0b00110011, 0b01011011, 0b01011111, 0b01110000, /* 4, 5, 6, 7 */
	0b01111111, 0b01111011, 0b00000000, 0b00000000, /* 8, 9, A, B */
	0b00000000, 0b00000000, 0b00000000, 0b01111001  /* C, D, E, F */
};

void KYX5461AS_setup()
{
	/* set segment pins and digit select pins to output */
	for (int i=0; i<8; i++)
		pinMode(pins_seg[i], OUTPUT);

	for (int i=0; i<4; i++)
		pinMode(pins_dig[i], OUTPUT);

	/* disable any digit selection */
	for (int i=0; i<4; i++)
		digitalWrite(pins_dig[i], HIGH);

	/* set last digit to 0 */
	position = 0;
}

void KYX5461AS_debug()
{
	char buf[256];
	sprintf(buf, "position=%d, digit enable pins = (%d, %d, %d, %d)",
		position,
		digitalRead(pins_dig[0]), digitalRead(pins_dig[1]),
		digitalRead(pins_dig[2]), digitalRead(pins_dig[3]));
	Serial.println(buf);
}

int first = 1;
void KYX5461AS_loop()
{
	/* disable current digit, move to next */
	digitalWrite(pins_dig[position], HIGH);

	position = (position + 1) % 4;

	/* set the segments */
	if(1) {
		byte pattern = current_data[position];
		for(int i=0; i<8; ++i)
			digitalWrite(pins_seg[i], (pattern >> i) & 1 ? HIGH : LOW);
		first = 0;
	}

	/* enable current position */
	digitalWrite(pins_dig[position], LOW);
}

// value in {0, 1, 2, ..., 15}
// position in {0, 1, 2, 3} where 0 is leftmost digit, 3 is rightmost
void KYX5461AS_set(byte value, byte position, bool point=false)
{
	if (position >= 4)
		return;
	if (value >= 16)
		return;

	current_data[position] = patterns[value];

	if (point)
		current_data[position] |= 0b10000000;
}

void setup() {
	// initialize digital pin LED_BUILTIN as an output.
	Serial.begin(9600);
	pinMode(LED_BUILTIN, OUTPUT);

	//dht.begin();

	KYX5461AS_setup();
}

float last_temp = 0;

void loop() {
	//float f = dht.readTemperature(true);

		KYX5461AS_set(0, 0);
		KYX5461AS_set(1, 1);
		KYX5461AS_set(2, 2);
		KYX5461AS_set(3, 3);

	//if(last_temp != f) {
	if (0)
	{
		//last_temp = f;

		KYX5461AS_set(0, 0);
		KYX5461AS_set(1, 1);
		KYX5461AS_set(2, 2);
		KYX5461AS_set(3, 3);

/*
		KYX5461AS_set(tens(f), 3);
		KYX5461AS_set(ones(f), 2, true);
		KYX5461AS_set(tenths(f), 1);
		KYX5461AS_set(0xF, 0);
*/
		//Serial.print("temperature updated to: ");
		//Serial.println(f);
	}

/*
	if(f > 74)
		digitalWrite(LED_BUILTIN, HIGH);
	else
		digitalWrite(LED_BUILTIN, LOW);
*/
	KYX5461AS_loop();
}
