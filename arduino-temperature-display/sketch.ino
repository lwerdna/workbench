#include "DHT.h"

#define DHTTYPE DHT11

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

void one()
{
  digitalWrite(segA, LOW);
  digitalWrite(segB, HIGH);
  digitalWrite(segC, HIGH);
  digitalWrite(segD, LOW);
  digitalWrite(segE, LOW);
  digitalWrite(segF, LOW);
  digitalWrite(segG, LOW);
  digitalWrite(segPt, LOW);
}

void two()
{
  digitalWrite(segA, HIGH);
  digitalWrite(segB, HIGH);
  digitalWrite(segC, LOW);
  digitalWrite(segD, HIGH);
  digitalWrite(segE, HIGH);
  digitalWrite(segF, LOW);
  digitalWrite(segG, HIGH);
  digitalWrite(segPt, LOW);
}

void three()
{
  digitalWrite(segA, HIGH);
  digitalWrite(segB, HIGH);
  digitalWrite(segC, HIGH);
  digitalWrite(segD, HIGH);
  digitalWrite(segE, LOW);
  digitalWrite(segF, LOW);
  digitalWrite(segG, HIGH);
  digitalWrite(segPt, LOW);
}

void four()
{
  digitalWrite(segA, LOW);
  digitalWrite(segB, HIGH);
  digitalWrite(segC, HIGH);
  digitalWrite(segD, LOW);
  digitalWrite(segE, LOW);
  digitalWrite(segF, HIGH);
  digitalWrite(segG, HIGH);
  digitalWrite(segPt, LOW);
}

void five()
{
  digitalWrite(segA, HIGH);
  digitalWrite(segB, LOW);
  digitalWrite(segC, HIGH);
  digitalWrite(segD, HIGH);
  digitalWrite(segE, LOW);
  digitalWrite(segF, HIGH);
  digitalWrite(segG, HIGH);
  digitalWrite(segPt, LOW);
}

void six()
{
  digitalWrite(segA, HIGH);
  digitalWrite(segB, LOW);
  digitalWrite(segC, HIGH);
  digitalWrite(segD, HIGH);
  digitalWrite(segE, HIGH);
  digitalWrite(segF, HIGH);
  digitalWrite(segG, HIGH);
  digitalWrite(segPt, LOW);
}

void seven()
{
  digitalWrite(segA, HIGH);
  digitalWrite(segB, HIGH);
  digitalWrite(segC, HIGH);
  digitalWrite(segD, LOW);
  digitalWrite(segE, LOW);
  digitalWrite(segF, LOW);
  digitalWrite(segG, LOW);
  digitalWrite(segPt, LOW);
}

void eight()
{
  digitalWrite(segA, HIGH);
  digitalWrite(segB, HIGH);
  digitalWrite(segC, HIGH);
  digitalWrite(segD, HIGH);
  digitalWrite(segE, HIGH);
  digitalWrite(segF, HIGH);
  digitalWrite(segG, HIGH);
  digitalWrite(segPt, LOW);
}

void nine()
{
  digitalWrite(segA, HIGH);
  digitalWrite(segB, HIGH);
  digitalWrite(segC, HIGH);
  digitalWrite(segD, HIGH);
  digitalWrite(segE, LOW);
  digitalWrite(segF, HIGH);
  digitalWrite(segG, HIGH);
  digitalWrite(segPt, LOW);
}

void zero()
{
  digitalWrite(segA, HIGH);
  digitalWrite(segB, HIGH);
  digitalWrite(segC, HIGH);
  digitalWrite(segD, HIGH);
  digitalWrite(segE, HIGH);
  digitalWrite(segF, HIGH);
  digitalWrite(segG, LOW);
  digitalWrite(segPt, LOW);
}

void clear()
{
  digitalWrite(segA, LOW);
  digitalWrite(segB, LOW);
  digitalWrite(segC, LOW);
  digitalWrite(segD, LOW);
  digitalWrite(segE, LOW);
  digitalWrite(segF, LOW);
  digitalWrite(segG, LOW);
  digitalWrite(segPt, LOW);
}

void point()
{
  digitalWrite(segPt, HIGH);
}

void selectDigit(int d)
{
  switch (d)
  {
    case 1:
      digitalWrite(d1, LOW);
      break;
    case 2:
      digitalWrite(d2, LOW);
      break;
    case 3:
      digitalWrite(d3, LOW);
      break;
    default:
      digitalWrite(d4, LOW);
      break;
  }
}

void deselectDigit(int d)
{
  switch (d)
  {
    case 1:
      digitalWrite(d1, HIGH);
      break;
    case 2:
      digitalWrite(d2, HIGH);
      break;
    case 3:
      digitalWrite(d3, HIGH);
      break;
    default:
      digitalWrite(d4, HIGH);
      break;
  }
}

void sendDigit(int x)
{
  switch(x)
  {
    case 1: one(); break;
    case 2: two(); break;
    case 3: three(); break;
    case 4: four(); break;
    case 5: five(); break;
    case 6: six();  break;
    case 7: seven(); break;
    case 8: eight(); break;
    case 9: nine(); break;
    default: zero(); break;
  }
}

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

void KYX5461AS_select_raw(int lohi1, int lohi2, int lohi3, int lohi4)
{
  digitalWrite(d1, lohi1 ? HIGH : LOW);
  digitalWrite(d2, lohi2 ? HIGH : LOW);
  digitalWrite(d3, lohi3 ? HIGH : LOW);
  digitalWrite(d4, lohi4 ? HIGH : LOW);
}

void KYX5461AS_select_digit(int displayDigit)
{
  switch(displayDigit)
  {
    case 1: KYX5461AS_select_raw(0, 1, 1, 1); break;
    case 2: KYX5461AS_select_raw(1, 0, 1, 1); break;
    case 3: KYX5461AS_select_raw(1, 1, 0, 1); break;
    case 4: KYX5461AS_select_raw(1, 1, 1, 0); break;
  }
}

void KYX5461AS_deselect_digit(int displayDigit)
{
  switch(displayDigit)
  {
    case 1: digitalWrite(d1, HIGH); break;
    case 2: digitalWrite(d2, HIGH); break;
    case 3: digitalWrite(d3, HIGH); break;
    case 4: digitalWrite(d4, HIGH); break;
  }
}

void KYX5461AS_print(int numToPrint, int displayDigit, bool point=false)
{
  int pinAstate, pinBstate, pinCstate, pinDstate, pinEstate, pinFstate, pinGstate;
  switch(numToPrint) {
    case 0:
      pinAstate = HIGH;   
      pinBstate = HIGH;   
      pinCstate = HIGH;   
      pinDstate = HIGH;   
      pinEstate = HIGH;   
      pinFstate = HIGH;   
      pinGstate = LOW;
      break;
    case 1:
      pinAstate = LOW;   
      pinBstate = HIGH;   
      pinCstate = HIGH;   
      pinDstate = LOW;   
      pinEstate = LOW;   
      pinFstate = LOW;   
      pinGstate = LOW;
      break;
    case 2:
      pinAstate = HIGH;   
      pinBstate = HIGH;   
      pinCstate = LOW;   
      pinDstate = HIGH;   
      pinEstate = HIGH;   
      pinFstate = LOW;   
      pinGstate = HIGH;
      break;
    case 3:
      pinAstate = HIGH;   
      pinBstate = HIGH;   
      pinCstate = HIGH;   
      pinDstate = HIGH;   
      pinEstate = LOW;   
      pinFstate = LOW;   
      pinGstate = HIGH;
      break;
    case 4:
      pinAstate = LOW;   
      pinBstate = HIGH;   
      pinCstate = HIGH;   
      pinDstate = LOW;   
      pinEstate = LOW;   
      pinFstate = HIGH;   
      pinGstate = HIGH;
      break;
    case 5:
      pinAstate = HIGH;   
      pinBstate = LOW;   
      pinCstate = HIGH;   
      pinDstate = HIGH;   
      pinEstate = LOW;   
      pinFstate = HIGH;   
      pinGstate = HIGH;
      break;
    case 6:
      pinAstate = HIGH;   
      pinBstate = LOW;   
      pinCstate = HIGH;   
      pinDstate = HIGH;   
      pinEstate = HIGH;   
      pinFstate = HIGH;   
      pinGstate = HIGH;
      break;
    case 7:
      pinAstate = HIGH;   
      pinBstate = HIGH;   
      pinCstate = HIGH;   
      pinDstate = LOW;   
      pinEstate = LOW;   
      pinFstate = LOW;   
      pinGstate = LOW;
      break;
    case 8:
      pinAstate = HIGH;   
      pinBstate = HIGH;   
      pinCstate = HIGH;   
      pinDstate = HIGH;   
      pinEstate = HIGH;   
      pinFstate = HIGH;   
      pinGstate = HIGH;
      break;
    case 9:
      pinAstate = HIGH;   
      pinBstate = HIGH;   
      pinCstate = HIGH;   
      pinDstate = HIGH;   
      pinEstate = LOW;   
      pinFstate = HIGH;   
      pinGstate = HIGH;
      break;
     case 0xF:
      pinAstate = HIGH;   
      pinBstate = LOW;   
      pinCstate = LOW;   
      pinDstate = LOW;   
      pinEstate = HIGH;   
      pinFstate = HIGH;   
      pinGstate = HIGH;
      break;
  }

  digitalWrite(segA, pinAstate);   
  digitalWrite(segB, pinBstate);   
  digitalWrite(segC, pinCstate);   
  digitalWrite(segD, pinDstate);   
  digitalWrite(segE, pinEstate);   
  digitalWrite(segF, pinFstate);   
  digitalWrite(segG, pinGstate);
  digitalWrite(segPt, point ? HIGH : LOW);

  KYX5461AS_select_digit(displayDigit);
  delay(4);
  KYX5461AS_deselect_digit(displayDigit);  
}

// the setup function runs once when you press reset or power the board
void setup() {
  // initialize digital pin LED_BUILTIN as an output.
  Serial.begin(9600);
  //pinMode(0, INPUT);
  pinMode(LED_BUILTIN, OUTPUT);
  //pinMode(14, INPUT)
  dht.begin();

  // seven segment setup
  pinMode(segA, OUTPUT);
  pinMode(segB, OUTPUT);
  pinMode(segC, OUTPUT);
  pinMode(segD, OUTPUT);
  pinMode(segE, OUTPUT);
  pinMode(segF, OUTPUT);
  pinMode(segG, OUTPUT);
  pinMode(segPt, OUTPUT);
  pinMode(d1, OUTPUT);
  pinMode(d2, OUTPUT);
  pinMode(d3, OUTPUT);
  pinMode(d4, OUTPUT);
}

float last_temp = 0;

int digit1 = 0;
int digit2 = 0;
int digit3 = 0;
int digit4 = 0;
  
// the loop function runs over and over again forever
void loop() {
  float f = dht.readTemperature(true);

 
  if(last_temp != f) { 
    digit1 = tens(f);
    digit2 = ones(f);
    digit3 = tenths(f);
    last_temp = f;
  }
  
  KYX5461AS_print(digit1, 1);
  KYX5461AS_print(digit2, 2, true);
  KYX5461AS_print(digit3, 3);
  KYX5461AS_print(0xF, 4);

  if(f > 78) {
    digitalWrite(LED_BUILTIN, HIGH);   // turn the LED on (HIGH is the voltage level)
  }
  else {
    digitalWrite(LED_BUILTIN, LOW);    // turn the LED off by making the voltage LOW
  }
  
  Serial.print("temperature is ");
  Serial.println(f);
}
