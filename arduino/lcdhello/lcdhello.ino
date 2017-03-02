
// include the library code:
#include <LiquidCrystal.h>

int counter = 0;
int ledPin = 13;

// initialize the library with the numbers of the interface pins
LiquidCrystal lcd(12, /* register select */
                11, /* enable */
                5, 4, 3, 2 /* to LCD's d4, d5, d6, d7 */
              );

void setup() {
  // set up the LCD's number of columns and rows:
  lcd.begin(16, 2);
  lcd.write("HELLO, WORLD!");
}

void loop() {
  //lcd.clear();

  /*
  while(1) {
    if((counter & 0xFFF)==0) {
      lcd.home();
      lcd.print(counter);
    }
    counter += 1;
  }
  */
}
