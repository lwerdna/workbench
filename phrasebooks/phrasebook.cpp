// This example illustrates explicit initialization
// by constructor.
#include <iostream>
using namespace std;

class complex {
  double re, im;
public:

  // default constructor
  complex() : re(0), im(0) { }

  // copy constructor
  complex(const complex& c) { re = c.re; im = c.im; }

  // constructor with default trailing argument
  complex( double r, double i = 0.0) { re = r; im = i; }

  void display() {
    cout << "re = "<< re << " im = " << im << endl;
  }
};

int main() {

  // initialize with complex(double, double)
  complex one(1);

  // initialize with a copy of one
  // using complex::complex(const complex&)
  complex two = one;

  // construct complex(3,4)
  // directly into three
  complex three = complex(3,4);

  // initialize with default constructor
  complex four;

  // complex(double, double) and construct
  // directly into five
  complex five = 5;

  one.display();
  two.display();
  three.display();
  four.display();
  five.display();
}
