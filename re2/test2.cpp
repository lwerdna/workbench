#include <iostream>
#include <string>
#include <re2/re2.h>
#include <vector>

using namespace std;

void test_fullmatch(){
  string s,t;
  string str("あぶらかたぶら");
  re2::StringPiece input(str);
  re2::RE2 re("(.ら).(.ぶ)");

  if(re2::RE2::FullMatch(input, re , &s, &t))
    cout << "s:"<< s << " t:"<< t << endl;
  else
    cout << "Not match." << endl;
  
  if(re2::RE2::FullMatch(input, ".(.ら).(.ぶ)." , &s, &t))
    cout << "s:"<< s << " t:"<< t << endl;
  else
    cout << "Not match." << endl;
  
}

void test_partialmatch(){
  string s,t;
  string str("あぶらかたぶら");
  re2::StringPiece input(str);
  re2::RE2 re("(.ら).(.ぶ)");

  if(re2::RE2::PartialMatch(input, re , &s, &t))
    cout << "s:"<< s << " t:"<< t << endl;
}

void test_partialmatchn(){
  string str("abcadca");
  re2::RE2 re("((a.)(..))");
  re2::StringPiece input(str);
  int groupSize = re.NumberOfCapturingGroups();
  vector<re2::RE2::Arg> argv(groupSize);
  vector<re2::RE2::Arg*> args(groupSize);  
  vector<re2::StringPiece> ws(groupSize);  
  for (int i = 0; i < groupSize; ++i) {  
    args[i] = &argv[i];  
    argv[i] = &ws[i];  
  }  
  re2::RE2::PartialMatchN(input, re, &(args[0]), groupSize);  
  cout << groupSize << endl;
  string s;
  for (int i = 0; i < groupSize; ++i){
    cout << ws[i] << endl;
  }
}

void test_findandconsume(){
  string str("あぶらかたぶら");
  RE2 re("(.ぶ)");
  re2::StringPiece input(str);
  string r;
  while(re2::RE2::FindAndConsume(&input, re, &r) ){
    cout << r << endl;
  }
}

void test_replace(){
  string s = "PerlRubyPython";
  re2::RE2::Replace(&s, "P", "D");
  cout << s << endl;
}

void test_globalreplace(){
  string s = "PerlRubyPython";
  re2::RE2::GlobalReplace(&s, "P", "D");
  cout << s << endl;
}

void test_extract(){
  string s;
  RE2::Extract("foo@bar.com", "(.*)@([^.]*)", "In domain \"\\2\", user \"\\1\" is exist!", &s);
  cout << s << endl;
}

int main(int argc, char **argv){
  cout << "test FullMatch" << endl;
  test_fullmatch();

  cout << "test PartialMatch" << endl;
  test_partialmatch();

  cout << "test PartialMatchN" << endl;
  test_partialmatchn();

  cout << "test FindAndConsume" << endl;
  test_findandconsume();

  cout << "test Replace" << endl;
  test_replace();

  cout << "test GlobalReplace" << endl;
  test_globalreplace();

  cout << "test Extract" << endl;
  test_extract();

  return 0;
}
