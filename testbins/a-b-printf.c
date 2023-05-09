void common() { }
void A() { common(); }
void B() { common(); }
int main(int ac, char **av) { A(); B(); return 0; }
