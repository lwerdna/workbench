#include "Gui.h"
#include "algo.h"

int main(int ac, char **av)
{
    Gui *g = new Gui();

    g->show(ac, av);

    return Fl::run();
}
