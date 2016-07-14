#include "Gui.h"

int main(int ac, char **av)
{
    UserInterface ui;

    Fl_Double_Window *w = ui.make_window();
    w->end();
    w->show();

    return Fl::run();
}
