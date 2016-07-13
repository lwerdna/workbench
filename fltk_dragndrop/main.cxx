#include <stdio.h>

#include <FL/Fl.H>
#include <FL/Fl_Window.H>

class MyWin : public Fl_Window 
{
    public:
    MyWin(int x, int y, int w, int h):
        Fl_Window(x, y, w, h)
    {
        printf("MyWin constructor\n");
    }

    int handle(int event)
    {
        int rc = 0; /* 0 if not used or understood, 1 if event was used and can be deleted */
   

        switch(event) {
            case FL_DND_ENTER:
            case FL_DND_DRAG:
            case FL_DND_RELEASE:
                printf("showing interest\n");
                rc = 1;
                break;

            case FL_PASTE:
                printf("got paste event");
                printf("event text: %s\n", Fl::event_text());
                printf("event length: %d\n", Fl::event_length());
                rc = 1;
                break;

            default:
                while(0);
                //printf("got event id: %d\n", event);
        }
    
        return rc;
    }   
};

/*
    MAIN
*/
int main(int ac, char **av)
{
    /* create the window */
    MyWin *winMain = new MyWin(32, 32, 640, 480);
    winMain->end();
    winMain->show();

    /* this will return when all windows are hidden
        eg: fltk::Window::hide() */
    return Fl::run();
}

