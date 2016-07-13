CXX      = $(shell fltk-config --cxx)
DEBUG    = -g
CXXFLAGS = $(shell fltk-config --use-gl --use-images --cxxflags ) -I.
LDFLAGS  = $(shell fltk-config --use-gl --use-images --ldflags )
LDSTATIC = $(shell fltk-config --use-gl --use-images --ldstaticflags )
LINK     = $(CXX)

TARGET = keygen
OBJS = main.o Gui.o algo.o
SRCS = main.cxx Gui.cxx algo.cxx

.SUFFIXES: .o .cxx
%.o: %.cxx
	$(CXX) $(CXXFLAGS) $(DEBUG) -c $<

all: $(TARGET)
	$(LINK) -o $(TARGET) $(OBJS) $(LDSTATIC)

$(TARGET): $(OBJS)
main.o: main.cxx
Gui.o: Gui.cxx Gui.h
algo.o: algo.cxx algo.h

clean: $(TARGET) $(OBJS)
	rm -f *.o 2> /dev/null
	rm -f $(TARGET) 2> /dev/null
