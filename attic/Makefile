
YOSYS_EXTENSION_LDLIBS = -lstdc++ -lm -lrt -lreadline -lffi -ldl -lz -ltcl8.6 -ltclstub8.6

YOSYS_EXTENSION_CFLAGS = -Wall -Wextra -ggdb -I/home/dlbraun/.local/share/yosys/include -MD -MP -D_YOSYS_ -fPIC -I/usr/local/include -std=c++11 -Os -DYOSYS_ENABLE_READLINE -DYOSYS_ENABLE_PLUGINS -DYOSYS_ENABLE_GLOB -DYOSYS_ENABLE_ZLIB -DYOSYS_ENABLE_TCL -DYOSYS_ENABLE_ABC -DYOSYS_ENABLE_COVER -rdynamic


doug_smash.so: doug_smash.cc dummy.cc
	gcc $(YOSYS_EXTENSION_CFLAGS) -o $@ -shared $^ $(YOSYS_EXTENSION_LDLIBS)

modules:  doug_smash.so

%.so: %.cc 
	gcc $(YOSYS_EXTENSION_CFLAGS) -o $@ -shared $< $(YOSYS_EXTENSION_LDLIBS)


#   yosys-config --build $@ $<

