.PHONY: all clean watch

SOURCE := $(wildcard *.c)
TARGET := main

CFLAGS += -Wall -Wextra -Wpedantic -ggdb -std=c11

all: $(TARGET)

main.o: main.c lib.c

clean:
	rm -fv -- $(TARGET) $(wildcard *.o)

watch:
	while true ; do \
		inotifywait -qr -e close_write $(SOURCE) ; \
		clear ; \
		make all ; \
		echo ; echo ; echo ; echo ; \
	done
