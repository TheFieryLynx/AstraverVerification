SOURCE=main.c map.c test.c
TARGET=main

CFLAGS = -I. -Wall -std=c99 -g

all: $(TARGET)

cov: $(TARGET)-cov

$(TARGET): $(SOURCE)
	gcc $(CFLAGS) -o $@ -I. $^

$(TARGET)-cov: $(SOURCE)
	gcc $(CFLAGS) --coverage -o $(TARGET) -I. $^

run: all
	./$(TARGET)

clean:
	rm -rf $(TARGET)

valgrind: all
	valgrind ./$(TARGET)

gcov: cov
	valgrind ./$(TARGET) --track-origins=yes -s
	lcov -t "$(TARGET)" -o $(TARGET).info -c -d .
	genhtml -o $(TARGET)-lcov-report $(TARGET).info

clean:
	rm -rf $(TARGET) $(TARGET).gcno $(TARGET).gcda $(TARGET).info $(TARGET)-lcov-report
	rm -rf *.gcno *.gcda