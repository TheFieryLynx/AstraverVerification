#include "map.h"

// 0 - ошибка
// 1 - верно

int initializeMap(Map *map, int size) {
    if (size <= 0) {
        return 0;
    }
    map->capacity = size;
    map->count = 0;
    map->items = calloc(map->capacity, sizeof(Item));
    if (map->items == NULL) {
        return 0;
    }
    for (int i = 0; i < map->capacity; ++i) {
        map->items[i].existent = 0;
    }
    return 1;
}

void finalizeMap(Map *map) {
    free(map->items);
}

int addElement(Map *map, Key *key, Value *value) {
    for (int i = 0; i < map->capacity; ++i) {
        if (map->items[i].key.a == key->a &&
            map->items[i].key.b == key->b) {
                map->items[i].value = *value;
                return 1;
            }
    }
    for (int i = 0; i < map->capacity; ++i) {
        if (map->items[i].existent == 0) {
            map->items[i].key = *key;
            map->items[i].value = *value;
            map->items[i].existent = 1;
            map->count = map->count + 1;
            return 1;
        }
    }
    return 0;
}

int removeElement(Map *map, Key *key, Value *value) {
    for (int i = 0; i < map->capacity; ++i) {
        if (map->items[i].key.a == key->a &&
            map->items[i].key.b == key->b) {
            if (value != NULL) {
                *value = map->items[i].value;
            }
            map->items[i].existent = 0;
            map->count--;

            // зачем сдвигать все, если можно переместить последний
            // на место удаленного :)
            int j = i + 1;
            while (j < map->capacity) {
                if (map->items[j].existent == 0) {
                    if (j == i + 1) {
                        return 1;
                    }
                    map->items[i].key = map->items[j - 1].key;
                    map->items[i].value = map->items[j - 1].value;
                    map->items[i].existent = 1;
                    map->items[j - 1].existent = 0;
                    // чтоб выглядело как будто там ничего нет (косметика - мб удалю потом)
                    map->items[j - 1].key.a = 0;
                    map->items[j - 1].key.b = 0;
                    map->items[j - 1].value.c = 0;
                    map->items[j - 1].value.d = 0;
                    return 1;
                }
                j++;
            }
            return 1;
        }
    }
    return 0;
}

int getElement(Map *map, Key *key, Value *value) {
    for (int i = 0; i < map->capacity; ++i) {
        if (map->items[i].key.a == key->a && map->items[i].key.b == key->b) {
            *value = map->items[i].value;
            return 1;
        }
    }
    return 0;
}