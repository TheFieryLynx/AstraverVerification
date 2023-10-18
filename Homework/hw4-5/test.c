#include "test.h"

// 0 

// если size <= 0 то должно вернуть ошибку
int test_zero_size() {
    Map *map = malloc(sizeof(Map));
    int size = 0;
    int res = initializeMap(map, size);
    if (res == 1) {
        free(map);
        return 0;
    }
    free(map);
    return 1;
}

// size > 0 и все интитися верно
int test_init() {
    Map *map = malloc(sizeof(Map));
    int size = 5;
    int res = initializeMap(map, size);

    if (res == 1) {
        finalizeMap(map);
        free(map);
        return 1;
    }

    if (map->capacity != 5) {
        finalizeMap(map);
        free(map);
        return -1;
    }
    if (map->count != 0) {
        finalizeMap(map);
        free(map);
        return -1;
    }
    for (int i = 0; i < map->capacity; ++i) {
        if (map->items[i].existent != 0) {
            finalizeMap(map);
            free(map);
            return -1;
        }
    }
    finalizeMap(map);
    free(map);
    return 0;
}

// добавление в пустой
int test_add_elem_empty_map() {
    Map *map = malloc(sizeof(Map));
    int size = 5;
    int res = initializeMap(map, size);
    
    if (res == 1) {
        finalizeMap(map);
        free(map);
        return 1;
    }

    Key k;
    k.a = 1;
    k.b = 2;

    Value v;
    v.c = 3;
    v.d = 4;

    // добавляем элемент
    res = addElement(map, &k, &v);
    if (res == 0) {
        finalizeMap(map);
        free(map);
        return -1;
    }

    if (map->count != 1) {
        finalizeMap(map);
        free(map);
        return -1;
    }

    // читаем элемент
    Value retv;
    res = getElement(map, &k, &retv);
    if (res == 0) {
        finalizeMap(map);
        free(map);
        return -1;
    }

    if (retv.c != v.c || retv.d != v.d) {
        finalizeMap(map);
        free(map);
        return -1;
    }

    finalizeMap(map);
    free(map);
    return 0;
}

// изменяем уже существующий
int test_add_elem_existed() {
    Map *map = malloc(sizeof(Map));
    int size = 5;
    int res = initializeMap(map, size);
    
    if (res == 1) {
        finalizeMap(map);
        free(map);
        return 1;
    }

    Key k;
    k.a = 1;
    k.b = 2;

    Value v;
    v.c = 3;
    v.d = 4;

    //добавляем элемент
    res = addElement(map, &k, &v);
    if (res == 0) {
        finalizeMap(map);
        free(map);
        return -1;
    }

    if (map->count != 1) {
        finalizeMap(map);
        free(map);
        return -1;
    }

    // читаем добавленный
    Value retv;
    res = getElement(map, &k, &retv);
    if (res == 0) {
        finalizeMap(map);
        free(map);
        return -1;
    }

    if (retv.c != v.c || retv.d != v.d) {
        finalizeMap(map);
        free(map);
        return -1;
    }

    // добавляем новое значение по тому же ключу
    Value v1;
    v1.c = 5;
    v1.d = 6;

    res = addElement(map, &k, &v1);
    if (res == 0) {
        finalizeMap(map);
        free(map);
        return -1;
    }

    if (map->count != 1) {
        finalizeMap(map);
        free(map);
        return -1;
    }

    // читаем новые значения
    res = getElement(map, &k, &retv);
    if (res == 0) {
        finalizeMap(map);
        free(map);
        return -1;
    }

    if (retv.c != v1.c || retv.d != v1.d) {
        finalizeMap(map);
        free(map);
        return -1;
    }

    finalizeMap(map);
    free(map);
    return 0;
}

int test_add_two_elems() {
    Map *map = malloc(sizeof(Map));
    int size = 5;
    int res = initializeMap(map, size);
    
    if (res == 1) {
        finalizeMap(map);
        free(map);
        return 1;
    }

    Key k;
    k.a = 1;
    k.b = 2;

    Value v;
    v.c = 3;
    v.d = 4;

    //добавляем первый элемент
    res = addElement(map, &k, &v);
    if (res == 0) {
        finalizeMap(map);
        free(map);
        return -1;
    }

    if (map->count != 1) {
        finalizeMap(map);
        free(map);
        return -1;
    }

    // читаем добавленный
    Value retv;
    res = getElement(map, &k, &retv);
    if (res == 0) {
        finalizeMap(map);
        free(map);
        return -1;
    }

    if (retv.c != v.c || retv.d != v.d) {
        finalizeMap(map);
        free(map);
        return -1;
    }

    // добавляем второй элемент
    Key k1;
    k1.a = 5;
    k1.b = 6;

    Value v1;
    v1.c = 7;
    v1.d = 8;

    res = addElement(map, &k1, &v1);
    if (res == 0) {
        finalizeMap(map);
        free(map);
        return -1;
    }

    if (map->count != 2) {
        finalizeMap(map);
        free(map);
        return -1;
    }

    // читаем второе значение
    res = getElement(map, &k1, &retv);
    if (res == 0) {
        finalizeMap(map);
        free(map);
        return -1;
    }

    if (retv.c != v1.c || retv.d != v1.d) {
        finalizeMap(map);
        free(map);
        return -1;
    }

    finalizeMap(map);
    free(map);
    return 0;
}

int test_add_in_full() {
    Map *map = malloc(sizeof(Map));
    int size = 1;
    int res = initializeMap(map, size);
    
    if (res == 1) {
        finalizeMap(map);
        free(map);
        return 1;
    }

    Key k;
    k.a = 1;
    k.b = 2;

    Value v;
    v.c = 3;
    v.d = 4;

    //добавляем первый элемент
    res = addElement(map, &k, &v);
    if (res == 0) {
        finalizeMap(map);
        free(map);
        return -1;
    }

    if (map->count != 1) {
        finalizeMap(map);
        free(map);
        return -1;
    }

    // читаем добавленный
    Value retv;
    res = getElement(map, &k, &retv);
    if (res == 0) {
        finalizeMap(map);
        free(map);
        return -1;
    }

    if (retv.c != v.c || retv.d != v.d) {
        finalizeMap(map);
        free(map);
        return -1;
    }

    // добавляем второй элемент
    Key k1;
    k1.a = 5;
    k1.b = 6;

    Value v1;
    v1.c = 7;
    v1.d = 8;

    res = addElement(map, &k1, &v1);
    if (res == 1) {
        finalizeMap(map);
        free(map);
        return -1;
    }

    finalizeMap(map);
    free(map);
    return 0;
}

// удаление из пустого
int test_remove_elem_empty_map() {
    Map *map = malloc(sizeof(Map));
    int size = 5;
    int res = initializeMap(map, size);
    
    if (res == 1) {
        finalizeMap(map);
        free(map);
        return 1;
    }

    Key k;
    k.a = 1;
    k.b = 2;

    Value v;

    // удаляем элемент
    res = removeElement(map, &k, &v);
    if (res == 1) {
        finalizeMap(map);
        free(map);
        return -1;
    }

    finalizeMap(map);
    free(map);
    return 0;
}

// удаление добавленного
int test_remove_elem() {
    Map *map = malloc(sizeof(Map));
    int size = 5;
    int res = initializeMap(map, size);
    
    if (res == 1) {
        finalizeMap(map);
        free(map);
        return 1;
    }

    Key k;
    k.a = 1;
    k.b = 2;

    Value v;
    v.c = 3;
    v.d = 4;

    //добавляем первый элемент
    res = addElement(map, &k, &v);
    if (res == 0) {
        finalizeMap(map);
        free(map);
        return -1;
    }

    if (map->count != 1) {
        finalizeMap(map);
        free(map);
        return -1;
    }

    // читаем добавленный
    Value retv;
    res = getElement(map, &k, &retv);
    if (res == 0) {
        finalizeMap(map);
        free(map);
        return -1;
    }

    if (retv.c != v.c || retv.d != v.d) {
        finalizeMap(map);
        free(map);
        return -1;
    }

    Value rmv;
    // удаляем элемент
    res = removeElement(map, &k, &rmv);
    if (res == 0) {
        finalizeMap(map);
        free(map);
        return -1;
    }

    if (rmv.c != v.c || rmv.d != v.d) {
        finalizeMap(map);
        free(map);
        return -1;
    }

    finalizeMap(map);
    free(map);
    return 0;
}

// удаление среднего 1 2 3 -> второй удаляем
int test_remove_middle_elem() {
    Map *map = malloc(sizeof(Map));
    int size = 5;
    int res = initializeMap(map, size);
    
    if (res == 1) {
        finalizeMap(map);
        free(map);
        return 1;
    }

    Key k;
    k.a = 1;
    k.b = 2;

    Value v;
    v.c = 3;
    v.d = 4;

    //добавляем первый элемент
    res = addElement(map, &k, &v);
    if (res == 0) {
        finalizeMap(map);
        free(map);
        return -1;
    }
    

    if (map->count != 1) {
        finalizeMap(map);
        free(map);
        return -1;
    }

    // читаем добавленный
    Value retv;
    res = getElement(map, &k, &retv);
    if (res == 0) {
        finalizeMap(map);
        free(map);
        return -1;
    }

    if (retv.c != v.c || retv.d != v.d) {
        finalizeMap(map);
        free(map);
        return -1;
    }

    Key k1;
    k1.a = 5;
    k1.b = 6;

    Value v1;
    v1.c = 7;
    v1.d = 8;

    //добавляем второй элемент
    res = addElement(map, &k1, &v1);
    if (res == 0) {
        finalizeMap(map);
        free(map);
        return -1;
    }
    

    if (map->count != 2) {
        finalizeMap(map);
        free(map);
        return -1;
    }
    
    // читаем добавленный
    Value retv1;
    res = getElement(map, &k1, &retv1);
    if (res == 0) {
        finalizeMap(map);
        free(map);
        return -1;
    }
 
    if (retv1.c != v1.c || retv1.d != v1.d) {
        finalizeMap(map);
        free(map);
        return -1;
    }

    Key k2;
    k2.a = 9;
    k2.b = 10;

    Value v2;
    v2.c = 11;
    v2.d = 12;
 
    //добавляем третий элемент
    res = addElement(map, &k2, &v2);
    if (res == 0) {
        finalizeMap(map);
        free(map);
        return -1;
    }
     

    if (map->count != 3) {
        finalizeMap(map);
        free(map);
        return -1;
    }
     

    // читаем добавленный
    Value retv2;
    res = getElement(map, &k2, &retv2);
    if (res == 0) {
        finalizeMap(map);
        free(map);
        return -1;
    }
     

    if (retv2.c != v2.c || retv2.d != v2.d) {
        finalizeMap(map);
        free(map);
        return -1;
    }
 
    Value rmv;
    // удаляем элемент
    res = removeElement(map, &k1, &rmv);
    if (res == 0) {
        finalizeMap(map);
        free(map);
        return -1;
    }
     

    if (rmv.c != v1.c || rmv.d != v1.d) {
        finalizeMap(map);
        free(map);
        return -1;
    }
 
    if (map->count != 2) {
        finalizeMap(map);
        free(map);
        return -1;
    }
     

    if (map->items[0].key.a != k.a && 
        map->items[0].key.b != k.b && 
        map->items[0].value.c != v.c && 
        map->items[0].value.d != v.c &&
        map->items[0].existent != 1) {
            finalizeMap(map);
            free(map);
            return -1;
        }
     

    if (map->items[1].key.a != k2.a && 
        map->items[1].key.b != k2.b && 
        map->items[1].value.c != v2.c && 
        map->items[1].value.d != v2.c &&
        map->items[1].existent != 1) {
            finalizeMap(map);
            free(map);
            return -1;
        }

    if (map->items[2].key.a != 0 && 
        map->items[2].key.b != 0 && 
        map->items[2].value.c != 0 && 
        map->items[2].value.d != 0 &&
        map->items[2].existent != 0) {
            finalizeMap(map);
            free(map);
            return -1;
        }

    Value retvcheck;
    res = getElement(map, &k, &retvcheck);
    if (res == 0) {
        finalizeMap(map);
        free(map);
        return -1;
    }

    if (retvcheck.c != v.c || retvcheck.d != v.d) {
        finalizeMap(map);
        free(map);
        return -1;
    }

    res = getElement(map, &k2, &retvcheck);
    if (res == 0) {
        finalizeMap(map);
        free(map);
        return -1;
    }

    if (retvcheck.c != v2.c || retvcheck.d != v2.d) {
        finalizeMap(map);
        free(map);
        return -1;
    }

    res = getElement(map, &k1, &retvcheck);
    if (res == 1) {
        finalizeMap(map);
        free(map);
        return -1;
    }

    finalizeMap(map);
    free(map);
    return 0;
}

int test_get_elem() {
    Map *map = malloc(sizeof(Map));
    int size = 5;
    int res = initializeMap(map, size);
    
    if (res == 1) {
        finalizeMap(map);
        free(map);
        return 1;
    }

    Key k;
    k.a = 1;
    k.b = 2;

    Value v;
    v.c = 3;
    v.d = 4;

    //добавляем первый элемент
    res = addElement(map, &k, &v);
    if (res == 0) {
        finalizeMap(map);
        free(map);
        return -1;
    }

    if (map->count != 1) {
        finalizeMap(map);
        free(map);
        return -1;
    }

    // читаем добавленный
    Value retv;
    res = getElement(map, &k, &retv);
    if (res == 0) {
        finalizeMap(map);
        free(map);
        return -1;
    }

    if (retv.c != v.c || retv.d != v.d) {
        finalizeMap(map);
        free(map);
        return -1;
    }

    finalizeMap(map);
    free(map);
    return 0;
}

int test_get_wrong_elem() {
    Map *map = malloc(sizeof(Map));
    int size = 5;
    int res = initializeMap(map, size);
    
    if (res == 1) {
        finalizeMap(map);
        free(map);
        return 1;
    }

    Key k;
    k.a = 1;
    k.b = 2;

    Value v;
    v.c = 3;
    v.d = 4;

    //добавляем первый элемент
    res = addElement(map, &k, &v);
    if (res == 0) {
        finalizeMap(map);
        free(map);
        return -1;
    }

    if (map->count != 1) {
        finalizeMap(map);
        free(map);
        return -1;
    }

    Key k1;
    k1.a = 3;
    k1.b = 4;

    // читаем добавленный
    Value retv;
    res = getElement(map, &k1, &retv);
    if (res == 1) {
        finalizeMap(map);
        free(map);
        return -1;
    }

    finalizeMap(map);
    free(map);
    return 0;
}

int test_remove_last_elem() {
    Map *map = malloc(sizeof(Map));
    int size = 1;
    int res = initializeMap(map, size);
    
    if (res == 1) {
        finalizeMap(map);
        free(map);
        return 1;
    }

    Key k;
    k.a = 1;
    k.b = 2;

    Value v;
    v.c = 3;
    v.d = 4;

    //добавляем первый элемент
    res = addElement(map, &k, &v);
    if (res == 0) {
        finalizeMap(map);
        free(map);
        return -1;
    }

    if (map->count != 1) {
        finalizeMap(map);
        free(map);
        return -1;
    }

    // читаем добавленный
    Value retv;
    res = getElement(map, &k, &retv);
    if (res == 0) {
        finalizeMap(map);
        free(map);
        return -1;
    }

    if (retv.c != v.c || retv.d != v.d) {
        finalizeMap(map);
        free(map);
        return -1;
    }

    Value rmv;
    // удаляем элемент
    res = removeElement(map, &k, &rmv);
    if (res == 0) {
        finalizeMap(map);
        free(map);
        return -1;
    }
    
    if (rmv.c != v.c || rmv.d != v.d) {
        finalizeMap(map);
        free(map);
        return -1;
    }

    if (map->count != 0) {
        finalizeMap(map);
        free(map);
        return -1;
    }
    finalizeMap(map);
    free(map);
    return 0;
}