#ifndef __MAP_H__
#define __MAP_H__

#include "maptypes.h"
#include <stdlib.h>
#include <stdio.h>
#include <limits.h>

/*  Формальная спецификация типов данных
    1. Структура Map:
        1) Уникальность ключей (Структура может хранить лишь единственное отображение для конкретного ключа)
        2) Размер items равен capacity (Поле items структуры Map представляет собой массив длины capacity)
        3) Количество элементов (Поле count этой структуры определяет, 
                                сколько элементов данного массива имеет поле existent установленным в истину (единицу))
        4) При работе со структурой учитываются те и только те записи массива items, которые имеют булево поле existent установленным в истину (единицу)
        5) Элементы хранятся с начала массива
        6) За двумя последовательно идущими элементами, у которых existent установлен в ложь, остальные элементы тоже имеют existent установленным в ложь.
    2. Структура Items:
        1) Поле key - структура типа Key
        2) Поле value - струтура типа Value
        3) Поле existent - принимает значение 0 или 1 (Если значение 0, то остальные поля не рассматриваются)
    3. Структура Key:
        1) Два целочисленных поля a, b
    4. Структура Value:
        1) Два целочисленных поля c, d
*/

/* Формальная спецификация функции getElement
    1. Bозвращает по указателю value сохранённое в ассоциативном массиве map значение для заданного ключа key
    2. Возвращает истину (единицу), если заданный ассоциативный массив имеет отображения для заданного ключа
    3. В случае, если значение по заданному ключу не содержится в отображении, возвращается ложь (ноль) и ничего другого не происходит.
    4. Функция не меняет ассоциативный массив и переданный ключ.
        - capacity не меняется
        - count не меняется
        - переданный ключ не меняется
        - все значения items не меняются
        - map valid
        - key valid
        - value valid 
*/

/* Формальная спецификация функции initializeMap
    1. Входной указатель на структуру валидный
    2. Если size <= 0, это означает некорректный размер входной map
    3. Создаёт пустой ассоциативный массив с заданным числом максимально хранимых элементов size
    4. Функция возвращает ноль (успех):
        - под map->items выделена память размера size * sizeof(Item)
        - map->capacity = size
        - map->count = 0
        - map->items[0..map->capacity - 1].existent = 0
*/

/* Формальная спецификация функции removeElement
    1. Удаляет сохранённое в ассоциативном массиве map значение по заданному ключу key (если оно там было)
    2. Функция не удаляет другие отображения, кроме отображения по заданному ключу, а также не добавляет новые отображения
    3. Функция возвращает истину (единицу), если функция изменила ассоциативный массив, ложь (ноль) в противном случае
    4. В случае, если значение было удалено и при этом переданный указатель value 
        был отличен от нулевого, функция записывает значение, содержавшееся для заданного ключа, по данному указателю
    5. Функция имеет право изменять структуру ассоциативного массива, если это не отражается на содержащихся в нём парах:
        - если был найден элемент по ключу, то после его удаления count уменьшается на 1
    6. Все остальные элементы остаются неизменными
*/

/*@ axiomatic Count {
    logic integer count{L}(Map *map, integer m, integer n);
     
    axiom count_zero: \forall Map *map, integer m, n; m >= n ==>
        count(map, m, n) == 0;

    predicate count_one_p{L}(Map *map, integer m) =
        count(map, m, m + 1) == (map->items[m].existent ? 1 : 0);

    axiom count_one{L}: \forall Map *map, integer m; count_one_p(map, m);

    predicate count_split_p{L}(Map *map, integer m, integer n, integer k) =
        count(map, m, k) == count(map, m, n) + count(map, n, k);

    axiom count_split{L}: \forall Map *map, integer m, n, k; m <= n <= k ==>
        count_split_p(map, m, n, k);
}*/

/*@ axiomatic CountLem {
    lemma l_count_split:
        \forall Map *map, integer i;
            (is_valid_map(map) && (0 < i < map->capacity)) ==>
                (count(map, 0, i) == 
                    count(map, 0, i - 1) + count(map, i - 1, i));

    lemma l_count_split2:
        \forall Map *map, integer i, j;
            (is_valid_map(map) && (0 < i < j) && (j < map->capacity)) ==>
                (count(map, 0, j) == 
                    count(map, 0, i) + count(map, i, j));

    lemma l_count_split3: 
        \forall Map *map, integer m, n, k; 
            (m <= n <= k) 
            ==> 
            count_split_p(map, m, n, k) && 
            (count(map, m, k) == count(map, m, n) + count(map, n, k));
    
    lemma l_count_one_p:
        \forall Map *map, integer i;
            is_valid_map(map) ==>
            (
                (count_one_p(map, i)) && 
                    (count(map, i, (i + 1)) ==
                        (
                            map->items[i].existent ? 1 : 0
                        )
                    )
            ); 

    lemma l_count_positive: 
        \forall Map *map, integer i; 
            (map->items[i].existent == 0 || map->items[i].existent == 1) ==>
            (count(map, i, i + 1) >= 0);
    
    lemma l_count_positive1:
        \forall Map *map;
            is_valid_map(map) ==> count(map, 0, map->capacity) >= 0;

    lemma l_count_positive2:
        \forall Map *map;
            is_valid_map(map) && (count(map, 0, map->capacity) >= 0) ==> 
                map->count >= 0;

}*/

// /*@
//     ghost
//     /@
//         lemma
//         requires \valid(map);
//         requires is_valid_map(map);
//         requires 0 <= m <= map->capacity;
//         requires 0 < map->capacity < INT_MAX;
//         ensures count(map, 0, map->capacity) == \result;
//         ensures map->count == \result;
//     @/
//     int all_count2(Map *map, int m)  {
//         int cnt = 0;
//         /@
//             loop invariant i >= 0;
//             loop invariant i <= map->capacity;
//             loop invariant cnt <= map->capacity;
//             loop invariant count(map, 0, i) == cnt;
//             loop variant map->capacity - i;
//         @/
//         for (int i = 0; i < map->capacity; ++i) {
//             if (map->items[i].existent == 1) {
//                 cnt++;
//             }
//         }
//         return cnt;
//     }
// */

/*@
    ghost
    /@
        lemma
        requires \valid(map);
        requires is_valid_map(map);
        requires 0 <= m <= map->capacity;
        decreases m;
        ensures count(map, 0, m) >= 0;
    @/
    void all_count(Map *map, int m)  {
        if (m > 0) {
            if (map->items[m-1].existent == 0) {
                //@ assert count(map, (m - 1), m) == 0;
                //@ assert (count(map, 0, m)) == (count(map, 0, (m - 1)) + (count(map, (m - 1), m)));
                all_count(map, (m - 1));
            }
            if (map->items[m-1].existent == 1){
                //@ assert count(map, (m - 1), m) == 1;
                //@ assert (count(map, 0, m)) == (count(map, 0, (m - 1)) + (count(map, (m - 1), m)));
                all_count(map, (m - 1));
            }
        }
    }
*/

/*@
    predicate is_valid_map (Map *map) =
        (\offset_max(map->items) == map->capacity - 1) &&
        (\valid(map->items + (0..map->capacity - 1))) && 
        (0 <= map->count <= map->capacity) && 
        (map->count > 0 ==> map->items[0].existent == 1) &&
        ( 
            \forall integer i; 
                (0 <= i < map->capacity) ==> 
                    ((map->items[i].existent == 0) || (map->items[i].existent == 1))
        ) && 
        (count(map, 0, map->capacity) == map->count) &&
        (
            \forall integer i, j;
                ((0 <= i < map->capacity) && (i < j < map->capacity) &&
                (map->items[i].existent == 1) && (map->items[j].existent == 1)) ==>
                    !((map->items[i].key.a == map->items[j].key.a) && (map->items[i].key.b == map->items[j].key.b)) 
        ) &&
        (
            \forall integer i, j;
                (
                    (0 < i < j) && (j < map->capacity) &&
                    (map->items[i - 1].existent == 0) &&
                    (map->items[i].existent == 0)
                ) ==> (map->items[j].existent == 0)
        );

    logic integer get_item_existent{L}(Map *map, integer i) = 
        \at(map->items[i].existent, L);

    logic Value* get_item_value{L}(Map *map, integer i) = 
        \at(&map->items[i].value, L);

    logic Key* get_item_key{L}(Map *map, integer i) = 
        \at(&map->items[i].key, L);
*/
// is_valid_map: (и не надо)
//
// predicate check_map_offset (Map *map) = 
//         \offset_max(map->items) == map->capacity - 1;
    
//     predicate check_valid_capacity (Map *map) = 
//         \valid(map->items + (0..map->capacity - 1));

//     predicate check_count_val (Map *map) =
//         0 <= map->count <= map->capacity;
    
//     predicate check_first_not_zero (Map *map) =
//         map->count > 0 ==> map->items[0].existent == 1;
    
//     predicate check_existent_val (Map *map) =
//         \forall integer i; 
//             (0 <= i < map->capacity) ==> 
//                 (map->items[i].existent == 0 || map->items[i].existent == 1);

//     predicate check_count (Map *map) =
//         check_valid_capacity(map) && check_count_val(map) && (count(map, 0, map->capacity) == map->count);

//     predicate check_unique_keys (Map *map) = 
//         \forall integer i, j;
//             (0 <= i < map->capacity) && (i < j < map->capacity) &&
//             (map->items[i].existent == 1 && map->items[j].existent == 1) ==>
//                 !(map->items[i].key.a == map->items[j].key.a && map->items[i].key.b == map->items[j].key.b);
    
//     predicate check_tail (Map *map) =
//         \forall integer i, j;
//             (
//                 (0 < i < j) && (j < map->capacity) &&
//                 (map->items[i - 1].existent == 0) &&
//                 (map->items[i].existent == 0)
//             ) ==> map->items[j].existent == 0; 

/*@
    requires \valid(map);
    ensures (\result == 0) ==> (\valid(map));
    ensures (\result == 0) ==> (\valid(map->items));
    ensures (\result == 0) ==> (\offset_max(map->items) == map->capacity - 1);
    ensures (\result == 0) ==> (is_valid_map(map));
    ensures (\result == 0) ==> (map->count == 0);
    ensures (\result == 0) ==> (map->capacity == size);
    ensures (\result == 0) ==> (
        \forall integer i; 
            (0 <= i < map->capacity) ==> 
                (map->items[i].existent == 0)
    );
    ensures (\result == 0) ==> (\allocable{Old}(map->items));
    ensures (\result == 0) ==> (\freeable(map->items));
*/
int initializeMap(Map *map, int size);

void finalizeMap(Map *map);

int addElement(Map *map, Key *key, Value *value);

/*@
    requires \valid(map);
    requires \valid(key);
    requires (\valid(value) || value == NULL);
    requires \valid(map->items + (0..map->capacity - 1));
    requires map->capacity > 0;
    requires is_valid_map(map);

    assigns *value;  
    assigns map->items[0..map->capacity - 1];
    assigns map->count;
    allocates \nothing;
    frees \nothing;

    ensures is_valid_map(map);
    ensures \valid(map);
    ensures \valid(key);
    ensures (\valid(value) || value == NULL);

    // count изменился на 1, если элемент был удален
    ensures (\result == 1) ==> (
        \at(count(map, 0, map->capacity), Old) ==
            \at(count(map, 0, map->capacity), Post) + 1
    );

    // count не изменился, если элемент не был найден
    ensures (\result == 0) ==> (
        \at(count(map, 0, map->capacity), Old) ==
            \at(count(map, 0, map->capacity), Post)
    );
    // ensures (\result == 0) ==> (
    //     \at(map->count, Old) ==
    //         \at(map->count, Post)
    // );

    // если элемент не был удален, то все элементы остались неизменными
    ensures (\result == 0) ==> (
        \forall integer i;
            ((0 <= i < map->capacity) &&
            \at(map->items[i].existent, Old) == 1 && 
            \at(map->items[i].existent, Post) == 1) ==>
            (
                (\at(map->items[i].key.a, Old) == \at(map->items[i].key.a, Post)) && 
                (\at(map->items[i].key.b, Old) == \at(map->items[i].key.b, Post)) && 
                (\at(map->items[i].value.c, Old) == \at(map->items[i].value.c, Post)) &&
                (\at(map->items[i].value.d, Old) == \at(map->items[i].value.d, Post))
            )
    );

    // если элемент был удален, то все ОСТАЛЬНЫЕ элементы остались неизменными
    // т е если существовал существующий ключ, отличный от переданного, то 
    // после работы функции существует элемент ему соответствуюший
    ensures (\result == 1) ==> (
        \forall integer i;
            (
                (0 <= i < map->capacity) &&
                (\at(map->items[i].existent, Old) == 1) && (
                    (\at(map->items[i].key.a, Old) != key->a) || 
                    (\at(map->items[i].key.b, Old) != key->b)
                )
            ) ==> (
                \exists integer j;
                    (
                        (0 <= j < map->capacity) && 
                        \at(map->items[j].existent, Post) == 1 && 
                        (\at(map->items[i].key.a, Old) == \at(map->items[j].key.a, Post)) && 
                        (\at(map->items[i].key.b, Old) == \at(map->items[j].key.b, Post)) && 
                        (\at(map->items[i].value.c, Old) == \at(map->items[j].value.c, Post)) &&
                        (\at(map->items[i].value.d, Old) == \at(map->items[j].value.d, Post))
                    )
            )
    );

    // отсутствует удаленный ключ
    ensures (\result == 1) ==> (
        \forall integer i;
        (
            (0 <= i < map->capacity) &&
            !(
                (\at(map->items[i].existent, Post) == 1) &&
                (\at(map->items[i].key.a, Post) == key->a) &&
                (\at(map->items[i].key.b, Post) == key->b)
            )
        )
    );

    ensures (
        (\at(value, Old) == NULL) ==> (\at(value, Post) == NULL)
    );
    
    ensures (
        (\at(key->b, Old) == \at(key->b, Post))
    );

    ensures (
        (\result == 0) && (\at(value, Old) != NULL) ==> 
            (
                (\at(value->c, Old) == \at(value->c, Post)) && 
                (\at(value->d, Old) == \at(value->d, Post))
            )
    );

    // Функция не добавляет новые отображения
    ensures (
        \forall integer i;
            (
                (0 <= i < map->capacity) &&
                (\at(map->items[i].existent, Post) == 1)
            ) ==> (
                \exists integer j;
                    (
                        (0 <= j < map->capacity) && 
                        (\at(map->items[j].existent, Old) == 1) && 
                        (\at(map->items[i].key.a, Old) == \at(map->items[j].key.a, Post)) && 
                        (\at(map->items[i].key.b, Old) == \at(map->items[j].key.b, Post)) && 
                        (\at(map->items[i].value.c, Old) == \at(map->items[j].value.c, Post)) &&
                        (\at(map->items[i].value.d, Old) == \at(map->items[j].value.d, Post))
                    )
            )
    );


*/
int removeElement(Map *map, Key *key, Value *value);


/*@
    
    requires \valid(key);
    requires \valid(value);
    requires \valid(map);
    requires map->capacity > 0;
    requires \valid(map->items + (0..map->capacity - 1));
    requires is_valid_map(map);

    assigns *value; 
    allocates \nothing;
    frees \nothing;

    ensures is_valid_map(map);
    ensures \valid(key);
    ensures \valid(value);
    ensures \valid(map);
    // capacity не изменился
    ensures \at(map->capacity, Old) == \at(map->capacity, Post);
    // count не изменился
    ensures \at(map->count, Old) == \at(map->count, Post);
    // все элементы не изменили значений
    ensures \forall integer i;
        (0 <= i < map->capacity &&
            \at(map->items[i].existent, Old) == 1 && \at(map->items[i].existent, Post) == 1) ==>
                (
                    (\at(map->items[i].key.a, Old) == \at(map->items[i].key.a, Post)) && 
                    (\at(map->items[i].key.b, Old) == \at(map->items[i].key.b, Post)) && 
                    (\at(map->items[i].value.c, Old) == \at(map->items[i].value.c, Post)) &&
                    (\at(map->items[i].value.d, Old) == \at(map->items[i].value.d, Post))
                );
    // входной key не изменился
    ensures (
        (\at(key->a, Old) == \at(key->a, Post)) && (\at(key->b, Old) == \at(key->b, Post))
    );
    // если элемент не найден, то входной value не изменился
    // и не нашлось такого существуещего элемента с переданным ключом
    ensures (
        (\result == 0) ==> 
            (
                (\at(value->c, Old) == \at(value->c, Post)) && 
                (\at(value->d, Old) == \at(value->d, Post))
            ) &&
            (
                \forall integer i;
                    (0 <= i < map->capacity) ==>
                        !(
                            (map->items[i].key.a == key->a) && 
                            (map->items[i].key.b == key->b) &&
                            map->items[i].existent == 1
                        )
            )
    );
    // если результат положителен, то существует элемент с таким ключом 
    // и value успешно записался в переданный
    ensures (
        (\result == 1) ==>
            (
                \exists integer i;
                    (0 <= i < map->capacity) &&
                    (map->items[i].existent == 1) &&
                    (map->items[i].key.a == key->a) && (map->items[i].key.b == key->b) &&
                    (map->items[i].value.c == \at(value->c, Post)) && (map->items[i].value.d == \at(value->d, Post))
            )
    );


*/
int getElement(Map *map, Key *key, Value *value);

#endif // __MAP_H__
