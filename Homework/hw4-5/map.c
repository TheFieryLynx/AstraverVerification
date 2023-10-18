#include "map.h"

// 0 - ошибка
// 1 - верно

int initializeMap(Map *map, int size) {
    if (size <= 0) {
        return 1;
    }
    map->capacity = size;
    map->count = 0;
    map->items = malloc(map->capacity * sizeof(Item));
    if (map->items == NULL) {
        return 1;
    }
    /*@
        loop invariant i >= 0;
        loop invariant i <= map->capacity;
        loop invariant \valid(map->items + (0..map->capacity - 1));
        loop invariant (
            \forall integer j;
                (0 <= j < i) ==> 
                    map->items[j].existent == 0
        );
        loop variant map->capacity - i; 
    */
    for (int i = 0; i < map->capacity; ++i) {
        map->items[i].existent = 0;
    }
    
    /*@ ghost
        int i = 0;
        /@
            loop invariant i >= 0;
            loop invariant i <= map->capacity;
            loop invariant map->count == 0;
            loop invariant count(map, 0, i) == 0;
            loop assigns \nothing;
            loop variant map->capacity - i;
        @/
        while (i < map->capacity) {
            //@ assert count(map, 0, i) == 0;
            //@ assert map->items[i].existent == 0 ==> count(map, i, i + 1) == 0;
            //@ assert count(map, 0, i) == count(map, 0, i) + count(map, i, i + 1);
            ++i;
        }
    */
    return 0;
}

void finalizeMap(Map *map) {
    free(map->items);
}

int addElement(Map *map, Key *key, Value *value) {
    for (int i = 0; i < map->capacity; ++i) {
        if (map->items[i].key.a == key->a &&
                map->items[i].key.b == key->b && 
                    map->items[i].existent == 1) {
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
    /*@
        loop invariant i >= 0;
        loop invariant i <= map->capacity;
        loop invariant map->capacity > 0;
        loop invariant \valid(map->items + (0..map->capacity - 1)); 
        loop invariant (\valid(value) || value == NULL);

        loop invariant (
            (\at(value->c, Pre) == \at(value->c, Here)) && 
            (\at(value->d, Pre) == \at(value->d, Here))
        );
        loop invariant (
            (\at(key->a, Pre) == \at(key->a, Here)) && 
            (\at(key->b, Pre) == \at(key->b, Here))
        );

        loop invariant (
            \forall integer k;
                (0 <= k < i) ==>
                    !(
                        (map->items[k].key.a == key->a) && 
                        (map->items[k].key.b == key->b) &&
                        (map->items[k].existent == 1)
                    )
        );

        loop invariant (i < map->capacity) ==> ((map->items[i].existent == 0) || (map->items[i].existent == 1));

        loop invariant count(map, 0, i + 1) == count(map, 0, i) + count(map, i, i + 1);
        loop invariant count(map, 0, map->capacity) == count(map, 0, i) + count(map, i, map->capacity);
        loop invariant count(map, 0, map->capacity) == map->count;

        loop invariant is_valid_map(map);
        loop invariant (\at(map->capacity, Pre) == \at(map->capacity, Here));

        // loop invariant (\at(map->count, Pre)) == (\at(map->count, Here));
        loop invariant get_item_key{Pre}(map, i) == get_item_key{Here}(map, i);
        loop invariant get_item_value{Pre}(map, i) == get_item_value{Here}(map, i);

        loop invariant (
            \forall integer k;
            (0 <= k < i) && (!((map->items[k].key.a == key->a) &&
                (map->items[k].key.b == key->b) && 
                    (map->items[k].existent == 1))) ==>
                        (
                            (\at(map->count, Pre)) == (\at(map->count, Here))
                        )
        );

        loop invariant (
            \forall integer k;
            (0 <= k < i) && (!((map->items[k].key.a == key->a) &&
                (map->items[k].key.b == key->b) && 
                    (map->items[k].existent == 1))) ==>
                        (
                            \at(map->items[\at(k, Here)].existent, Pre) == \at(map->items[k].existent, Here)
                        )
        );

        loop variant map->capacity - i;
    */
    for (int i = 0; i < map->capacity; ++i) {
        if ((map->items[i].key.a == key->a) &&
                (map->items[i].key.b == key->b) && 
                    (map->items[i].existent == 1)) {
            //@ assert \exists integer l; (0 <= l < map->capacity) && map->items[l].existent == 1;
            //@ assert count(map, 0, map->capacity) == count(map, 0, i) + count(map, i, map->capacity);
            //@ assert count(map, i, i + 1) == 1;
            //@ assert count(map, 0, i + 1) == count(map, 0, i) + count(map, i, i + 1);
            //@ assert count(map, 0, map->capacity) == count(map, 0, i) + count(map, i, i + 1) + count(map, i + 1, map->capacity);
            //@ assert count(map, 0, map->capacity) == count(map, 0, i) + 1 + count(map, i + 1, map->capacity);
            if (value != NULL) {
                *value = map->items[i].value;
            }

            int found = i;
            //@ assert map->items[found].existent == 1;
            /*@
                loop invariant j >= i + 1;
                loop invariant j <= map->capacity;
                loop invariant map->capacity > 0;
                loop invariant \valid(map->items + (0..map->capacity - 1)); 
                loop invariant map->items[found].existent == 1;


                loop invariant found >= i; 
                loop invariant found < map->capacity;  
                loop variant map->capacity - j;
            */
            for (int j = i + 1; j < map->capacity; ++j) {
                if (map->items[j].existent == 1) {
                    found = j;
                    //@ assert map->items[found].existent == 1;
                }
            }
            //@ assert (i <= found);
            //@ assert (found < map->capacity);
            //@ assert map->items[found].existent == 1;
            map->items[i].key = map->items[found].key;
            map->items[i].value = map->items[found].value;
            //@ assert map->items[i].existent == 1;
            // assert \at(map->items[\at(i, Here)].existent, Pre) == \at(map->items[i].existent, Here);
            map->items[found].existent = 0;

            map->count--;
            //@ assert map->count >= 0;
            
            //@ assert (map->items[i].key.a == map->items[found].key.a);
            //@ assert (map->items[i].key.b == map->items[found].key.b);

            /*@ ghost
                /@
                    loop invariant k >= 0;
                    loop invariant k <= i; 

                    loop invariant count{Here}(map, 0, k) == count{Pre}(map, 0, k);

                    loop variant i - k;
                @/
                for (int k = 0; k < i; ++k) {
                    //@ assert count{Here}(map, k - 1, k) == count{Pre}(map, k - 1, k);
                    //@ assert count{Here}(map, 0, k) == count{Here}(map, 0, k - 1) + count{Here}(map, k - 1, k);
                    //@ assert count{Pre}(map, 0, k) == count{Pre}(map, 0, k - 1) + count{Pre}(map, k - 1, k);
                }
            */

            /*@ ghost
                /@
                    loop invariant k >= i;
                    loop invariant k <= map->capacity; 
                    
                    loop invariant count{Here}(map, i, k) == (count{Pre}(map, i, k) - 1);

                    loop variant map->capacity - k;
                @/
                for (int k = i; k < map->capacity; ++k) {
                    ++k;
                }
            */

            //@ assert count(map, 0, map->capacity) == count(map, 0, i) + count(map, i, map->capacity);
            //@ assert (\at(value, Pre) == NULL) ==> (\at(value, Here) == NULL);
            //@ assert (\at(key->a, Pre) == \at(key->a, Here));
            //@ assert (\at(key->b, Pre) == \at(key->b, Here));

            //@ assert \forall integer i; (0 <= i < map->capacity) ==> !((map->items[i].key.a == key->a) && (map->items[i].key.b == key->b) && map->items[i].existent == 1);
            
            // не добавляет новые отображения
            //@ assert \forall integer k1; (0 <= k1 < map->capacity) && (\at(map->items[k1].existent, Here) == 1) ==> \exists integer j; (0 <= j < map->capacity) && (\at(map->items[\at(j, Here)].existent, Pre) == 1) && (\at(map->items[k1].key, Here) == \at(map->items[\at(j, Here)].key, Pre));
            //@ assert \forall integer k1; (0 <= k1 < map->capacity) && (\at(map->items[k1].existent, Here) == 1) ==> \exists integer j; (0 <= j < map->capacity) && (\at(map->items[\at(j, Here)].existent, Pre) == 1) && (\at(map->items[k1].value, Here) == \at(map->items[\at(j, Here)].value, Pre));
            
            // отсутствует удаляемый элемент
            //@ assert \forall integer l; (0 <= l < map->capacity) ==> !((map->items[l].key.a == key->a) && (map->items[l].key.b == key->b) && map->items[l].existent == 1);
            return 1;
        } else {
            //@ assert (\at(key->a, Pre) == \at(key->a, Here));
            //@ assert (\at(key->b, Pre) == \at(key->b, Here));
            //@ assert \at(map->items[i].existent, Here) == \at(map->items[\at(i, Here)].existent, LoopCurrent);
            //@ assert \at(map->items[i].existent, LoopCurrent) == \at(map->items[i].existent, Here);
            //@ assert (\at(map->count, LoopCurrent)) == (\at(map->count, Here));

            /*@ ghost
                /@
                    loop invariant k >= 0;
                    loop invariant k <= i; 

                    loop invariant count{Here}(map, 0, k) == count{Pre}(map, 0, k);

                    loop variant i - k;
                @/
                for (int k = 0; k < i; ++k) {
                    //@ assert count{Here}(map, k - 1, k) == count{Pre}(map, k - 1, k);
                    //@ assert count{Here}(map, 0, k) == count{Here}(map, 0, k - 1) + count{Here}(map, k - 1, k);
                    //@ assert count{Pre}(map, 0, k) == count{Pre}(map, 0, k - 1) + count{Pre}(map, k - 1, k);
                }
            */

            /*@ ghost
                /@
                    loop invariant k >= 0;
                    loop invariant k <= i; 

                    loop invariant (
                        \forall integer l;
                            (0 <= l < k) ==>
                                (
                                    (\at(map->count, Pre)) == (\at(map->count, Here))
                                )
                    );

                    loop invariant (
                        \forall integer l;
                            (0 <= l < k) ==>
                                (
                                    \at(map->items[\at(l, Here)].existent, Pre) == \at(map->items[l].existent, Here)
                                )
                    );

                    loop invariant (
                        \forall integer l;
                            (0 <= l < k) ==>
                                (
                                    count{Here}(map, 0, l) == count{LoopCurrent}(map, 0, l)
                                )
                    );

                    loop invariant (
                        \forall integer l;
                            ((0 <= l < k) && (\at(map->items[l].existent, Here) == 1)) ==>
                                (
                                    \exists integer j; 
                                        (0 <= j < map->capacity) && 
                                            (\at(map->items[\at(j, Here)].existent, Pre) == 1) && 
                                                (\at(map->items[l].value, Here) == \at(map->items[\at(j, Here)].value, Pre))
                                )
                    );

                    loop variant i - k;
                @/
                for (int k = 0; k < i; ++k) {
                }
            */
        }
    }
    //@ assert (\at(value, Pre) == NULL) == (\at(value, Here) == NULL);
    //@ assert (\at(value, Pre) != NULL) ==> ( \at(value, Pre) == \at(value, Here));
    //@ assert (\at(key->a, Pre) == \at(key->a, Here));
    //@ assert (\at(key->b, Pre) == \at(key->b, Here));

    //@ assert \forall integer i; (0 <= i < map->capacity) ==> !((map->items[i].key.a == key->a) && (map->items[i].key.b == key->b) && map->items[i].existent == 1);
    
   
    //@ assert \forall integer k1; (0 <= k1 < map->capacity) ==> count{Here}(map, 0, k1) == count{Pre}(map, 0, k1);
    //@ assert count{Here}(map, 0, map->capacity) == count{Pre}(map, 0, map->capacity);

    // все элементы не изменились
    //@ assert \forall integer k1; (0 <= k1 < map->capacity) && (\at(map->items[k1].existent, Here) == 1) && (\at(map->items[\at(k1, Here)].existent, Pre) == 1) ==> ((\at(map->items[k1].key, Here)) ==(\at(map->items[\at(k1, Here)].key, Pre)));
    //@ assert \forall integer k1; (0 <= k1 < map->capacity) && (\at(map->items[k1].existent, Here) == 1) && (\at(map->items[\at(k1, Here)].existent, Pre) == 1) ==> ((\at(map->items[k1].value, Here)) ==(\at(map->items[\at(k1, Here)].value, Pre)));
    
    // не добавляяет новые отображения
    //@ assert \forall integer k1; (0 <= k1 < map->capacity) && (\at(map->items[k1].existent, Here) == 1) ==> \exists integer j; (0 <= j < map->capacity) && (\at(map->items[\at(j, Here)].existent, Pre) == 1) && (\at(map->items[k1].key, Here) == \at(map->items[\at(j, Here)].key, Pre));
    //@ assert \forall integer k1; (0 <= k1 < map->capacity) && (\at(map->items[k1].existent, Here) == 1) ==> \exists integer j; (0 <= j < map->capacity) && (\at(map->items[\at(j, Here)].existent, Pre) == 1) && (\at(map->items[k1].value, Here) == \at(map->items[\at(j, Here)].value, Pre));
    
    
    return 0;
}


int getElement(Map *map, Key *key, Value *value) {
    /*@
        loop invariant i >= 0;
        loop invariant i <= map->capacity;
        loop invariant map->capacity > 0;
        loop invariant \valid(map->items + (0..map->capacity - 1));
        loop invariant (
            (\at(value->c, Pre) == \at(value->c, Here)) && 
            (\at(value->d, Pre) == \at(value->d, Here))
        );
        loop invariant (
            \forall integer j;
                (0 <= j < i) ==>
                    !(
                        (map->items[j].key.a == key->a) && 
                        (map->items[j].key.b == key->b) &&
                        map->items[j].existent == 1
                    )
        );
        
        loop variant map->capacity - i;
    */
    for (int i = 0; i < map->capacity; ++i) {
        if (map->items[i].existent == 1 && map->items[i].key.a == key->a && map->items[i].key.b == key->b) {
            *value = map->items[i].value;
            return 1;
        }
    }
    return 0;
}