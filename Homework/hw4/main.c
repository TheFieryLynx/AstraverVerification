#include "map.h"
#include "test.h"

int main(void) {
    int res;
    res = test_zero_size();
    printf("T zero size: %d\n", res);
    res = test_init();
    printf("T init: %d\n", res);
    res = test_add_elem_empty_map();
    printf("T add elem empty map: %d\n", res);
    res = test_add_elem_existed();
    printf("T add elem existed: %d\n", res);
    res = test_add_two_elems();
    printf("T add two elems: %d\n", res);
    res = test_add_in_full();
    printf("T add two elems: %d\n", res);
    res = test_remove_elem_empty_map();
    printf("T remove from empty map: %d\n", res);
    res = test_remove_elem();
    printf("T remove: %d\n", res);
    res = test_remove_middle_elem();
    printf("T remove middle: %d\n", res);
    res = test_remove_last_elem();
    printf("T remove last elem: %d\n", res);
    res = test_get_elem();
    printf("T get elem: %d\n", res);
    res = test_get_wrong_elem();
    printf("T get wrong elem: %d\n", res);
    return 0;
}