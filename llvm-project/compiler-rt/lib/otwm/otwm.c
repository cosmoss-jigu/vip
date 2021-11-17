#include<stdlib.h>
#include<stdio.h>
#include<sys/mman.h>


void *otwm_dummy(void *ptr_address_input);

void sm_register_8b(void *address_to_protect);
void sm_write_8b(void *address_to_protect);

void sm_register(void *address_to_protect, int size);
void sm_unregister(void *address_to_protect);
void sm_write_once(void *address_to_protect);
void sm_write(void *address_to_protect, int size);

//void sm_assert(void *address_to_protect, int size);
//void sm_assert_8b(void *address_to_protect);
