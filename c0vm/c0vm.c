/**************************************************************************/
/*              COPYRIGHT Carnegie Mellon University 2022                 */
/* Do not post this file or any derivative on a public site or repository */
/**************************************************************************/
#include <assert.h>
#include <stdio.h>
#include <limits.h>
#include <stdlib.h>

#include "lib/xalloc.h"
#include "lib/stack.h"
#include "lib/contracts.h"
#include "lib/c0v_stack.h"
#include "lib/c0vm.h"
#include "lib/c0vm_c0ffi.h"
#include "lib/c0vm_abort.h"

/* call stack frames */
typedef struct frame_info frame;
struct frame_info {
  c0v_stack_t S;   /* Operand stack of C0 values */
  ubyte *P;        /* Function body */
  size_t pc;       /* Program counter */
  c0_value *V;     /* The local variables */
};

void push_int(c0v_stack_t S, int32_t i) {
  c0v_push(S, int2val(i));
}

void push_ptr(c0v_stack_t S, void *a) {
  c0v_push(S, ptr2val(a));
}

int32_t pop_int(c0v_stack_t S) {
  return val2int(c0v_pop(S));
}

void *pop_ptr(c0v_stack_t S){
  return val2ptr(c0v_pop(S));
}

int execute(struct bc0_file *bc0) {
  REQUIRES(bc0 != NULL);

  /* Variables */
  c0v_stack_t S = c0v_stack_new(); /* Operand stack of C0 values */
  ubyte *P = bc0->function_pool->code;      
  /* Array of bytes that make up the current function */
  size_t pc = 0;     /* Current location within the current byte array P */
  c0_value *V = xcalloc(bc0->function_pool[0].num_vars, sizeof(c0_value));   
  /* Local variables (you won't need this till Task 2) */
  (void) V;      // silences compilation errors about V being currently unused
  (void) S;

  /* The call stack, a generic stack that should contain pointers to frames */
  /* You won't need this until you implement functions. */
  gstack_t callStack = stack_new();
  (void) callStack; 
  // silences compilation errors about callStack being currently unused

  while (true) {

#ifdef DEBUG
    /* You can add extra debugging information here */
    fprintf(stderr, "Opcode %x -- Stack size: %zu -- PC: %zu\n",
            P[pc], c0v_stack_size(S), pc);
#endif

    switch (P[pc]) {

    /* Additional stack operation: */

    case POP: {
      pc++;
      c0v_pop(S);
      break;
    }

    case DUP: {
      pc++;
      c0_value v = c0v_pop(S);
      c0v_push(S,v);
      c0v_push(S,v);
      break;
    }

    case SWAP: {
      pc++;
      c0_value v2 = c0v_pop(S);
      c0_value v1 = c0v_pop(S);
      c0v_push(S, v2);
      c0v_push(S,v1);
      break;
    }
    /* Returning from a function.
     * This currently has a memory leak! You will need to make a slight
     * change for the initial tasks to avoid leaking memory.  You will
     * need to revise it further when you write INVOKESTATIC. */
    case RETURN: {
      c0_value retval = c0v_pop(S);
      assert(c0v_stack_empty(S));
// Another way to print only in DEBUG mode
        //IF_DEBUG(fprintf(stderr, "Returning %d from execute()\n", retval));
      // Free everything before returning from the execute function!
      c0v_stack_free(S);
      free(V);
      if(!stack_empty(callStack)){
        frame *new_frame = pop(callStack);
        S = new_frame->S;
        P = new_frame->P;
        pc = new_frame->pc;
        V = new_frame->V;
        c0v_push(S, retval);
        free(new_frame); 
        break;
      }
      else {
        stack_free(callStack,NULL);
        return val2int(retval);
      }
    }


    /* Arithmetic and Logical operations */

    case IADD:{
      pc++;
      int32_t y = pop_int(S);
      int32_t x = pop_int(S);
      int32_t res = x+y;
      push_int(S, res);
      break;
    }

    case ISUB:{
      pc++;
      int32_t y = pop_int(S);
      int32_t x = pop_int(S);
      int32_t res = x-y;
      push_int(S, res);
      break;
    }

    case IMUL:{
      pc++;
      int32_t y = pop_int(S);
      int32_t x = pop_int(S);
      int32_t res = x*y;
      push_int(S, res);
      break;
    }

    case IDIV:{
      pc++;
      int32_t y = pop_int(S);
      int32_t x = pop_int(S);
      if ((y == (int32_t) 0) || ((x == INT_MIN) && (y == (int32_t) -1))) {
        c0_arith_error("arithematic error");
      }
      else {
        int32_t res = x/y;
        push_int(S, res);
      }
      break;
    }

    case IREM:{
      pc++;
      int32_t y = pop_int(S);
      int32_t x = pop_int(S);
      if ((y == (int32_t) 0) || ((x == INT_MIN) && (y == (int32_t) -1))) {
        c0_arith_error("arithematic error");
      }
      else {
        int32_t res = x%y;
        push_int(S, res);
      }
      break;
    }

    case IAND: {
      pc++;
      int32_t y = pop_int(S);
      int32_t x = pop_int(S);
      int32_t res = x&y;
      push_int(S, res);
      break;
    }

    case IOR:{
      pc++;
      int32_t y = pop_int(S);
      int32_t x = pop_int(S);
      int32_t res = x|y;
      push_int(S, res);
      break;
    }

    case IXOR:{
      pc++;
      int32_t y = pop_int(S);
      int32_t x = pop_int(S);
      int32_t res = x^y;
      push_int(S, res);
      break;
    }

    case ISHR:{
      pc++;
      int32_t y = pop_int(S);
      int32_t x = pop_int(S);
      if ((y < (int32_t) 0) || (y >= (int32_t) 32)) {
        c0_arith_error("shift error");
      }
      int32_t res = x >> y;
      push_int(S, res);
      break;
    }

    case ISHL: {
      pc++;
      int32_t y = pop_int(S);
      int32_t x = pop_int(S);
      if ((y < (int32_t) 0) || (y >= (int32_t) 32)) {
        c0_arith_error("shift error");
      }
      int32_t res = x << y;
      push_int(S, res);
      break;
    }


    /* Pushing constants */

    case BIPUSH:{
      pc++;
      int32_t x = (int32_t) ((int8_t)P[pc]);
      push_int(S,x);
      pc++;
      break;
    }

    case ILDC:{
      pc++;
      uint16_t x = (((uint16_t) P[pc]) << 8) | (uint16_t)P[pc+1];
      int32_t n = bc0->int_pool[x];
      push_int(S, n);
      pc++;
      pc++;
      break;
    }

    case ALDC: {
      pc++;
      uint16_t x = ((uint16_t)P[pc]) << 8;
      pc++;
      x = x|(uint16_t)P[pc]; 
      char *a = &(bc0->string_pool[x]);
      push_ptr(S, a);
      pc++;
      break;
    }

    case ACONST_NULL:{
      pc++;
      void* ptr = NULL;
      push_ptr(S,ptr);
      break;
    }


    /* Operations on local variables */

    case VLOAD:{
      pc++;
      int val = (int)P[pc];
      c0v_push(S,V[val]);
      pc++;
      break;
    }

    case VSTORE:{
      pc++;
      c0_value v = c0v_pop(S);
      int val = (int)P[pc];
      V[val] = v;
      pc++;
      break;
    }


    /* Assertions and errors */

    case ATHROW:{
      pc++;
      void *a = pop_ptr(S);
      c0_user_error(a);
      break;
    }

    case ASSERT:{
      pc++;
      void *a = pop_ptr(S);
      int32_t x = pop_int(S);
      if (x == 0) c0_assertion_failure(a);
      break;
    }


    /* Control flow operations */

    case NOP: {
      pc ++;
      break;
    }

    case IF_CMPEQ:{
      pc++;
      c0_value v2 = c0v_pop(S);
      c0_value v1 = c0v_pop(S);
      if (val_equal(v1, v2)) {
        int16_t count = (((int16_t) P[pc]) << 8) | ((int16_t) P[pc+1]);
        pc += count-1;
        break;
      }
      pc += 2;
      break;
    }

    case IF_CMPNE:{
      pc++;
      c0_value v2 = c0v_pop(S);
      c0_value v1 = c0v_pop(S);
      if (!val_equal(v1,v2)) {
        int16_t count = (((int16_t) P[pc]) << 8) | ((int16_t) P[pc+1]);
        pc += count-1;
        break;
      }
      pc += 2;
      break;
    }

    case IF_ICMPLT:{
      pc++;
      int32_t y = pop_int(S);
      int32_t x = pop_int(S);
      if (x < y) {
        int16_t count = (((int16_t) P[pc]) << 8) | ((int16_t) P[pc+1]);
        pc += count-1;
        break;
      }
      pc += 2;
      break;
    }

    case IF_ICMPGE:{
      pc++;
      int32_t y = pop_int(S);
      int32_t x = pop_int(S);
      if (x >= y) {
        int16_t count = (((int16_t) P[pc]) << 8) | ((int16_t) P[pc+1]);
        pc += count-1;
        break;
      }
      pc += 2;
      break;
    }

    case IF_ICMPGT:{
      pc++;
      int32_t y = pop_int(S);
      int32_t x = pop_int(S);
      if (x > y) {
        int16_t count = (((int16_t) P[pc]) << 8) | ((int16_t) P[pc+1]);
        pc += count-1;
        break;
      }
      pc += 2;
      break;
    }

    case IF_ICMPLE: {
      pc++;
      int32_t y = pop_int(S);
      int32_t x = pop_int(S);
      if (x <= y) {
        int16_t count = (((int16_t) P[pc]) << 8) | ((int16_t) P[pc+1]);
        pc += count-1;
        break;
      }
      pc +=2;
      break;
    }

    case GOTO:{
      pc++;
      int16_t count = (((int16_t) P[pc]) << 8) | ((int16_t) P[pc+1]);
      pc += count-1;
      break;
    }


    /* Function call operations: */

    case INVOKESTATIC: {
      frame *new_frame = xcalloc(sizeof(frame), 1);
      new_frame->S = S;      
      new_frame->P = P;
      new_frame->V = V;
      new_frame->pc = pc + 3;
      push(callStack, new_frame);
      pc ++;
      uint16_t count = (((int16_t) P[pc]) << 8) | ((int16_t) P[pc+1]);
      pc --;
      uint16_t len = bc0->function_pool[count].num_args; //size
      uint16_t nums = bc0->function_pool[count].num_vars;
      S = c0v_stack_new();
      P = bc0->function_pool[count].code;
      V = xcalloc(sizeof(frame), nums);
      pc = 0;
      for (int i = 0; i < len; i++) {
        c0_value v = c0v_pop(new_frame->S);
        V[len-1-i] = v;
      }
      break;
    }

    case INVOKENATIVE: {
      pc++;
      uint16_t count = (((uint16_t) P[pc]) << 8) | ((uint16_t) P[pc+1]);
      struct native_info n_pool = bc0->native_pool[count];
      int8_t len = n_pool.num_args;
      c0_value *val = xcalloc(sizeof(c0_value), len);
      for (int i = 0; i < len; i++) {
        val[len-1-i] = c0v_pop(S); 
      }
      int index = n_pool.function_table_index;
      c0_value result = (*native_function_table[index])(val); // c0_value native_fn(c0_value *);
      c0v_push(S,result);
      free(val);
      pc += 2;
      break;
    }

    /* Memory allocation and access operations: */

    case NEW: {
      pc ++;
      uint8_t count = P[pc];
      char *a = xcalloc(count,1);
      push_ptr(S, (void*) a);
      pc ++;
      break;
    }

    case IMLOAD: {
      pc ++;
      void *a = pop_ptr(S);
      if (a == NULL) c0_memory_error("memory-related error");
      int32_t x = *((int*)a);
      push_int(S, x);
      break;
    }

    case IMSTORE: {
      pc ++;
      int32_t x = pop_int(S);
      void *a = pop_ptr(S);
      if (a == NULL) c0_memory_error("memory-related error");
      *((int32_t*)a) = x;
      break;
    }

    case AMLOAD: {
      pc++;
      void **a = (void**) pop_ptr(S);
      if (a == NULL) c0_memory_error("memory-related error");
      push_ptr(S,*a);
      break;
    }

    case AMSTORE: {
      pc++;
      void *b = pop_ptr(S);
      void **a = (void**) pop_ptr(S);
      if (a == NULL) c0_memory_error("memory-related error");
      *a = b;
      break;
    }

    case CMLOAD: {
      pc ++;
      void *a = pop_ptr(S);
      char *c = (char*) a;
      if (c == NULL) c0_memory_error("memory-related error");
      char x = *c;
      push_int(S,x);
      break;
    }

    case CMSTORE: {
      pc++;
      int32_t x = pop_int(S);
      void *a = pop_ptr(S);
      if (a == NULL) c0_memory_error("memory-related error");
      *((char*)a) = x;
      break;
    }

    case AADDF: {
      pc ++;
      uint16_t f = P[pc];
      void *a = pop_ptr(S);
      if (a == NULL) c0_memory_error("memory-related error");
      push_ptr(S, (void*)((char*)a + f));
      pc++;
      break;
    }


    /* Array operations: */

    case NEWARRAY: {
      pc++;
      uint8_t size = P[pc];
      int32_t n = pop_int(S);
      if (n < 0) c0_memory_error("memory-related error");
      c0_array *new_arr = xcalloc(sizeof(c0_array), 1);
      new_arr -> count = n;
      new_arr->elt_size = size;
      new_arr -> elems = (void*) xcalloc(n,size);
      push_ptr(S, (void*) new_arr);
      pc++;
      break;
    }

    case ARRAYLENGTH: {
      pc++;
      void *a = pop_ptr(S);
      c0_array *arr = (c0_array *)a;
      if (arr==NULL) c0_memory_error("memory-related error");
      uint32_t n = arr->count;
      push_int(S,n);
      break;
    }

    case AADDS: {
      pc ++;
      char i = pop_int(S);
      c0_array *a = (c0_array *)pop_ptr(S);
      if (a==NULL) c0_memory_error("memory-related error");
      if (i > (char) a->count) c0_user_error("'i' is not valid index");
      char *x = (char*)(a->elems) + ((a->elt_size) * i);
      push_ptr(S,x);
      break;
    }


    /* BONUS -- C1 operations */

    case CHECKTAG:

    case HASTAG:

    case ADDTAG:

    case ADDROF_STATIC:

    case ADDROF_NATIVE:

    case INVOKEDYNAMIC:

    default:
      fprintf(stderr, "invalid opcode: 0x%02x\n", P[pc]);
      abort();
    }
  }

  /* cannot get here from infinite loop */
  assert(false);
}
