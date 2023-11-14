#include "mm.h"

#include <assert.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include "memlib.h"

/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your team information in the following struct.
 ********************************************************/
team_t team = {
    /* Team name */
    "individual",
    /* First member's full name */
    "coyorkdow",
    /* First member's email address */
    "coyorkdow@outlook.com",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""};


/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT - 1)) & ~0x7)

#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

/* ========================= Macros ========================= */                               

#define WSIZE 4  // word and header/footer size (bytes)
#define DSIZE 8  // double word size (bytes)
#define CHUNKSIZE (1 << 12)

#define MINIMUM_TREE_BLOCK_SIZE (3 * DSIZE)

#define MAX(x, y) ((x) > (y) ? (x) : (y))
#define MIN(x, y) ((x) < (y) ? (x) : (y))

#define PACK(size, alloc) ((size) | (alloc))

#define GET(p) (*(unsigned int *)(p))
#define PUT(p, val) (*(unsigned int *)(p) = (val))

#define GET_SIZE(p) (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)

// 새로운 매크로!
// Tag for foot compression, which indicates whether the previous block
// was allocated or not.
#define GET_TAG(p) (GET(p) & 0x2)

// 새로운 매크로! Set or clear allocation bit
#define SET_ALLOC(p) PUT(p, (GET(p) | 0x1))
#define CLR_ALLOC(p) PUT(p, (GET(p) & ~0x1))
#define SET_TAG(p) PUT(p, (GET(p) | 0x2));
#define CLR_TAG(p) PUT(p, (GET(p) & ~0x2));

// 새로운 매크로! Set block's size
#define SET_SIZE(p, size) PUT(p, (size | (GET(p) & 0x7)))

#define HDRP(ptr) ((char *)(ptr)-WSIZE)
#define FTRP(ptr) ((char *)(ptr) + GET_SIZE(HDRP(ptr)) - DSIZE)

#define NEXT_BLKP(ptr) ((char *)(ptr) + GET_SIZE((char *)(ptr)-WSIZE))
#define PREV_BLKP(ptr) ((char *)(ptr)-GET_SIZE((char *)(ptr)-DSIZE))

#define PRED_PTR(ptr) ((char *)(ptr))
#define SUCC_PTR(ptr) ((char *)(ptr) + WSIZE)

// 새로운 매크로! 
#define BP_LESS(bp, size) (GET_SIZE(HDRP(bp)) < size)
#define BP_GREATER(bp, size) (GET_SIZE(HDRP(bp)) > size)
#define BP_GEQ(bp, size) (!BP_LESS(bp, size))
#define BP_LEQ(bp, size) (!BP_GREATER(bp, size))

static char *heap_listp = 0;    
static char *heap_epilogue = 0;  /* 에필로그 헤더를 기억한다 */

static char *free_list_head = 0; /* Pointer to the head of explicit free list*/

#define PRED(ptr) (char *)(free_list_head + GET(PRED_PTR(ptr)))
#define SUCC(ptr) (char *)(free_list_head + GET(SUCC_PTR(ptr)))

#define OFFSET(ptr) ((char *)(ptr)-free_list_head)

#define SET_PRED(self, ptr) PUT(PRED_PTR(self), OFFSET(ptr))
#define SET_SUCC(self, ptr) PUT(SUCC_PTR(self), OFFSET(ptr))

// 새로운 매크로! explicit free list를 간단하게 만든 것
// Link ptr1 and ptr2 as ptr1 is predecessor of ptr2
#define LINK(ptr1, ptr2)  \
  do {                    \
    SET_SUCC(ptr1, ptr2); \
    SET_PRED(ptr2, ptr1); \
  } while (0)

// Remove ptr from linked list -> splice_free_block
#define ERASE(ptr) LINK(PRED(ptr), SUCC(ptr))

// Insert target as successor -> add_free_block
#define INSERT(self, target)  \
  do {                        \
    LINK(target, SUCC(self)); \
    LINK(self, target);       \
  } while (0)

/*********************************************************
 *        Binary Search Tree Definition Begin
 ********************************************************/

// 새로운 매크로! 이진 검색을 하기 위한 정의
#define LCH(ptr) PRED(ptr)
#define RCH(ptr) SUCC(ptr)

#define PARENT_PTR(ptr) ((char *)(ptr) + (2 * WSIZE))
#define PARENT(ptr) (char *)(free_list_head + GET(PARENT_PTR(ptr)))

#define SET_LCH(self, ptr) SET_PRED(self, ptr)
#define SET_RCH(self, ptr) SET_SUCC(self, ptr)
#define SET_PARENT(self, ptr) PUT(PARENT_PTR(self), OFFSET(ptr))

char *NIL = 0; /* NIL 정의! */

/* Replaces subtree u as a child of its parent with subtree v. */
#define TRANSPLANT(root, u, v)              \
  do {                                      \
    if (PARENT(u) == NIL) {                 \
      *(root) = v;                          \
    } else if (u == LCH(PARENT(u))) {       \
      SET_LCH(PARENT(u), v);                \
    } else {                                \
      SET_RCH(PARENT(u), v);                \
    }                                       \
    if (v != NIL) SET_PARENT(v, PARENT(u)); \
  } while (0)

static char *tree_lower_bound(char *root, size_t size) {
  char *r = NIL;
  char *ptr = root;
  while (ptr != NIL && size != GET_SIZE(HDRP(ptr))) {
    if (GET_SIZE(HDRP(ptr)) < size) {
      ptr = RCH(ptr);
    } else {
      r = ptr;
      ptr = LCH(ptr);
    }
  }
  // If r is not NIL, then it points to the first block whose capacity is not
  // less than {size}.
  if (ptr != NIL && GET_SIZE(HDRP(ptr)) == size) {
    return ptr;
  } else {
    return r;
  }
}

static void tree_insert(char **root, char *ptr) {
  SET_LCH(ptr, NIL);
  SET_RCH(ptr, NIL);
  char *y = NIL;
  char *x = *root;
  size_t size = GET_SIZE(HDRP(ptr));
  while (x != NIL) {
    y = x;
    if (GET_SIZE(HDRP(x)) < size) {
      x = RCH(x);
    } else {
      x = LCH(x);
    }
  }
  SET_PARENT(ptr, y);
  if (y == NIL) {
    *root = ptr;
  } else if (GET_SIZE(HDRP(y)) < size) {
    SET_RCH(y, ptr);
  } else {
    SET_LCH(y, ptr);
  }
}

static void tree_erase(char **root, char *ptr) {
  if (LCH(ptr) == NIL) {
    TRANSPLANT(root, ptr, RCH(ptr));
  } else if (RCH(ptr) == NIL) {
    TRANSPLANT(root, ptr, LCH(ptr));
  } else {
    char *y = RCH(ptr);
    while (LCH(y) != NIL) y = LCH(y);
    // y is the minimum node in subtree RCH(ptr), it may has RCH but has no LCH.
    if (PARENT(y) != ptr) {
      TRANSPLANT(root, y, RCH(y));
      SET_RCH(y, RCH(ptr));
      SET_PARENT(RCH(y), y);
    }
    TRANSPLANT(root, ptr, y);
    SET_LCH(y, LCH(ptr));
    SET_PARENT(LCH(y), y);
  }
}
/*********************************************************
 *        Binary Search Tree Definition End
 ********************************************************/

static char *tree_root = 0;

#define ERASE_FROM_TREE_OR_LIST(root, bp)     \
  do {                                        \
    if (BP_LESS(bp, MINIMUM_TREE_BLOCK_SIZE)) \
      ERASE(bp);                              \
    else                                      \
      tree_erase(root, bp);                   \
  } while (0)

static void *extend_heap(size_t words);
static void *coalesce(void *bp);
static void *find_fit(size_t asize);
static void *place(void *bp, size_t asize, bool trivial_split);

/* Check if split free block from the back of the old block */
#define SPLIT_BACK(asize, next_size) (asize < 96 || next_size < 48)

/* ========================= FUNCTION ========================= */
/*
 * mm_init - initialize the malloc package.
 */
int mm_init(void) {
  if ((heap_listp = mem_sbrk(6 * WSIZE)) == (void *)-1) {
    return -1;
  }

  free_list_head = heap_listp + WSIZE; /* Init head ptr */
  NIL = free_list_head;                /* Init NIL, which is used in BST */
  tree_root = NIL;

  PUT(heap_listp, 0);                            /* Alignment padding */
  PUT(heap_listp + WSIZE, 0);                    // 여기가 특이하다!
  PUT(heap_listp + (2 * WSIZE), 0);              // 패딩과 프롤로그 사이에 무언가 존재!
  PUT(heap_listp + (3 * WSIZE), PACK(DSIZE, 1)); /* Prologue header */
  PUT(heap_listp + (4 * WSIZE), PACK(DSIZE, 1)); /* Prologue footer */
  PUT(heap_listp + (5 * WSIZE), PACK(0, 3));     /* Epilogue header */
  heap_listp += (4 * WSIZE);

  if (extend_heap(CHUNKSIZE / WSIZE) == NULL) {
    return -1;
  }
  
  // 새로운 부분! 태그 설정
  SET_TAG(HDRP(NEXT_BLKP(heap_listp)));
  if (BP_LESS(NEXT_BLKP(heap_listp), MINIMUM_TREE_BLOCK_SIZE)) {
    INSERT(free_list_head, NEXT_BLKP(heap_listp));
  } else {
    tree_insert(&tree_root, NEXT_BLKP(heap_listp));
  }

  return 0;
}

static inline size_t size_in_need(size_t size) {
  return MAX(DSIZE * 2, (ALIGN(size) - size >= WSIZE) ? ALIGN(size)
                                                      : (ALIGN(size) + DSIZE));
}

static void *extend_heap(size_t words) {
  char *bp;
  size_t size;

  size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;
  if ((long)(bp = mem_sbrk(size)) == -1) {
    return NULL;
  }
  
  // 헤더 설정이 다르다!
  /* Initialize free block header/footer and the epilogue header */
  SET_SIZE(HDRP(bp), size); /* Free block header */
  CLR_ALLOC(HDRP(bp));

  PUT(FTRP(bp), PACK(size, 0));         /* Free block footer */
  PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); /* New epilogue header */
  
  heap_epilogue = HDRP(NEXT_BLKP(bp));

  return coalesce(bp);
}

// 새로운 함수! 그런데 이게 사실상 mm_malloc이네
void *mm_malloc_wrapped(size_t size, bool realloc) {
  size_t asize;
  size_t extendsize;
  char *bp;

  if (size == 0) {
    return NULL;
  }

  asize = size_in_need(size);  // 이것도 약간 다른데 거의 비슷하다

  if (asize < MINIMUM_TREE_BLOCK_SIZE && (bp = find_fit(asize)) != NULL) {
    return place(bp, asize, false);
  }

  // 새로운 분기! asize >= MINIMUM_TREE_BLOCK_SIZE일 때
  /* Search the BST */
  if ((bp = tree_lower_bound(tree_root, asize)) != NIL) {
    tree_erase(&tree_root, bp);
    return place(bp, asize, false);
  }


  extendsize = MAX(asize, CHUNKSIZE);
  if (!realloc && !GET_TAG(heap_epilogue)) {  // 새로운 분기! extendsize를 조정하는 부분
    extendsize -= GET_SIZE(heap_epilogue - WSIZE);
  }

  if ((bp = extend_heap(extendsize / WSIZE)) == NULL) {
    return NULL;
  }
  return place(bp, asize, false);
}

/*
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size) { return mm_malloc_wrapped(size, false); }

/*
 * find_fit - Perform a first-fit search of the implicit free list.
 */
void *find_fit(size_t asize) {
  char *ptr = free_list_head;
  while ((ptr = SUCC(ptr)) != free_list_head) {
    if (GET_SIZE(HDRP(ptr)) >= asize) {
      ERASE(ptr);  // 이거 추가된다!
      return ptr;
    }
  }
  return NULL;
}

/*
 * place - Place the requested block at the beginning of the free block,
 * splitting only if the size of the remainder would equal or exceed the minimum
 * block size.
 * 여기가 굉장히 복잡하다
 */
void *place(void *bp, size_t asize, bool trivial_split) {
  SET_ALLOC(HDRP(bp));
  size_t csize = GET_SIZE(HDRP(bp));
  if (csize > asize && csize - asize >= 2 * DSIZE) {
    size_t next_size = csize - asize;
    char *next;

    if (trivial_split || SPLIT_BACK(asize, next_size)) {
      SET_SIZE(HDRP(bp), asize);
      next = NEXT_BLKP(bp);
      
      PUT(HDRP(next), PACK(next_size, 0));
      PUT(FTRP(next), PACK(next_size, 0));
    } 
    else {
      next = bp;
      SET_SIZE(HDRP(next), next_size);
      PUT(FTRP(next), PACK(next_size, 0));
      bp = NEXT_BLKP(next);
      SET_ALLOC(HDRP(bp));
      SET_SIZE(HDRP(bp), asize);
    }
    SET_TAG(HDRP(NEXT_BLKP(bp)));
    next = coalesce(next);

    // 여기가 add_free_block
    SET_TAG(HDRP(next));
    CLR_ALLOC(HDRP(next));
    CLR_TAG(HDRP(NEXT_BLKP(next)));
    if (BP_LESS(next, MINIMUM_TREE_BLOCK_SIZE)) {
      INSERT(free_list_head, next);
    } else {
      tree_insert(&tree_root, next);
    }

  }
  SET_TAG(HDRP(NEXT_BLKP(bp)));

  return bp;
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *ptr) {
  size_t size = GET_SIZE(HDRP(ptr));
  
  // 헤더만 좀 다르게 교체해주는 것
  SET_SIZE(HDRP(ptr), size);
  CLR_ALLOC(HDRP(ptr));
  CLR_TAG(HDRP(NEXT_BLKP(ptr)));
  PUT(FTRP(ptr), PACK(size, 0));
  ptr = coalesce(ptr);
  
  // 새로 생긴 부분! free된 노드를 트리에 넣어주어야 하는 것 같다!
  if (BP_LESS(ptr, MINIMUM_TREE_BLOCK_SIZE)) {
    INSERT(free_list_head, ptr);
  } else {
    tree_insert(&tree_root, ptr);
  }
}

static void *coalesce(void *bp) {
  size_t prev_alloc = GET_TAG(HDRP(bp));
  size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
  size_t size = GET_SIZE(HDRP(bp));

  if (prev_alloc && next_alloc) { /* Case 1 */
    // 여기서 free_list에 추가하는 것이 아니다
    return bp;
  } 

  else if (prev_alloc && !next_alloc) { /* Case 2 */
    ERASE_FROM_TREE_OR_LIST(&tree_root, NEXT_BLKP(bp));  // splice_free_block와 같은 역할인 것 같다

    size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
    SET_SIZE(HDRP(bp), size);
    PUT(FTRP(bp), PACK(size, 0));
  } 

  else if (!prev_alloc && next_alloc) { /* Case 3 */
    ERASE_FROM_TREE_OR_LIST(&tree_root, PREV_BLKP(bp));  // splice_free_block

    size += GET_SIZE(HDRP(PREV_BLKP(bp)));
    PUT(FTRP(bp), PACK(size, 0));
    SET_SIZE(HDRP(PREV_BLKP(bp)), size);
    bp = PREV_BLKP(bp);
  } 

  else { /* Case 4 */
    ERASE_FROM_TREE_OR_LIST(&tree_root, NEXT_BLKP(bp));  // splice_free_block
    ERASE_FROM_TREE_OR_LIST(&tree_root, PREV_BLKP(bp));

    size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));
    SET_SIZE(HDRP(PREV_BLKP(bp)), size);
    PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
    bp = PREV_BLKP(bp);
  }

  return bp;
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size) {
  if (ptr == NULL) {
    return mm_malloc(size);
  }
  if (size == 0) {
    mm_free(ptr);
    return NULL;
  }

  void *newptr;
  size_t asize = size_in_need(size);

  size_t next_available_size =
      GET_ALLOC(HDRP(NEXT_BLKP(ptr))) ? 0 : GET_SIZE(HDRP(NEXT_BLKP(ptr)));
  size_t prev_available_size =
      GET_TAG(HDRP(ptr)) ? 0 : GET_SIZE(HDRP(PREV_BLKP(ptr)));
  size_t blocksize = GET_SIZE(HDRP(ptr));

#define COALESCE_NEXT                                    \
  do {                                                   \
    ERASE_FROM_TREE_OR_LIST(&tree_root, NEXT_BLKP(ptr)); \
    blocksize += next_available_size;                    \
    SET_SIZE(HDRP(ptr), blocksize);                      \
    SET_SIZE(FTRP(ptr), blocksize);                      \
    SET_TAG(HDRP(NEXT_BLKP(ptr)));                       \
  } while (0)

#define COALESCE_PREV                                    \
  do {                                                   \
    ERASE_FROM_TREE_OR_LIST(&tree_root, PREV_BLKP(ptr)); \
    char *oldptr = ptr;                                  \
    ptr = PREV_BLKP(ptr);                                \
    memmove(ptr, oldptr, blocksize - WSIZE);             \
    blocksize += prev_available_size;                    \
    SET_SIZE(HDRP(ptr), blocksize);                      \
    SET_SIZE(FTRP(ptr), blocksize);                      \
  } while (0)

#define TRIVAL_PLACE(bp)          \
  do {                            \
    SET_ALLOC(HDRP(bp));          \
    SET_TAG(HDRP(NEXT_BLKP(bp))); \
  } while (0)

  if (blocksize >= asize) {
    TRIVAL_PLACE(ptr);
    return ptr;
  } else if (blocksize + next_available_size >= asize) {
    COALESCE_NEXT;
    TRIVAL_PLACE(ptr);
    return ptr;
  } else if (blocksize + prev_available_size >= asize) {
    COALESCE_PREV;
    TRIVAL_PLACE(ptr);
    return ptr;
  } else if (blocksize + next_available_size + prev_available_size >= asize) {
    COALESCE_NEXT;
    COALESCE_PREV;
    TRIVAL_PLACE(ptr);
    return ptr;
  }

  if (prev_available_size) {
    COALESCE_PREV;
  }
  if (next_available_size) {
    COALESCE_NEXT;
  }
  // Check if ptr points to the last block of the heap, ptr may be NULL
  if (HDRP(NEXT_BLKP(ptr)) == heap_epilogue) {
    TRIVAL_PLACE(ptr);
    char *bp;
    if ((bp = extend_heap((asize - blocksize) / WSIZE)) == NULL) {
      return NULL;
    }
    blocksize += GET_SIZE(HDRP(NEXT_BLKP(ptr)));
    SET_SIZE(HDRP(ptr), blocksize);
    SET_SIZE(FTRP(ptr), blocksize);
    SET_TAG(HDRP(NEXT_BLKP(ptr)));
    return ptr;
  }

  if ((newptr = mm_malloc_wrapped(size, true)) == NULL) {
    return newptr;
  }
  memcpy(newptr, ptr, blocksize - WSIZE);
  mm_free(ptr);
  return newptr;
#undef TRIVAL_PLACE
#undef COALESCE_PREV
#undef COALESCE_NEXT
}