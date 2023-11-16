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
    "malloc_Binary",
    /* First member's full name */
    "",
    /* First member's email address */
    "",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""};


/* ================== 매서드 및 변수 PreDefine ==================== */

static void *extend_heap(size_t words);
static void *coalesce(void *bp);
static void *find_fit(size_t asize);
static void *place(void *bp, size_t asize, bool trivial_split);

static char *heap_listp = 0;    
static char *free_listp = 0;

static char *heap_epilogue = 0;  /* 에필로그 헤더를 기억한다 */

/* ========================= Macros ========================= */ 

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT - 1)) & ~0x7)
#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

#define WSIZE 4  // word and header/footer size (bytes)
#define DSIZE 8  // double word size (bytes)
#define CHUNKSIZE (1 << 12)

#define MAX(x, y) ((x) > (y) ? (x) : (y))
#define MIN(x, y) ((x) < (y) ? (x) : (y))

#define PACK(size, alloc) ((size) | (alloc))

#define GET(p) (*(unsigned int *)(p))
#define PUT(p, val) (*(unsigned int *)(p) = (val))

#define GET_SIZE(p) (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)

#define HDRP(bp) ((char *)(bp) - WSIZE)
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE((char *)(bp) - WSIZE))
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE((char *)(bp) - DSIZE))

// 새로운 매크로! 내 앞 블록이 free인지 alloc인지 확인할 수 있는 태그
#define GET_TAG(p) (GET(p) & 0x2)

// 새로운 매크로! Set or clear allocation bit
#define SET_ALLOC(p) PUT(p, (GET(p) | 0x1))   // GET_ALLOC은 읽기이고 SET_ALLOC은 쓰기이다
#define CLR_ALLOC(p) PUT(p, (GET(p) & ~0x1))  // free로 설정
#define SET_TAG(p) PUT(p, (GET(p) | 0x2));    // 앞 블록이 alloc 상태이다
#define CLR_TAG(p) PUT(p, (GET(p) & ~0x2));   // 앞 블록이 free 상태이다

// 새로운 매크로! Set block's size
#define SET_SIZE(p, size) PUT(p, (size | (GET(p) & 0x7))) // 0111과 and 연산 후 or연산이므로 -> alloc 상태는 유지하고 사이즈만 설정하겠다

// 새로운 매크로! 
#define BP_LESS(bp, size) (GET_SIZE(HDRP(bp)) < size)     // bp가 작으면 TRUE
#define BP_GREATER(bp, size) (GET_SIZE(HDRP(bp)) > size)  // bp가 크면 TRUE
#define BP_GEQ(bp, size) (!BP_LESS(bp, size))
#define BP_LEQ(bp, size) (!BP_GREATER(bp, size))

// 새로운 매크로! 
#define OFFSET(ptr) ((char *)(ptr)-free_listp)                   // free_listp에 대한 ptr의 상대주소 생성 -> 이를 통해 왼쪽, 오른쪽, 부모인지 구분 가능

#define PRED_PTR(bp) ((char *)(bp))                              // 블럭의 첫 번째 칸이 왼쪽 자식 주소
#define SUCC_PTR(bp) ((char *)(bp) + WSIZE)                      // 블럭의 두 번째 칸이 오른쪽 자식 주소
#define PARENT_PTR(ptr) ((char *)(ptr) + (2 * WSIZE))            // 블럭의 세 번째 칸이 부모 주소

#define PRED(bp) (char *)(free_listp + GET(PRED_PTR(bp)))        // PRED_PTR를 절대 주소로 변경
#define SUCC(bp) (char *)(free_listp + GET(SUCC_PTR(bp)))        // SUCC_PTR를 절대 주소로 변경
#define PARENT(ptr) (char *)(free_listp + GET(PARENT_PTR(ptr)))  // PARENT_PTR를 절대 주소로 변경

#define SET_PRED(self, ptr) PUT(PRED_PTR(self), OFFSET(ptr))     // ptr의 상대주소를 왼쪽 자식으로 저장
#define SET_SUCC(self, ptr) PUT(SUCC_PTR(self), OFFSET(ptr))     // ptr의 상대주소를 오른쪽 자식으로 저장

/*********************************************************
 *        Doubly Linked List Definition Begin
 ********************************************************/

// 새로운 매크로! explicit free list를 간단하게 만든 것
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
#define MINIMUM_TREE_BLOCK_SIZE (3 * DSIZE)

#define LCH(ptr) PRED(ptr)  // 왼쪽 자식의 절대 주소를 가져온다
#define RCH(ptr) SUCC(ptr)  // 오른쪽 자식의 절대 주소를 가져온다

#define SET_LCH(self, ptr) SET_PRED(self, ptr)                   // 왼쪽 자식 저장
#define SET_RCH(self, ptr) SET_SUCC(self, ptr)                   // 오른쪽 자식 저장
#define SET_PARENT(self, ptr) PUT(PARENT_PTR(self), OFFSET(ptr)) // 부모 저장

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

// tree에서 size를 find
static char *tree_find(char *root, size_t size) {
  char *nilNode = NIL;
  char *ptr = root;

  while (ptr != NIL && size != GET_SIZE(HDRP(ptr))) {  
    if (GET_SIZE(HDRP(ptr)) < size) {
      ptr = RCH(ptr);
    } 
    else {
      nilNode = ptr;
      ptr = LCH(ptr);
    }
  }

  // ptr을 찾았으면!
  if (ptr != NIL && GET_SIZE(HDRP(ptr)) == size) {
    return ptr;
  } 
  // 못 찾았으면 NIL
  else {
    return nilNode;
  }
}

// tree에 ptr을 삽입
static void tree_insert(char **root, char *ptr) {
  SET_LCH(ptr, NIL);
  SET_RCH(ptr, NIL);

  char *y = NIL;
  char *x = *root;
  size_t size = GET_SIZE(HDRP(ptr));

  while (x != NIL) {
    y = x;
    if (GET_SIZE(HDRP(x)) < size) {  // 루트에서 비교하면서 내려가는 중
      x = RCH(x);
    } 
    else {
      x = LCH(x);
    }
  }
  SET_PARENT(ptr, y);  // 제자리에 도착했으면 부모 설정 -> y를 ptr의 부모로 저장

  if (y == NIL) {  // 그런데 삽입노드 밖에 없다?
    *root = ptr;   // 루트로 설정
  } 
  // y를 기준으로 오른쪽 자식인지 왼쪽 자식인지 설정
  else if (GET_SIZE(HDRP(y)) < size) {  
    SET_RCH(y, ptr);  // ptr의 상대주소를 y의 SUCC 저장 ptr에 저장
  } 
  else {
    SET_LCH(y, ptr);  // ptr의 상대주소를 y의 PRED 저장 ptr에 저장
  }
}

// tree에서 ptr을 삭제
static void tree_erase(char **root, char *ptr) {
  if (LCH(ptr) == NIL) {  // 삭제노드의 왼쪽 자식이 없으면
    TRANSPLANT(root, ptr, RCH(ptr));
  } 
  else if (RCH(ptr) == NIL) {  // 삭제노드의 오른쪽 자식이 없으면
    TRANSPLANT(root, ptr, LCH(ptr));
  } 
  else {  // 자식이 둘 다 있으면
    char *y = RCH(ptr);
    while (LCH(y) != NIL) y = LCH(y);  // SUCC 찾기
    
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

// root에서 bp를 삭제하는 매크로
#define ERASE_FROM_TREE_OR_LIST(root, bp)     \
  do {                                        \
    if (BP_LESS(bp, MINIMUM_TREE_BLOCK_SIZE)) \
      ERASE(bp);                              \
    else                                      \
      tree_erase(root, bp);                   \
  } while (0)

/* Check if split free block from the back of the old block */
#define SPLIT_BACK(asize, next_size) (asize < 96 || next_size < 48)  // 6워드(MINIMUM_TREE_BLOCK_SIZE)가 48이다

/* ========================= FUNCTION ========================= */

/*
 * mm_init - initialize the malloc package.
 */
int mm_init(void) {
  if ((heap_listp = mem_sbrk(6 * WSIZE)) == (void *)-1) {
    return -1;
  }

  free_listp = heap_listp + WSIZE; /* Init head ptr */
  NIL = free_listp;                /* Init NIL, which is used in BST */
  tree_root = NIL;

  PUT(heap_listp, 0);                            /* Alignment padding */
  PUT(heap_listp + WSIZE, 0);                    // free list header
  PUT(heap_listp + (2 * WSIZE), 0);              // 정렬요구사항을 맞춰주기 위해 패딩 1개 더 넣는다 -> 여기는 안쓴다
  PUT(heap_listp + (3 * WSIZE), PACK(DSIZE, 1)); /* Prologue header */
  PUT(heap_listp + (4 * WSIZE), PACK(DSIZE, 1)); /* Prologue footer */
  PUT(heap_listp + (5 * WSIZE), PACK(0, 3));     /* Epilogue header */
  heap_listp += (4 * WSIZE);

  if (extend_heap(CHUNKSIZE / WSIZE) == NULL) {
    return -1;
  }
  
  // 새로운 부분! 태그 설정
  SET_TAG(HDRP(NEXT_BLKP(heap_listp)));  // 아 여기서 태그가 설정되어 있기 때문에 extend_heap에서 초기화하면 안된다
  if (BP_LESS(NEXT_BLKP(heap_listp), MINIMUM_TREE_BLOCK_SIZE)) {
    INSERT(free_listp, NEXT_BLKP(heap_listp));  // 6워드보다 작으면 explicit free list에 추가
  } 
  else {
    tree_insert(&tree_root, NEXT_BLKP(heap_listp));  // 6워드보다 크면 트리에 넣는다
  }

  return 0;
}
// size를 포함할 수 있고 정렬조건에 맞는 size를 반환(최소 사이즈는 4워드)
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
  
  /* Initialize free block header/footer and the epilogue header */
  SET_SIZE(HDRP(bp), size);  // alloc을 유지한 채로 사이즈만 변경
  CLR_ALLOC(HDRP(bp));       // tag는 유지한 채로 free로 설정

  PUT(FTRP(bp), PACK(size, 0));         /* Free block footer */
  PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); /* New epilogue header */
  
  heap_epilogue = HDRP(NEXT_BLKP(bp));

  return coalesce(bp);
}

// 새로운 함수! mm_malloc을 포함한 wrapper이다
void *mm_malloc_wrapped(size_t size, bool realloc) {
  size_t asize;
  size_t extendsize;
  char *bp;

  if (size == 0) {
    return NULL;
  }

  asize = size_in_need(size);  // 필요한만큼만 asize를 불러온다

  // asize가 MINIMUM_TREE_BLOCK_SIZE보다 작으면 free list에서 찾고
  if (asize < MINIMUM_TREE_BLOCK_SIZE && (bp = find_fit(asize)) != NULL) {
    return place(bp, asize, false);
  }

  // asize가 MINIMUM_TREE_BLOCK_SIZE보다 크면 tree에서 찾는다
  if ((bp = tree_find(tree_root, asize)) != NIL) {
    tree_erase(&tree_root, bp);       // 트리에서 bp(적절한 free block)를 삭제하고
    return place(bp, asize, false);   // bp에 할당
  }

  // 못 찾으면 새로 확장
  extendsize = MAX(asize, CHUNKSIZE);
  if (!realloc && !GET_TAG(heap_epilogue)) {  // realloc이 False이고 heap_epilogue의 앞 블록이 free이면
    extendsize -= GET_SIZE(heap_epilogue - WSIZE); // heap_epilogue의 앞 블록의 사이즈만큼 줄여서 확장한다 -> 정말 필요한만큼만 할당하기 위함
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
  char *ptr = free_listp
;
  while ((ptr = SUCC(ptr)) != free_listp
) {
    if (GET_SIZE(HDRP(ptr)) >= asize) {
      ERASE(ptr);  // 링크드 리스트에서 삭제
      return ptr;
    }
  }
  return NULL;
}

/*
 * place - Place the requested block at the beginning of the free block,
 * splitting only if the size of the remainder would equal or exceed the minimum
 * block size.
 */
void *place(void *bp, size_t asize, bool trivial_split) {
  SET_ALLOC(HDRP(bp));                // bp를 alloc으로 설정
  size_t csize = GET_SIZE(HDRP(bp));  // bp의 사이즈

  if (csize > asize && csize - asize >= 2 * DSIZE) {  // 여유공간이 4워드 이상이면 분할한다
    size_t next_size = csize - asize;                 // 여유공간
    char *next;

    // trivial_split
    if (trivial_split || SPLIT_BACK(asize, next_size)) { 
      SET_SIZE(HDRP(bp), asize);
      next = NEXT_BLKP(bp);
      
      PUT(HDRP(next), PACK(next_size, 0));
      PUT(FTRP(next), PACK(next_size, 0));
    } 
    // next size가 6워드 이상이면 앞 쪽 free block과 합쳐서 트리에 넣음으로써 외부 단편화를 해소할 수 있다
    else {
      next = bp;
      SET_SIZE(HDRP(next), next_size);
      PUT(FTRP(next), PACK(next_size, 0));  // 앞 쪽에 free block을 위치하게 만든다

      bp = NEXT_BLKP(next);
      SET_ALLOC(HDRP(bp));
      SET_SIZE(HDRP(bp), asize);  // 그리고 뒤에다가 alloc block
    }
    SET_TAG(HDRP(NEXT_BLKP(bp)));  // bp에 태그 설정
    next = coalesce(next);  // free된 여유공간은 연결처리, 반환된 next는 합쳐진 후 bp를 의미한다

    // next를 free로 설정하는 설정 콤보
    SET_TAG(HDRP(next));             // next 앞 블록인 bp가 alloc 상태임을 표시
    CLR_ALLOC(HDRP(next));           // next free 설정
    CLR_TAG(HDRP(NEXT_BLKP(next)));  // next의 뒷 블록 태그 수정

    if (BP_LESS(next, MINIMUM_TREE_BLOCK_SIZE)) {  // 다시 next의 크기가 6워드보다 작으면 free list
      INSERT(free_listp, next);  
    } 
    else {
      tree_insert(&tree_root, next);              // 크면 트리에 넣는다
    }
  }  

  SET_TAG(HDRP(NEXT_BLKP(bp)));     // next 앞 블록인 bp가 alloc 상태임을 표시(중복처리이지만 상관없다)
  return bp;
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *bp) {
  size_t size = GET_SIZE(HDRP(bp));
  
  // free 설정 콤보
  SET_SIZE(HDRP(bp), size);
  CLR_ALLOC(HDRP(bp));
  CLR_TAG(HDRP(NEXT_BLKP(bp)));
  PUT(FTRP(bp), PACK(size, 0));
  bp = coalesce(bp);
  
  if (BP_LESS(bp, MINIMUM_TREE_BLOCK_SIZE)) {
    INSERT(free_listp, bp);       // 길이가 짧으면 explicit free list
  } else {
    tree_insert(&tree_root, bp);  // 길면 트리에
  }
}

static void *coalesce(void *bp) {
  size_t prev_alloc = GET_TAG(HDRP(bp));  // GET_ALLOC(FTRP(PREV_BLKP(bp)));의 최적화 코드다
  size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
  size_t size = GET_SIZE(HDRP(bp));

  if (prev_alloc && next_alloc) { // 앞 뒤 블록이 모두 alloc이면
    return bp;
  } 

  else if (prev_alloc && !next_alloc) { // 뒤의 블록만 free일 때
    ERASE_FROM_TREE_OR_LIST(&tree_root, NEXT_BLKP(bp));  // splice_free_block와 같은 역할인 것 같다

    size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
    SET_SIZE(HDRP(bp), size);
    PUT(FTRP(bp), PACK(size, 0));
  } 

  else if (!prev_alloc && next_alloc) { // 앞의 블록만 free일 때
    ERASE_FROM_TREE_OR_LIST(&tree_root, PREV_BLKP(bp));  // splice_free_block

    size += GET_SIZE(HDRP(PREV_BLKP(bp)));
    PUT(FTRP(bp), PACK(size, 0));
    SET_SIZE(HDRP(PREV_BLKP(bp)), size);
    bp = PREV_BLKP(bp);
  } 

  else { // 둘 다 free일 때
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

  size_t next_available_size = GET_ALLOC(HDRP(NEXT_BLKP(ptr))) ? 0 : GET_SIZE(HDRP(NEXT_BLKP(ptr)));
  size_t prev_available_size = GET_TAG(HDRP(ptr)) ? 0 : GET_SIZE(HDRP(PREV_BLKP(ptr)));
  size_t originalSize = GET_SIZE(HDRP(ptr));

// next를 coalesce하는 macro
#define COALESCE_NEXT                                    \
  do {                                                   \
    ERASE_FROM_TREE_OR_LIST(&tree_root, NEXT_BLKP(ptr)); \
    originalSize += next_available_size;                    \
    SET_SIZE(HDRP(ptr), originalSize);                      \
    SET_SIZE(FTRP(ptr), originalSize);                      \
    SET_TAG(HDRP(NEXT_BLKP(ptr)));                       \
  } while (0)

// prev를 coalesce하는 macro
#define COALESCE_PREV                                    \
  do {                                                   \
    ERASE_FROM_TREE_OR_LIST(&tree_root, PREV_BLKP(ptr)); \
    char *oldptr = ptr;                                  \
    ptr = PREV_BLKP(ptr);                                \
    memmove(ptr, oldptr, originalSize - WSIZE);             \
    originalSize += prev_available_size;                    \
    SET_SIZE(HDRP(ptr), originalSize);                      \
    SET_SIZE(FTRP(ptr), originalSize);                      \
  } while (0)

// bp를 alloc하는 macro
#define TRIVAL_PLACE(bp)          \
  do {                            \
    SET_ALLOC(HDRP(bp));          \
    SET_TAG(HDRP(NEXT_BLKP(bp))); \
  } while (0)

  /*
  * improved realloc
  */
  // originalSize로만 asize를 커버할 수 있으면
  if (originalSize >= asize) {
    TRIVAL_PLACE(ptr);
    return ptr;
  } 
  // next_available_size와 합쳐서 커버가 가능하면
  else if (originalSize + next_available_size >= asize) {
    COALESCE_NEXT;
    TRIVAL_PLACE(ptr);
    return ptr;
  } 
  // prev_available_size와 합쳐서 커버가 가능하면
  else if (originalSize + prev_available_size >= asize) {
    COALESCE_PREV;
    TRIVAL_PLACE(ptr);
    return ptr;
  } 
  // 앞 뒤 모두를 합쳐서 커버할 수 있으면
  else if (originalSize + next_available_size + prev_available_size >= asize) {
    COALESCE_NEXT;
    COALESCE_PREV;
    TRIVAL_PLACE(ptr);
    return ptr;
  }

  // 그냥 커버할 수 없으면 일단 다 합친다
  if (prev_available_size) {
    COALESCE_PREV;
  }
  if (next_available_size) {
    COALESCE_NEXT;
  }

  // 만약 ptr이 마지막 블럭이라면
  if (HDRP(NEXT_BLKP(ptr)) == heap_epilogue) {
    TRIVAL_PLACE(ptr);
    char *bp;

    // 필요한만큼만 확장한다
    if ((bp = extend_heap((asize - originalSize) / WSIZE)) == NULL) {
      return NULL;
    }

    originalSize += GET_SIZE(HDRP(NEXT_BLKP(ptr))); // NEXT_BLKP(ptr) = bp이다
    SET_SIZE(HDRP(ptr), originalSize);
    SET_SIZE(FTRP(ptr), originalSize);
    SET_TAG(HDRP(NEXT_BLKP(ptr)));
    return ptr;
  }

  // ptr이 마지막 블럭이 아니라면 size만큼 malloc한다
  if ((newptr = mm_malloc_wrapped(size, true)) == NULL) {
    return newptr;
  }
  memcpy(newptr, ptr, originalSize - WSIZE);
  mm_free(ptr);
  return newptr;
#undef TRIVAL_PLACE
#undef COALESCE_PREV
#undef COALESCE_NEXT
}
