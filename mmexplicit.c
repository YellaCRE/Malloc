#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>

#include "mm.h"
#include "memlib.h"

/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your team information in the following struct.
 ********************************************************/
team_t team = {
    /* Team name */
    "jungle_malloc",
    /* First member's full name */
    "Joe Hwang",
    /* First member's email address */
    "yellacre@cs.cmu.edu",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""
};

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8 // 8 : double word(byte)

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)


#define SIZE_T_SIZE (ALIGN(sizeof(size_t))) 
                                            
                                            
#define WSIZE 4
#define DSIZE 8
#define CHUNKSIZE (1<<12)

#define MAX(x, y) ((x) > (y) ? (x) : (y))

#define PACK(size, alloc) ((size) | (alloc))

#define GET(p)      (*(unsigned int *)(p))
#define PUT(p, val) (*(unsigned int *)(p) = (val))

#define GET_SIZE(p)  (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)

#define HDRP(bp) ((char *)(bp) - WSIZE)
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE((char *)(bp) - WSIZE))
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE((char *)(bp) - DSIZE))

#define GET_SUCC(bp) (*(void **)((char *)(bp) + WSIZE))  // 다음 가용 블록의 주소
#define GET_PRED(bp) (*(void **)(bp))                    // 이전 가용 블록의 주소

// 매서드 및 변수 선언
static void *coalesce(void *bp);
static void *extend_heap(size_t words);

static void *find_fit(size_t asize);

static void place(void *bp, size_t asize);

static void add_free_block(void *bp);  // 가용 리스트에 추가하는 함수
static void splice_free_block(void *bp);  // 가용 리스트에서 제거하는 함수

static char *free_listp;  // heap_listp 대신 생성

/*
 * mm_init - initialize the malloc package.
 */
int mm_init(void) {
    // 초기 힙 생성
    if ((free_listp = mem_sbrk(8 * WSIZE)) == (void *)-1) // 8워드 크기의 힙 생성, free_listp에 힙의 시작 주소값 할당(가용 블록만 추적)
        return -1;
    
    PUT(free_listp, 0);                                // 정렬 패딩
    PUT(free_listp + (1 * WSIZE), PACK(2 * WSIZE, 1)); // 프롤로그 Header
    PUT(free_listp + (2 * WSIZE), PACK(2 * WSIZE, 1)); // 프롤로그 Footer
    
    // explicit에서 새로 추가되는 부분
    PUT(free_listp + (3 * WSIZE), PACK(4 * WSIZE, 0)); // 첫 가용 블록의 헤더
    PUT(free_listp + (4 * WSIZE), NULL);               // 이전 가용 블록의 주소
    PUT(free_listp + (5 * WSIZE), NULL);               // 다음 가용 블록의 주소
    PUT(free_listp + (6 * WSIZE), PACK(4 * WSIZE, 0)); // 첫 가용 블록의 푸터
    // 여기까지

    PUT(free_listp + (7 * WSIZE), PACK(0, 1));         // 에필로그 Header: 프로그램이 할당한 마지막 블록의 뒤에 위치하며, 블록이 할당되지 않은 상태를 나타냄
    free_listp += (4 * WSIZE);                         // 첫번째 가용 블록의 bp

    if (extend_heap(CHUNKSIZE / WSIZE) == NULL)
        return -1;

    return 0;
}

static void *extend_heap(size_t words) {  // implicit와 동일
    char *bp;
    size_t size;

    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;
    if ( (long)(bp = mem_sbrk(size)) == -1 )
        return NULL;

    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));

    return coalesce(bp);
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *bp) {  // implicit와 동일
    size_t size = GET_SIZE(HDRP(bp));
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    coalesce(bp);
}

// LIFO를 쓸 때
// 가용 리스트에 추가하는 함수
static void add_free_block(void *bp) {
    GET_SUCC(bp) = free_listp;     // bp의 SUCC은 루트가 가리키던 블록
    if (free_listp != NULL)        // free list에 블록이 존재했을 경우만
        GET_PRED(free_listp) = bp; // 루트였던 블록의 PRED를 추가된 블록으로 연결
    free_listp = bp;               // 루트를 현재 블록으로 변경
}

// 가용 리스트에서 제거하는 함수
static void splice_free_block(void *bp) {
    if (bp == free_listp){                 // 분리하려는 블록이 루트이면, case 1
        free_listp = GET_SUCC(free_listp); // 다음 블록을 루트로 변경
        return;
    }

    // 이전 블록의 SUCC을 다음 가용 블록으로 연결
    GET_SUCC(GET_PRED(bp)) = GET_SUCC(bp);  
    
    if (GET_SUCC(bp) != NULL) // 다음 가용 블록이 있을 경우만
        // 다음 블록의 PRED를 이전 블록으로 변경
        GET_PRED(GET_SUCC(bp)) = GET_PRED(bp);
}

/*
 * coalesce
 */
static void *coalesce(void *bp) {
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    if ( prev_alloc && next_alloc ) {   // 앞 뒤 블록이 모두 할당돼있으면
        
        add_free_block(bp); // free_list에 추가
        
        return bp;
    }
    
    else if ( prev_alloc && !next_alloc ) { // 앞의 블록만 할당되어 있을 때
        
        splice_free_block(NEXT_BLKP(bp)); // 뒤쪽 free block은 제거하고 앞이랑 합쳐준다.

        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }

    else if ( !prev_alloc && next_alloc ) { // 뒤의 블록만 할당되어 있을 때
        
        splice_free_block(PREV_BLKP(bp)); // 앞쪽 free block은 제거하고 현재랑 합쳐준다

        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));  // 앞쪽 free block의 헤더를 바꿔준다!
        bp = PREV_BLKP(bp);
    }

    else {  // 둘다 할당되지 않았을 때

        splice_free_block(PREV_BLKP(bp)); // 이전 가용 블록을 free_list에서 제거
        splice_free_block(NEXT_BLKP(bp)); // 다음 가용 블록을 free_list에서 제거

        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }

    add_free_block(bp); // 현재 병합한 가용 블록을 free_list에 추가
    
    return bp;
}

/*
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size) {  // implicit와 동일
    size_t asize;
    size_t extendsize;
    char *bp;

    if (size == 0)
        return NULL;
    
    if (size <= DSIZE)
        asize = 2*DSIZE;
    else
        asize = DSIZE * ((size + (DSIZE) + (DSIZE-1)) / DSIZE);
    
    bp = find_fit(asize);

    if (bp != NULL) {
        place(bp, asize);
        return bp;
    }

    extendsize = MAX(asize, CHUNKSIZE);
    if ((bp = extend_heap(extendsize/WSIZE)) == NULL)
        return NULL;
    place(bp, asize);
    return bp;
}

/*
 * find_fit : first fit
 */
static void *find_fit(size_t asize) {
    void *bp;

    for ( bp = free_listp ; bp != NULL ; bp = GET_SUCC(bp) ) {
        if ( !GET_ALLOC(HDRP(bp)) && ( asize <= GET_SIZE(HDRP(bp)) ) ) {
            return bp;
        }
    }
    return NULL;
}

/*
 * place : LIFO를 쓸 때
 */
static void place(void *bp, size_t asize) {
    splice_free_block(bp); // free_list에서 해당 블록 제거

    size_t csize = GET_SIZE(HDRP(bp)); // 현재 블록의 크기

    if ((csize - asize) >= (2 * DSIZE)) { // 차이가 최소 블록 크기 16보다 같거나 크면 분할
        PUT(HDRP(bp), PACK(asize, 1)); // 현재 블록에는 필요한 만큼만 할당
        PUT(FTRP(bp), PACK(asize, 1));

        PUT(HDRP(NEXT_BLKP(bp)), PACK((csize - asize), 0)); // 남은 크기를 다음 블록에 할당(가용 블록)
        PUT(FTRP(NEXT_BLKP(bp)), PACK((csize - asize), 0));
        add_free_block(NEXT_BLKP(bp)); // 남은 블록을 free_list에 추가
    }
    else {
        PUT(HDRP(bp), PACK(csize, 1)); // 해당 블록 전부 사용
        PUT(FTRP(bp), PACK(csize, 1));
    }
}

/*
 * mm_realloc - implicit와 동일하다!
 */
// 향상된 realloc
void *mm_realloc(void *ptr, size_t size) {
    void *oldptr = ptr;
    void *newptr;

    size_t originalSize = GET_SIZE(HDRP(oldptr));
    size_t newSize = size + DSIZE;
    size_t addSize;

    if (newSize <= originalSize) {
        return oldptr;
    }
    else {
        addSize = originalSize + GET_SIZE(HDRP(NEXT_BLKP(oldptr)));
        if (!GET_ALLOC(HDRP(NEXT_BLKP(oldptr))) && (newSize <= addSize)) {  // 뒤의 블록이 free이고 용량이 충분하면
            PUT(HDRP(oldptr), PACK(addSize, 1));
            PUT(FTRP(oldptr), PACK(addSize, 1));
            return oldptr;
        }
        else {
            newptr = mm_malloc(newSize);
            if (newptr == NULL) {
                return NULL;
            }
            memmove(newptr, oldptr, newSize);  // memcpy 사용 시, overlap 발생
            mm_free(oldptr);
            return newptr;
        }
    }
}