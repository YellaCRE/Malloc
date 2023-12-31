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
    "malloc_implicit",
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
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)   // size를 ALIGNMENT의 배수로 맞춰주는 함수


#define SIZE_T_SIZE (ALIGN(sizeof(size_t))) // size_t의 크기보다 크거나 같은 양의 공간 계산
                                            // size_t : 데이터의 최대 크기를 저장할 수 있는 타입(32비트에서는 32비트 / 64비트에서는 64비트)
                                            // unsigned int와의 차이점 : unsigned int는 64비트라고 해서 무조건 64비트 정수인 것은 아니지만 size_t는 무조건 64비트
#define WSIZE 4 // word size
#define DSIZE 8 // double word size
#define CHUNKSIZE (1<<12)   // 초기 가용 블록과 힙 확장을 위한 기본 크기 ( 4096 바이트 )

#define MAX(x, y) ((x) > (y) ? (x) : (y))   // 최댓값

#define PACK(size, alloc) ((size) | (alloc))    // size와 alloc을 합치기 (alloc => 001 : allocated / 000 : free)

#define GET(p)      (*(unsigned int *)(p))   //  주소 p에 있는 값 받아오기
#define PUT(p, val) (*(unsigned int *)(p) = (val))    // p에 val값 넣기

#define GET_SIZE(p)  (GET(p) & ~0x7) // p를 담을 수 있는 블록의 size 구하기 ( 비트연산자를 통해 header, footer에 적힌 size 반환 )
#define GET_ALLOC(p) (GET(p) & 0x1) // p를 0000...01 (alloc) 이나 0000...00 (free) 으로 바꾸기

#define HDRP(bp) ((char *)(bp) - WSIZE) // HeaDer Return Point  현재 블록의 헤더 위치 반환
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)    // FooTer Return Point  현재 블록의 푸터 위치 반환
                                                                // bp + 현재 블록의 크기 = 다음 블록의 bp위치 -> -2word = footer위치

#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE((char *)(bp) - WSIZE))   // 다음 블록의 bp 위치 반환
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE((char *)(bp) - DSIZE))   // 이전 블록의 bp 위치 반환

// 매서드 및 변수 선언
static void *coalesce(void *bp);
static void *extend_heap(size_t words);

static void *find_fit(size_t asize);
static void *find_nextfit(size_t asize);
static void *find_bestfit(size_t asize);

static void place(void *bp, size_t asize);

static char *heap_listp;
static char *next_fit_bp;

/*
 * mm_init - initialize the malloc package.
 */
int mm_init(void) {
    if ( ((heap_listp) = mem_sbrk(4*WSIZE)) == (void *)-1 ) // mem_sbrk에 의해 에러가 발생하면 -1
        return -1;

    PUT(heap_listp, 0);                             // 정렬 패딩
    PUT(heap_listp + (1*WSIZE), PACK(DSIZE, 1));    // 프롤로그 Header
    PUT(heap_listp + (2*WSIZE), PACK(DSIZE, 1));    // 프롤로그 Footer
    PUT(heap_listp + (3*WSIZE), PACK(0, 1));        // 에필로그 Header
    heap_listp += (2*WSIZE);                        // 첫 번째 bp로 이동

    next_fit_bp = heap_listp;

    if ( extend_heap(CHUNKSIZE/WSIZE) == NULL )  // 힙 크기를 더이상 늘릴 수 없을 때, 최대 사이즈를 넘거나 incr가 음수
        return -1;
    return 0;
}

static void *extend_heap(size_t words) {
    char *bp;
    size_t size;

    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE; // word가 홀수면 +1하고 공간 할당받을 준비
    if ( (long)(bp = mem_sbrk(size)) == -1 )    // mem_sbrk에 의해 에러가 발생하면 NULL 반환
        return NULL;

    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));   // 다음 블록의 헤더로 가서 epilogue block header 입력

    return coalesce(bp);
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *bp) {
    size_t size = GET_SIZE(HDRP(bp));   // 할당을 해제하려는 블록의 사이즈 저장
    PUT(HDRP(bp), PACK(size, 0));   // header, footer 둘다 (size, 1) -> (size, 0) 으로 변환
    PUT(FTRP(bp), PACK(size, 0));
    coalesce(bp);   // 할당이 끝난 블록들 즉시 연결
}

/*
 * coalesce
 */
static void *coalesce(void *bp) {
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    if ( prev_alloc && next_alloc ) {   // 앞 뒤 블록이 모두 할당돼있으면
        return bp;
    }
    
    else if ( prev_alloc && !next_alloc ) { // 앞의 블록만 할당되어 있을 때
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }

    else if ( !prev_alloc && next_alloc ) { // 뒤의 블록만 할당되어 있을 때
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }

    else {  // 둘다 할당되지 않았을 때
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }

    // next_fit일 경우
    next_fit_bp = bp;
    return bp;
}

/*
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{
    size_t asize;
    size_t extendsize;
    char *bp;

    if (size == 0)
        return NULL;
    
    if (size <= DSIZE)
        asize = 2*DSIZE;
    else
        asize = DSIZE * ((size + (DSIZE) + (DSIZE-1)) / DSIZE);
    
    // 여기서 fit 종류 설정
    // bp = find_fit(asize);
    bp = find_nextfit(asize);
    // bp = find_bestfit(asize);

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

    for ( bp = heap_listp ; GET_SIZE(HDRP(bp)) > 0 ; bp = NEXT_BLKP(bp) ) {
        if ( !GET_ALLOC(HDRP(bp)) && ( asize <= GET_SIZE(HDRP(bp)) ) ) {
            return bp;
        }
    }
    return NULL;
}

/*
 * find_nextfit : next fit
 */
static void *find_nextfit(size_t asize) {
    char *bp;  // 여기가 first fit과 다르다! 타입이 char

    for ( bp = NEXT_BLKP(next_fit_bp) ; GET_SIZE(HDRP(bp)) > 0 ; bp = NEXT_BLKP(bp) ) {
        if ( !GET_ALLOC(HDRP(bp)) && ( asize <= GET_SIZE(HDRP(bp)) ) ) {
            next_fit_bp = bp;
            return bp;
        }
    }

    for (bp = heap_listp; bp <= next_fit_bp; bp = NEXT_BLKP(bp)){
        if ( !GET_ALLOC(HDRP(bp)) && ( asize <= GET_SIZE(HDRP(bp)) ) ) {
            next_fit_bp = bp;
            return bp;
        }
    }

    return NULL;
}

/*
 * find_bestfit : best fit
 */
static void *find_bestfit(size_t asize) {
    void *bp;
    void *best_bp = NULL;

    for ( bp = heap_listp ; GET_SIZE(HDRP(bp)) > 0 ; bp = NEXT_BLKP(bp) ) {
        if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))) {
            if (!best_bp ||(GET_SIZE(HDRP(bp)) < GET_SIZE(HDRP(best_bp))))  // best_bp가 없거나 갱신될 때 
                best_bp = bp;
        }
    }
    
    return best_bp;  // 기본 값을 NULL로 정의했기 때문에 못찾으면 NULL임
}

/*
 * place
 */
static void place(void *bp, size_t asize) {
    size_t csize = GET_SIZE(HDRP(bp));

    if ( (csize - asize) >= (2 * DSIZE) ) {
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        
        bp = NEXT_BLKP(bp);

        PUT(HDRP(bp), PACK(csize - asize, 0));
        PUT(FTRP(bp), PACK(csize - asize, 0));
    }

    else {
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
    }
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
// void *mm_realloc(void *ptr, size_t size) {
//     void *newptr;
//     size_t copySize;

//     if (ptr == NULL){
//         return mm_malloc(size);
//     }
//     if (size == 0){  // size == 0일 때
//         mm_free(ptr);
//         return NULL;
//     }

//     newptr = mm_malloc(size);
//     copySize = GET_SIZE(HDRP(ptr)) - DSIZE;
//     if (size < copySize){    // 이미 할당된 메모리의 양을 줄일 때
//         copySize = size;
//     }

//     memcpy(newptr, ptr, copySize); // 메모리 복사 ( 덮어쓰기 느낌으로다가 )
//     mm_free(ptr);
//     return newptr;
// }

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
        if (!GET_ALLOC(HDRP(NEXT_BLKP(oldptr))) && (newSize <= addSize)){  // 뒤의 블록이 free이고 용량이 충분하면
            PUT(HDRP(oldptr), PACK(addSize, 1));
            PUT(FTRP(oldptr), PACK(addSize, 1));
            return oldptr;
        }
        else {
            newptr = mm_malloc(newSize);
            if (newptr == NULL){
                return NULL;
            }
            memmove(newptr, oldptr, newSize);  // memcpy 사용 시, overlap 발생
            mm_free(oldptr);
            return newptr;
        }
    }
}