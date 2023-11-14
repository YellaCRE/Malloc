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
    "malloc_seglist",
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

#define SEGREGATED_SIZE (12)  // 가용 리스트의 개수
#define GET_ROOT(class) (*(void **)((char *)(heap_listp) + (WSIZE * class)))  // 해당 가용 리스트의 루트

// 매서드 및 변수 선언
static void *coalesce(void *bp);
static void *extend_heap(size_t words);

static void *find_fit(size_t asize);

static void place(void *bp, size_t asize);

static void add_free_block(void *bp);  // 가용 리스트에 추가하는 함수
static void splice_free_block(void *bp);  // 가용 리스트에서 제거하는 함수

int get_class(size_t size);

static char *heap_listp;  // heap_listp 대신 생성

/*
 * mm_init - initialize the malloc package.
 */
int mm_init(void) {
    // 초기 힙 생성
    if ((heap_listp = mem_sbrk((SEGREGATED_SIZE + 4) * WSIZE)) == (void *)-1) // 8워드 크기의 힙 생성, heap_listp에 힙의 시작 주소값 할당(가용 블록만 추적)
        return -1;
    PUT(heap_listp, 0);  // 정렬 패딩

    PUT(heap_listp + (1 * WSIZE), PACK((SEGREGATED_SIZE + 2) * WSIZE, 1)); // 프롤로그 Header (크기: 헤더 1 + 푸터 1 + segregated list 크기)
    for (int i = 0; i < SEGREGATED_SIZE; i++)
        PUT(heap_listp + ((2 + i) * WSIZE), NULL);
    PUT(heap_listp + ((SEGREGATED_SIZE + 2) * WSIZE), PACK((SEGREGATED_SIZE + 2) * WSIZE, 1)); // 프롤로그 Footer
    PUT(heap_listp + ((SEGREGATED_SIZE + 3) * WSIZE), PACK(0, 1));                             // 에필로그 Header: 프로그램이 할당한 마지막 블록의 뒤에 위치

    heap_listp += (2 * WSIZE);

    if (extend_heap(4) == NULL)  // 최소 사이즈가 4워드여서 그런 듯
        return -1;
    if (extend_heap(CHUNKSIZE / WSIZE) == NULL)  // 힙사이즈 초과 체크
        return -1;

    return 0;
}

// seg free list(class)를 만들고 찾는 함수
int get_class(size_t size) {
    if (size < 16) // 최소 블록 크기는 16바이트 -> 4워드
        return -1; // 잘못된 크기, 이미 init에서 체크함

    // 클래스별 최소 크기
    size_t class_sizes[SEGREGATED_SIZE];
    class_sizes[0] = 16;

    // 주어진 크기에 적합한 클래스 검색
    for (int i = 0; i < SEGREGATED_SIZE; i++) {
        if (i != 0)
            class_sizes[i] = class_sizes[i - 1] << 1;  // 2의 제곱을 쉬프트 연산으로 처리
        if (size <= class_sizes[i])
            return i;  // find 과정
    }

    // 주어진 크기가 마지막 클래스의 범위를 넘어갈 경우, 마지막 클래스로 처리
    return SEGREGATED_SIZE - 1;
}

// 가용 리스트에서 제거하는 함수
static void splice_free_block(void *bp) {
    int class = get_class(GET_SIZE(HDRP(bp))); // 여기서 적합한 가용 리스트를 찾는다
    if (bp == GET_ROOT(class)) { // 분리하려는 블록이 root이면
        GET_ROOT(class) = GET_SUCC(GET_ROOT(class)); // 다음 블록을 루트로 변경
        return;
    }
    
    // 여기는 같네
    GET_SUCC(GET_PRED(bp)) = GET_SUCC(bp);
    if (GET_SUCC(bp) != NULL) 
        GET_PRED(GET_SUCC(bp)) = GET_PRED(bp);
}

// 적합한 가용 리스트를 찾아서 추가하는 함수 -> find 과정이 추가됨
static void add_free_block(void *bp) {
    int class = get_class(GET_SIZE(HDRP(bp)));  // 여기서 적합한 가용 리스트를 찾는다
    
    // GET_ROOT인 것만 제외하면 같다
    GET_SUCC(bp) = GET_ROOT(class);
    if (GET_ROOT(class) != NULL)
        GET_PRED(GET_ROOT(class)) = bp;
    GET_ROOT(class) = bp;  // 루트 설정까지!
}

/*
 * coalesce
 */
static void *coalesce(void *bp) {  // explicit와 동일
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
 * find_fit : first fit
 */
static void *find_fit(size_t asize) {
    int class = get_class(asize);
    void *bp = GET_ROOT(class);
    while (class < SEGREGATED_SIZE) // 현재 탐색하는 클래스가 범위 안에 있는 동안 반복
    {
        bp = GET_ROOT(class);
        while (bp != NULL)
        {
            if ((asize <= GET_SIZE(HDRP(bp)))) // 적합한 사이즈의 블록을 찾으면 반환
                return bp;
            bp = GET_SUCC(bp); // 다음 가용 블록으로 이동
        }
        class += 1;
    }
    return NULL;
}

/*
 * mm_free - explicit와 동일
 */
void mm_free(void *bp) {  // explicit와 동일
    size_t size = GET_SIZE(HDRP(bp));
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    coalesce(bp);
}

/*
 * extend_heap - explicit와 동일
 */
static void *extend_heap(size_t words) {  
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
 * mm_malloc - explicit와 동일
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
 * place - explicit와 동일
 */
static void place(void *bp, size_t asize) {
    splice_free_block(bp);

    size_t csize = GET_SIZE(HDRP(bp));

    if ((csize - asize) >= (2 * DSIZE)) { 
        PUT(HDRP(bp), PACK(asize, 1)); 
        PUT(FTRP(bp), PACK(asize, 1));

        PUT(HDRP(NEXT_BLKP(bp)), PACK((csize - asize), 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK((csize - asize), 0));
        add_free_block(NEXT_BLKP(bp)); 
    }
    else {
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
    }
}

/*
 * mm_realloc - 향상된 아님!
 * 여기서는 향상된 realloc을 쓸 수 없다
 * 할당을 위해 연결을 할 수 없기 때문!
 */
void *mm_realloc(void *ptr, size_t size) {
    void *newptr;
    size_t copySize;

    if (ptr == NULL){
        return mm_malloc(size);
    }
    if (size == 0){  // size == 0일 때
        mm_free(ptr);
        return NULL;
    }

    newptr = mm_malloc(size);
    copySize = GET_SIZE(HDRP(ptr)) - DSIZE;
    if (size < copySize){    // 이미 할당된 메모리의 양을 줄일 때
        copySize = size;
    }

    memcpy(newptr, ptr, copySize); // 메모리 복사 ( 덮어쓰기 느낌으로다가 )
    mm_free(ptr);
    return newptr;
}