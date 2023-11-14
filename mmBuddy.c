// 단편화 때문에 case5를 통과하지 못한다.

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
    "malloc_buddy",
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
// #define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE) buddy에서는 풋터가 필요없기 때문에 삭제된다

#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE((char *)(bp) - WSIZE))
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE((char *)(bp) - DSIZE))

#define GET_SUCC(bp) (*(void **)((char *)(bp) + WSIZE))
#define GET_PRED(bp) (*(void **)(bp))

#define SEGREGATED_SIZE (20) // buddy system의 class 개수
#define GET_ROOT(class) (*(void **)((char *)(heap_listp) + (WSIZE * class)))

// 매서드 및 변수 선언
static void *coalesce(void *bp);
static void *extend_heap(size_t words);

static void *find_fit(size_t asize);

static void place(void *bp, size_t asize);

static void add_free_block(void *bp);
static void splice_free_block(void *bp);

int get_class(size_t size);

static char *heap_listp;

/*
 * mm_malloc
 */
void *mm_malloc(size_t size) {  // implicit와 동일
    size_t asize = 16;  // 최소 사이즈 16바이트
    size_t extendsize;
    char *bp;

    if (size == 0)
        return NULL;
    
    // 사이즈 조정이 다르다
    while (asize < size + DSIZE) { // 요청받은 size에 8(헤더와 푸터 크기)를 더한 값을 2의 n승이 되도록 올림
        asize <<= 1;
    }
    
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
 * place - 2의 제곱 수 처리
 */
static void place(void *bp, size_t asize) {
    splice_free_block(bp);
    size_t csize = GET_SIZE(HDRP(bp));

    while (asize != csize) // 사용하려는 asize와 블록의 크기 csize가 다르면
    {
        csize >>= 1;                           // 블록의 크기를 반으로 나눔
        PUT(HDRP(bp + csize), PACK(csize, 0)); // 뒷부분을 가용 블록으로 변경
        add_free_block(bp + csize);            // 뒷부분을 가용 블록 리스트에 추가
    }
    PUT(HDRP(bp), PACK(csize, 1)); // 크기가 같아지면 해당 블록 사용 처리
}

// 어짜피 class가 2의 제곱수이기 때문에 코드가 간단해짐!
int get_class(size_t size) {
    int next_power_of_2 = 1;
    int class = 0;
    while (next_power_of_2 < size && class + 1 < SEGREGATED_SIZE) {
        next_power_of_2 <<= 1;
        class ++;
    }

    return class;
}

/*
 * mm_free - 풋터는 없다
 */
void mm_free(void *bp) {
    size_t size = GET_SIZE(HDRP(bp));
    PUT(HDRP(bp), PACK(size, 0));
    coalesce(bp);
}

/*
 * coalesce - 여기가 핵심인데 구조가 아예 다르다
 */
static void *coalesce(void *bp) {
    add_free_block(bp);                                      // 현재 블록을 free list에 추가
    size_t csize = GET_SIZE(HDRP(bp));                       // 반환할 사이즈
    void *root = heap_listp + (SEGREGATED_SIZE + 1) * WSIZE; // 실제 메모리 블록들이 시작하는 위치
    void *left_buddyp;                                       // 왼쪽 버디의 bp
    void *right_buddyp;                                      // 오른쪽 버디의 bp

    while (1) {
        // 좌우 버디의 bp 파악
        if ((bp - root) & csize) { // 현재 블록에서 힙까지의 메모리 합(bp - root)과 csize가 중복되는 비트가 있다면 현재 블록은 오른쪽 버디에 해당
            left_buddyp = bp - csize;
            right_buddyp = bp;
        }
        else {
            right_buddyp = bp + csize;
            left_buddyp = bp;
        }

        // 양쪽 버디가 모두 가용 상태이고, 각 사이즈가 동일하면 (각 버디가 분할되어있지 않으면)
        if (!GET_ALLOC(HDRP(left_buddyp)) && !GET_ALLOC(HDRP(right_buddyp)) && GET_SIZE(HDRP(left_buddyp)) == GET_SIZE(HDRP(right_buddyp))) {
            splice_free_block(left_buddyp); // 양쪽 버디를 모두 가용 리스트에서 제거
            splice_free_block(right_buddyp);
            csize <<= 1;                            // size를 2배로 변경
            PUT(HDRP(left_buddyp), PACK(csize, 0)); // 왼쪽 버디부터 size만큼 가용 블록으로 변경
            add_free_block(left_buddyp);            // 가용 블록으로 변경된 블록을 free list에 추가
            bp = left_buddyp;
        }
        else
            break;
    }
    return bp;
}

/*
 * mm_init - seglist allocator와 동일
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

/*
 * find_fit : seglist allocator와 동일
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

// seglist allocator와 동일
static void splice_free_block(void *bp) {
    int class = get_class(GET_SIZE(HDRP(bp)));
    if (bp == GET_ROOT(class)) {
        GET_ROOT(class) = GET_SUCC(GET_ROOT(class));
        return;
    }
    
    GET_SUCC(GET_PRED(bp)) = GET_SUCC(bp);
    if (GET_SUCC(bp) != NULL) 
        GET_PRED(GET_SUCC(bp)) = GET_PRED(bp);
}

// seglist allocator와 동일
static void add_free_block(void *bp) {
    int class = get_class(GET_SIZE(HDRP(bp)));
    
    GET_SUCC(bp) = GET_ROOT(class);
    if (GET_ROOT(class) != NULL)
        GET_PRED(GET_ROOT(class)) = bp;
    GET_ROOT(class) = bp;
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
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));

    return coalesce(bp);
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