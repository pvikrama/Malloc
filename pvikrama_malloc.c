/*
 * mm.c
 * Name: Pradeep Kumar. V 
 * ID: pvikrama@andrew.cmu.edu
 * Description: 
 * I have implemented a malloc function using segregated lists
 * The segregated list was implemented using circular doubly linked lists
 * The first fit search algorithm was used to locate free blocks
 * The footers have been removed from the allocated blocks
 * When a new free block is created, it is placed in the list using LIFO policy
 * The list sizes chosen are:
 * 1) 16-31
 * 2) 32-63
 * 3) 64-127
 * 4) 128-255
 * 5) 256-511
 * 6) 512-1023
 * 7) 1023-2047
 * 8) 2048-4095
 * 9) >=4096
 */

#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include "mm.h"
#include "memlib.h"

#ifdef DEBUG
# define dbg_printf(...) printf(__VA_ARGS__)
#else
# define dbg_printf(...)
#endif

#ifdef DRIVER
/* create aliases for driver tests */
#define malloc mm_malloc
#define free mm_free
#define realloc mm_realloc
#define calloc mm_calloc
#endif /* def DRIVER */

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(p) (((size_t)(p) + (ALIGNMENT-1)) & ~0x7)


static char *heap_listp = 0;
static char *heapstart;
static char *root;
static char *epilogueaddr;

/* Function prototypes for internal helper routines */
static void *extend_heap(size_t words);
static void place(void *bp,size_t asize);
static void *find_fit(size_t asize);
static void *coalesce(void *bp);
size_t listno(size_t asize);
static void print_block(void *bp);

#define WSIZE 4
#define DSIZE 8
#define maxlist 8
#define CHUNKSIZE (1<<9)

#define MAX(x, y) ((x) > (y) ? (x) : (y))
#define PACK(size , prev_alloc,  alloc) ((size) | (prev_alloc) | (alloc))
/* Sets the prev_alloc bit indicating that previous block is allocated */
#define SET_PREV_ALLOC(p) (PUT(p,(GET(p)+2)))
/* Resets the prev_alloc bit indicating that previous block is free */
#define RESET_PREV_ALLOC(p) (PUT(p,GET(p)-2))
/* Gets information as to whether the previous block is allocated or not */
#define GET_PREV_ALLOC(p) (GET(p) & 0x2);

#define GET(p)		(*(unsigned int *)(p))              
#define PUT(p, val) (*(unsigned int *)(p) = (val))      

#define GET_SIZE(p) (GET(p) & ~0x7)
#define GET_ALLOC(p)(GET(p) & 0x1)

#define HDRP(bp) ((char *)(bp) - WSIZE)
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

/* Returns address of the next free block in the free list */
#define NEXT_FREE_BLKP(bp) ((*(unsigned int *)(bp))+ heapstart)
/* Returns address of the previous free block in the free list */
#define PREV_FREE_BLKP(bp) ((*(unsigned int *)((char *)(bp) + WSIZE))+heapstart)
/* Returns address of next pointer of current block */
#define CURRENT_NEXT_POINTER(bp) (bp)
/* Returns address of previous pointer of current block */
#define CURRENT_PREV_POINTER(bp) ((char *)(bp) + WSIZE)

/*
 * Initialize: return -1 on error, 0 on success.i
 */
int mm_init(void) {
	if((heap_listp = mem_sbrk(22*WSIZE)) == (void *)-1)
		return -1;

	heapstart = mem_heap_lo();
	int offset = 16;
	root=heap_listp + 8;

	/* Padding for 8-byte alignment */
	PUT(heap_listp,0);

	/* The root block's header is used as prologue
	 * Hence, its allocated bit is set to avoid boundary conditions
	 */
	PUT(heap_listp + WSIZE, PACK(80,2, 1));

	/* Storing the next/prev pointers of the root nodes of the 9 lists 
	 * The lists are arranged in ascending order of sizes
	 */
	
	PUT(heap_listp + 8, (long)(root)- (long)(heapstart));
	PUT(heap_listp + 12, (long)(root)- (long)(heapstart));
	
	while(offset != 80)
	{
		PUT(heap_listp+offset, (long)(heap_listp+offset)-(long)(heapstart));
		PUT(heap_listp+offset+4, (long)(heap_listp+offset)-(long)(heapstart));
		offset = offset+8;
	}

	PUT(heap_listp + 80, PACK(80,2, 1));

	/* Epilogue blocks allocated bit is set to 1 to avoid boundary conditions
	 * The size is 0, to differentiate it from other blocks
	 * The prev_alloc bit is set to 1, which indicates root always allocated
	 */
	PUT(heap_listp + 84, PACK(0,2, 1)); 

	if(extend_heap(CHUNKSIZE/WSIZE) == NULL)
		return -1;
	return 0;
}

/*
 * Extend_Heap
 */
static void *extend_heap(size_t words)
{
	char *bp;
	size_t size;

	/* Allocate an even number of words to maintain alignement */
	size = (words % 2) ? (words+1) * WSIZE : words * WSIZE;
	if ((long)(bp = mem_sbrk(size)) == -1)
		return NULL;
	size_t previous = GET_PREV_ALLOC(HDRP(bp));

	/* Initialize free block header/footer and the epilogue header */
	PUT(HDRP(bp), PACK(size,previous, 0));
	PUT(FTRP(bp), size);
	epilogueaddr = HDRP(NEXT_BLKP(bp));
	PUT(HDRP(NEXT_BLKP(bp)), PACK(0,2,1));

	/* Coalesce if the previous block was free */
	return coalesce(bp);
}

/*
 * malloc
 */
void *malloc (size_t size) {
	size_t asize;
	size_t extendsize;
	char *bp;

	/* Ignore spurious requests */
	if(size <= 0)
		return NULL;

	/* Adjust block size to include alignment and overhead requirements */
	if(size <= 12)
		asize = 16;
	else
		asize = DSIZE * ((size +4 + (DSIZE - 1))/DSIZE);

	if((bp = find_fit(asize))!=NULL)
	{
		place(bp,asize);
		return bp;
	}

	/* No fit found get more memory and place the block */
	extendsize = MAX(asize,CHUNKSIZE);
	if((bp=extend_heap(extendsize/WSIZE))==NULL)
		return NULL;
	place(bp,asize);
	return bp;
}

/*
 * free
 */
void free (void *bp) 
{
	/*Ignore spurious request*/
	if(bp==0)
		return;

	size_t size = GET_SIZE(HDRP(bp));
	size_t previous = GET_PREV_ALLOC(HDRP(bp));

	/*Set the allocated bit to zero*/
	PUT(HDRP(bp), PACK(size,previous,0));
	PUT(FTRP(bp), size);
	coalesce(bp);
}

/*
 * find_fit
 */
static void *find_fit(size_t asize)
{
	void *bp,*bpouter;
	size_t list = listno(asize);

	if(list >=maxlist)
		list=maxlist;
	char *startlist;
	/*Startlist denotes the root pointer of that list*/
	startlist = root + 8*list;

	/* First fit search 
	 * Outer loop iterates through the root node of each list
	 * Inner loop goes through free blocks of that particular list
	 */
	for(bpouter=startlist;bpouter != root + 72;bpouter = (char *)(bpouter) + 8)
	{
		for(bp=NEXT_FREE_BLKP(bpouter);bp != bpouter ;bp=NEXT_FREE_BLKP(bp))
		{	
			if(!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp))))
				return bp;
		}
	}

	/* If no match found return NULL */
	return NULL;
}

/*
 * place
 */
static void place(void *bp, size_t asize)
{
	size_t csize = GET_SIZE(HDRP(bp));
	size_t list;
	size_t previous = GET_PREV_ALLOC(HDRP(bp));
	/*splitting has to happen*/
	if((csize - asize) >= 16)
	{
		/* Remove the current block from its free list */
		PUT(CURRENT_PREV_POINTER(NEXT_FREE_BLKP(bp)),
				GET(CURRENT_PREV_POINTER(bp)));
		PUT(CURRENT_NEXT_POINTER(PREV_FREE_BLKP(bp)),
				GET(CURRENT_NEXT_POINTER(bp)));

		/*The allocated bit is set to 1*/
		PUT(HDRP(bp), PACK(asize,previous, 1));
		bp= NEXT_BLKP(bp);	

		/* The remainder of the free block is made into a new free block */
		PUT(HDRP(bp), PACK(csize-asize,2,0));
		PUT(FTRP(bp), csize-asize);

		/* Call listno to find the list number in which this split block should 
		 * be put and insert it right after the root node of that list
		 */
		list = listno(csize - asize);
		if(list >=maxlist)
			list=maxlist;
		PUT(CURRENT_NEXT_POINTER(bp),GET(CURRENT_NEXT_POINTER(root + 8*list)));
		PUT(CURRENT_PREV_POINTER(bp),
				GET(CURRENT_PREV_POINTER(NEXT_FREE_BLKP(bp))));
		PUT(CURRENT_NEXT_POINTER(root + 8*list),(long)bp-(long)heapstart);
		PUT(CURRENT_PREV_POINTER(NEXT_FREE_BLKP(bp)),(long)bp-(long)heapstart);
	}
	/* No splitting */
	else
	{
		/* Remove the current block from its free list */
		PUT(CURRENT_PREV_POINTER(NEXT_FREE_BLKP(bp)),
				GET(CURRENT_PREV_POINTER(bp)));
		PUT(CURRENT_NEXT_POINTER(PREV_FREE_BLKP(bp)),
				GET(CURRENT_NEXT_POINTER(bp)));

		/* Set the allocated bit of current block */
		PUT(HDRP(bp), PACK(csize,previous,1));

		/* Set the prev_alloc bit of next block */
		SET_PREV_ALLOC(HDRP(NEXT_BLKP(bp)));
	}
}

/*
 * realloc - you may want to look at mm-naive.c
 */

void *mm_realloc(void *ptr, size_t size)
{
	size_t oldsize;
	void *newptr;

	/* If size == 0 then this is just free, and we return NULL. */
	if(size == 0) {
		mm_free(ptr);
		return 0;
	}

	/* If oldptr is NULL, then this is just malloc. */
	if(ptr == NULL) {
		return mm_malloc(size);
	}

	newptr = mm_malloc(size);

	/* If realloc() fails the original block is left untouched  */
	if(!newptr) {
		return 0;
	}

	/* Copy the old data. */
	oldsize = GET_SIZE(HDRP(ptr));
	if(size < oldsize) oldsize = size;
	memcpy(newptr, ptr, oldsize);

	/* Free the old block. */
	mm_free(ptr);

	return newptr;
}

/*
 * Coalesce
 */
static void* coalesce(void *bp)
{
	size_t prev_alloc = GET_PREV_ALLOC(HDRP(bp));
	size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
	size_t size = GET_SIZE(HDRP(bp));
	size_t list;

	/* If previous and next blocks are both allocated */
	if(prev_alloc && next_alloc)
	{
		/* Find the list number in which the block belongs and put it right 
		 * after the root node for that list
		 */
		list = listno(size);

		if(list >=maxlist)
			list=maxlist;
		PUT(CURRENT_NEXT_POINTER(bp),GET(CURRENT_NEXT_POINTER(root+ 8*list)));
		PUT(CURRENT_PREV_POINTER(bp),
				GET(CURRENT_PREV_POINTER(NEXT_FREE_BLKP(bp))));
		PUT(CURRENT_NEXT_POINTER(root + 8*list),(long)bp-(long)heapstart);
		PUT(CURRENT_PREV_POINTER(NEXT_FREE_BLKP(bp)),(long)bp-(long)heapstart);
		RESET_PREV_ALLOC(HDRP(NEXT_BLKP(bp)));
		return bp;
	}

	/* If only previous block is allocated */
	else if(prev_alloc && !next_alloc)
	{
		size += GET_SIZE(HDRP(NEXT_BLKP(bp)));

		list = listno(size);

		if(list >=maxlist)
			list=maxlist;
		/* Remove the next block from its free list */
		PUT(CURRENT_PREV_POINTER(NEXT_FREE_BLKP(NEXT_BLKP(bp))),
				GET(CURRENT_PREV_POINTER(NEXT_BLKP(bp))));
		PUT(CURRENT_NEXT_POINTER(PREV_FREE_BLKP(NEXT_BLKP(bp))),
				GET(CURRENT_NEXT_POINTER(NEXT_BLKP(bp))));

		/* Coalesce the current and next block*/
		PUT(HDRP(bp), PACK(size,prev_alloc,0));
		PUT(FTRP(bp), size);

		/* Put the newly coalesced block in front of the appropriate root node
		 * depending on its size
		 */
		PUT(CURRENT_NEXT_POINTER(bp),GET(CURRENT_NEXT_POINTER(root+ 8*list)));
		PUT(CURRENT_PREV_POINTER(bp),
				GET(CURRENT_PREV_POINTER(NEXT_FREE_BLKP(bp))));
		PUT(CURRENT_NEXT_POINTER(root+ 8*list),(long)bp-(long)heapstart);
		PUT(CURRENT_PREV_POINTER(NEXT_FREE_BLKP(bp)),(long)bp-(long)heapstart);
		return(bp);
	}

	/* If only next block is allocated */
	else if(!prev_alloc && next_alloc)
	{
		size+= GET_SIZE(HDRP(PREV_BLKP(bp)));
		size_t previous = GET_PREV_ALLOC(HDRP(PREV_BLKP(bp)));
		list = listno(size);

		if(list >=maxlist)
			list=maxlist;

		/* Remove the prev block from its free list */
		PUT(CURRENT_PREV_POINTER(NEXT_FREE_BLKP(PREV_BLKP(bp))),
				GET(CURRENT_PREV_POINTER(PREV_BLKP(bp))));
		PUT(CURRENT_NEXT_POINTER(PREV_FREE_BLKP(PREV_BLKP(bp))),
				GET(CURRENT_NEXT_POINTER(PREV_BLKP(bp))));


		/* Coalesce the current and prev block */
		PUT(FTRP(bp), size);
		PUT(HDRP(PREV_BLKP(bp)),PACK(size,previous,0));
		RESET_PREV_ALLOC(HDRP(NEXT_BLKP(PREV_BLKP(bp))));

		/* Put the newly coalesced block in front of the appropriate root node
		 * depending on its size
		 */
		PUT(CURRENT_NEXT_POINTER(PREV_BLKP(bp)),
				GET(CURRENT_NEXT_POINTER(root+ 8*list)));
		PUT(CURRENT_PREV_POINTER(PREV_BLKP(bp)),
				GET(CURRENT_PREV_POINTER(NEXT_FREE_BLKP(PREV_BLKP(bp)))));
		PUT(CURRENT_NEXT_POINTER(root+ 8*list),
				(long)(PREV_BLKP(bp))-(long)heapstart);
		PUT(CURRENT_PREV_POINTER(NEXT_FREE_BLKP(PREV_BLKP(bp))),
				(long)(PREV_BLKP(bp))-(long)heapstart);

		return(PREV_BLKP(bp));
	}

	/* If prev and next blocks both are free */
	else 
	{
		size+= GET_SIZE(HDRP(PREV_BLKP(bp)))+GET_SIZE(FTRP(NEXT_BLKP(bp)));
		size_t previous = GET_PREV_ALLOC(HDRP(PREV_BLKP(bp)));
		list = listno(size);

		if(list >=maxlist)
			list=maxlist;
		/* Remove the next block from its free list */
		PUT(CURRENT_PREV_POINTER(NEXT_FREE_BLKP(NEXT_BLKP(bp))),
				GET(CURRENT_PREV_POINTER(NEXT_BLKP(bp))));
		PUT(CURRENT_NEXT_POINTER(PREV_FREE_BLKP(NEXT_BLKP(bp))),
				GET(CURRENT_NEXT_POINTER(NEXT_BLKP(bp))));

		/* Remove the previous block from its free list */
		PUT(CURRENT_PREV_POINTER(NEXT_FREE_BLKP(PREV_BLKP(bp))),
				GET(CURRENT_PREV_POINTER(PREV_BLKP(bp))));
		PUT(CURRENT_NEXT_POINTER(PREV_FREE_BLKP(PREV_BLKP(bp))),
				GET(CURRENT_NEXT_POINTER(PREV_BLKP(bp))));

		/* Coalesce the current, prev and next block */
		PUT(HDRP(PREV_BLKP(bp)),PACK(size,previous,0));
		PUT(FTRP(NEXT_BLKP(bp)),size);

		/* Put the newly coalesced block in front of the appropriate root node
		 * depending on its size
		 */
		PUT(CURRENT_NEXT_POINTER(PREV_BLKP(bp)),
				GET(CURRENT_NEXT_POINTER(root+ 8*list)));
		PUT(CURRENT_PREV_POINTER(PREV_BLKP(bp)),
				GET(CURRENT_PREV_POINTER(NEXT_FREE_BLKP(PREV_BLKP(bp)))));
		PUT(CURRENT_NEXT_POINTER(root+ 8*list),
				(long)(PREV_BLKP(bp))-(long)heapstart);
		PUT(CURRENT_PREV_POINTER(NEXT_FREE_BLKP(PREV_BLKP(bp))),
				(long)(PREV_BLKP(bp))-(long)heapstart);
		return(PREV_BLKP(bp));
	}
}
/*
 * calloc - you may want to look at mm-naive.c
 * This function is not tested by mdriver, but it is
 * needed to run the traces.
 */

void *calloc (size_t nmemb, size_t size)
{
	size_t bytes = nmemb * size;
	void *newptr;

	newptr = malloc(bytes);
	memset(newptr, 0, bytes);

	return newptr;
}

/*
 * listno - Uses the position of the highest set bit as a metric to 
 * calculate the list number. For ex : If highest set bit position = 5, then
 * number lies between 2^(5-1) and (2^5)-1 i.e. 16 and 31
 */
size_t listno(size_t asize)
{
	/* Shift initially by 5 position because first list starts from 16 */
	asize = asize >> 5;
	size_t count=0;
	while(asize!=0)
	{
		asize=asize>>1;
		count=count+1;
	}
	return count;
}

/*
 * Return whether the pointer is in the heap.
 * May be useful for debugging.
 */

static int in_heap(const void *p) {
	return p <= mem_heap_hi() && p >= mem_heap_lo() && p< (void *)epilogueaddr;
}


/*
 * Return whether the pointer is aligned.
 * May be useful for debugging.
 */

static int aligned(const void *p) {
	return (size_t)ALIGN(p) == (size_t)p;
}

/*
 * printf_block : Prints the header and footer information of a block
 */

static void print_block(void *bp)
{
	size_t hsize,halloc,hpalloc,fsize;

	hsize = GET_SIZE(HDRP(bp));
	halloc  = GET_ALLOC(HDRP(bp));
	hpalloc = GET_PREV_ALLOC(HDRP(bp));
	fsize = GET_SIZE(FTRP(bp));

	if(hsize == 0)
	{
		printf("%p: EOL \n", bp);
	}

	/*To not print footer information in allocated blocks */
	if(!halloc)
		printf("%p:FREE:  HEADER[%zu , %c, %c] FOOTER [%zu] \n", bp, hsize, 
				(hpalloc? 'a':'f'),(halloc ? 'a' : 'f'),fsize);
	else
		printf("%p:ALLOCATED:  HEADER[%zu , %c, %c] \n", bp, hsize, 
				(hpalloc?'a':'f'),(halloc ? 'a' : 'f'));
}



/*
 * mm_checkheap
 */
void mm_checkheap(int verbose) {
	int adjacent = 0;
	char *address = heap_listp + 8;
	void *bp,*bpouter;
	char *next,*prev;
	size_t countfreelist=0,countfreeblock=0, minblocksize =16, maxblocksize =32;

	size_t alloc, prev_alloc, size, saved_prev_alloc;
	alloc = GET_ALLOC((HDRP(address)));
	prev_alloc = GET_PREV_ALLOC((HDRP(address)));
	size = GET_SIZE((HDRP(address)));
	saved_prev_alloc = 1 << 1;

	/* Checks if the prologue block is allocated,because if it is not it would 
	 * cause boundary error conditions 
	 */
	if(!GET_ALLOC(heap_listp+4))
		printf("Check Failed: Prologue block not allocated \n");

	/* Checks if the address pointed by epilogue addr is the epilogue block
	 * by first checking if the size=0 and then returning an error if its
	 * not allocated
	 */
	if(!GET_SIZE(epilogueaddr))
	{
		if(!GET_ALLOC(epilogueaddr))	
			printf("Check Failed: Epilogue block is not allocated \n");
	}

	/* Until you reach a block whose size is 0(epliogue) keep iterating*/
	while(size)
	{
		/* Used to check if all the pointers that will be returned by malloc are
		 * 8-byte aligned
		 */
		if(!aligned(address))
			printf("Check Failed: Alignment mismatch \n");

		/* Check heap boundaries */
		if(!in_heap(address))
			printf("The block does not lie in heap range \n");

		if(verbose)
			print_block(address);
		/* Check if the prev_alloc bit in the header of every block
		 * is correct by comparing with alloc bit of previous block
		 */
		if(saved_prev_alloc != prev_alloc)
			printf("Check Failed: prev_allocated bit of header is wrong\n");

		saved_prev_alloc = alloc<<1;

		/* If size is less than minimum block size return error */
		if(size < 16)
			printf("Check Failed: Block size less than min allowed size(16)\n");


		if(!alloc)
		{
			/* Countfreeblock: Used to keep track of number of free blocks */
			countfreeblock = countfreeblock + 1;

			/* Check the header and footer only if its a free block and return 
			 * error if there is a mismatch
			 */
			if(size != GET_SIZE(FTRP(address)))
				printf("Check Failed: The sizes in header " 
						"and footer do not match\n");

			/* Adjacent variable is set when encountering free block and reset 
			 * on allocated block, so on reaching a free block if adjacent is
			 * equal to 1,then prev block is also free, and hence it indicates 
			 * a coalescing error
			 */
			if(adjacent==1)	
				printf("Check Failed: Two adjacent free blocks \n");
			else
				adjacent=adjacent+1;	
		}
		else
			adjacent=0;

		address = NEXT_BLKP(address);
		alloc = GET_ALLOC((HDRP(address)));
		prev_alloc = GET_PREV_ALLOC((HDRP(address)));
		size = GET_SIZE((HDRP(address)));
	}

	/* Check each block in free list iteratively starting from first block
	 * in first list 
	 */
	for(bpouter=heap_listp + 8;bpouter != root+72;bpouter =(char *)(bpouter)+8)
	{
		for(bp=NEXT_FREE_BLKP(bpouter);bp != bpouter ;bp=NEXT_FREE_BLKP(bp))
		{	
			countfreelist= countfreelist + 1;
			size = GET_SIZE(HDRP(bp));
			next = NEXT_FREE_BLKP(bp);
			prev = PREV_FREE_BLKP(bp);

			/* Check if the next and previous pointers point to location within
			 * allocated heap range
			 */
			if(!in_heap(next))
				printf("Check Failed: Next Pointer Falls out of heap range \n");

			if(!in_heap(prev))
				printf("Check Failed: Prev Pointer Falls out of heap range\n");

			/* Current block's next pointer is next, but now if next's previous 
			 * pointer is no current, then there is pointer mismatch
			 */
			if(PREV_FREE_BLKP(next) != bp)
				printf("Check Failed: Pointer Mismatch \n");

			/* Check if the block size falls within bucket range
			 * But for the last list alone check if the block falls 
			 * within lower limit of bucket ( 4096) and infinity 
			 * (i.e. no upper bound)
			 */
			if(minblocksize < 4096)
			{
				if(size < minblocksize || size >= maxblocksize)
				{
					printf("Check Failed: Block Size does not fall"
							"in bucket range\n");			
				}	
			}
			else
			{
				if(size < minblocksize)
					printf("Check Failed: Block Size does not fall" 
							"in bucket range\n");
			}				
		}
		/*Increasing the bounds of the next bucket*/
		minblocksize = 2 * minblocksize;
		maxblocksize = 2 * maxblocksize;
	}

	/* If number of free block found by iterating through every block
	 * and traversing the free list do not match return error
	 */
	if ( countfreelist != countfreeblock)
		printf("Check Failed: Number of free blocks mismatch \n");
}	



