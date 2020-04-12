/*
 ******************************************************************************
 *                               mm.c                                         *
 *           64-bit struct-based implicit free list memory allocator          *
 *                      without coalesce functionality                        *
 *                 CSE 361: Introduction to Computer Systems                  *
 *                                                                            *
 *  ************************************************************************  *
 *                     insert your documentation here. :)                     *
 *                                                                            *
 *  ************************************************************************  *
 *  ** ADVICE FOR STUDENTS. **                                                *
 *  Step 0: Please read the writeup!                                          *
 *  Step 1: Write your heap checker. Write. Heap. checker.                    *
 *  Step 2: Place your contracts / debugging assert statements.               *
 *  Good luck, and have fun!                                                  *
 *                                                                            *
 ******************************************************************************
 */

/* Do not change the following! */

#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include <stdbool.h>
#include <stddef.h>
#include <assert.h>
#include <stddef.h>

#include "mm.h"
#include "memlib.h"

#ifdef DRIVER
/* create aliases for driver tests */
#define malloc mm_malloc
#define free mm_free
#define realloc mm_realloc
#define calloc mm_calloc
#endif /* def DRIVER */

/* You can change anything from here onward */

/*
 * If DEBUG is defined, enable printing on dbg_printf and contracts.
 * Debugging macros, with names beginning "dbg_" are allowed.
 * You may not define any other macros having arguments.
 */
#define DEBUG // uncomment this line to enable debugging

#ifdef DEBUG
/* When debugging is enabled, these form aliases to useful functions */
#define dbg_printf(...) printf(__VA_ARGS__)
#define dbg_requires(...) assert(__VA_ARGS__)
#define dbg_assert(...) assert(__VA_ARGS__)
#define dbg_ensures(...) assert(__VA_ARGS__)
#else
/* When debugging is disnabled, no code gets generated for these */
#define dbg_printf(...)
#define dbg_requires(...)
#define dbg_assert(...)
#define dbg_ensures(...)
#endif

/* Basic constants */
typedef uint64_t word_t;
static const size_t wsize = sizeof(word_t);   // word and header size (bytes)
static const size_t dsize = 2*sizeof(word_t);       // double word size (bytes)
static const size_t min_block_size = 4*sizeof(word_t); // Minimum block size
static const size_t chunksize = (1 << 12);    // requires (chunksize % 16 == 0)

static const word_t alloc_mask = 0x1;
static const word_t prev_alloc_mask = 0x2;
static const word_t size_mask = ~(word_t)0xF;

// forward declarations
struct block;
typedef struct block block_t;

typedef struct ListNode {
    block_t* next;
    block_t* prev;
} node_t;

typedef union Payload {
    char data[0];
    node_t list_node;
} payload_t;

struct block
{
    /* Header contains size + allocation flag */
    word_t header;
    /*
     * We don't know how big the payload will be.  Declaring it as an
     * array of size 0 allows computing its starting address using
     * pointer notation.
     */
    payload_t payload;
    /*
     * We can't declare the footer as part of the struct, since its starting
     * position is unknown
     */
};


/* Global variables */
/* Pointer to first block */
static block_t *heap_start = NULL;
static block_t *free_ptr = NULL;
static int free_count = 0;

bool mm_checkheap(int lineno);

/* Function prototypes for internal helper routines */
static block_t *extend_heap(size_t size);
static void place(block_t *block, size_t asize);
static block_t *find_fit(size_t asize);
static block_t *coalesce(block_t *block);
static void add_free_block(block_t *block);
static void remove_block(block_t *block);

static size_t max(size_t x, size_t y);
static size_t round_up(size_t size, size_t n);
static word_t pack(size_t size, bool alloc, bool prev_alloc);

static size_t extract_size(word_t header);
static size_t get_size(block_t *block);
static size_t get_payload_size(block_t *block);

static bool extract_alloc(word_t header);
static bool get_alloc(block_t *block);
static bool extract_prev_alloc(word_t header);
static bool get_prev_alloc(block_t *block);

static void write_header(block_t *block, size_t size, bool alloc);
static void write_footer(block_t *block, size_t size, bool alloc);
static void update_prev_alloc(block_t *block, bool prev_alloc);

static block_t *payload_to_header(void *bp);
static void *header_to_payload(block_t *block);

static block_t *find_next(block_t *block);
static block_t *find_next_free(block_t *block);
static word_t *find_prev_footer(block_t *block);
static block_t *find_prev(block_t *block);


/*
 * mm_init: Initializes heap variables and requests chunksize bytes for heap.
 *          returns true if heap was successfully initialized, false otherwise.
 */
bool mm_init(void)
{
    // Create the initial empty heap
    word_t *start = (word_t *)(mem_sbrk(2*wsize));

    if (start == (void *)-1)
    {
        return false;
    }

    // Prologue footer's prev_alloc field does not matter
    start[0] = pack(0, true, false); // Prologue footer
    start[1] = pack(0, true, true); // Epilogue header
    // Heap starts with first "block header", currently the epilogue footer
    heap_start = (block_t *) &(start[1]);

    // Extend the empty heap with a free block of chunksize bytes
    if (extend_heap(chunksize) == NULL)
    {
        return false;
    }

    return true;
}

/*
 * malloc: Allocates new block of at least size bytes. Returns a pointer to the
 *         payload of the newly allocated block.
 */
void *malloc(size_t size)
{
    dbg_requires(mm_checkheap(__LINE__));

    size_t asize;      // Adjusted block size
    size_t extendsize; // Amount to extend heap if no fit is found
    block_t *block;
    void *bp = NULL;

    if (heap_start == NULL) // Initialize heap if it isn't initialized
    {
        mm_init();
    }

    if (size == 0) // Ignore spurious request
    {
        dbg_ensures(mm_checkheap(__LINE__));
        return bp;
    }

    // Adjust block size to include overhead and to meet alignment requirements
    asize = round_up(size + dsize, dsize);

    // Search the free list for a fit
    block = find_fit(asize);

    // If no fit is found, request more memory, and then and place the block
    if (block == NULL)
    {
        extendsize = max(asize, chunksize);
        block = extend_heap(extendsize);
        if (block == NULL) // extend_heap returns an error
        {
            return bp;
        }
    }

    place(block, asize);
    bp = header_to_payload(block);

    dbg_ensures(mm_checkheap(__LINE__));
    return bp;
}

/*
 * free: Frees a given block in the heap. bp is a pointer to the payload of the
 *       block.
 */
void free(void *bp)
{
    if (bp == NULL)
    {
        return;
    }

    block_t *block = payload_to_header(bp);
    size_t size = get_size(block);

    // updating header and writing footer for this block
    write_header(block, size, false);
    write_footer(block, size, false);

    // updating header for next block
    block_t *next_block = find_next(block);
    update_prev_alloc(next_block, false);

    // coalescing incase neighboring blocks are also free
    coalesce(block);
    dbg_ensures(mm_checkheap(__LINE__));
}

/*
 * <what does realloc do?>
 */
void *realloc(void *ptr, size_t size)
{
    block_t *block = payload_to_header(ptr);
    size_t copysize;
    void *newptr;

    // If size == 0, then free block and return NULL
    if (size == 0)
    {
        free(ptr);
        return NULL;
    }

    // If ptr is NULL, then equivalent to malloc
    if (ptr == NULL)
    {
        return malloc(size);
    }

    // Otherwise, proceed with reallocation
    newptr = malloc(size);
    // If malloc fails, the original block is left untouched
    if (newptr == NULL)
    {
        return NULL;
    }

    // Copy the old data
    copysize = get_payload_size(block); // gets size of old payload
    if(size < copysize)
    {
        copysize = size;
    }
    memcpy(newptr, ptr, copysize);

    // Free the old block
    free(ptr);

    return newptr;
}

/*
 * <what does calloc do?>
 */
void *calloc(size_t elements, size_t size)
{
    void *bp;
    size_t asize = elements * size;

    if (asize/elements != size)
    {
        // Multiplication overflowed
        return NULL;
    }

    bp = malloc(asize);
    if (bp == NULL)
    {
        return NULL;
    }
    // Initialize all bits to 0
    memset(bp, 0, asize);

    return bp;
}

/******** The remaining content below are helper and debug routines ********/

/*
 * extend_heap: Extends heap by size bytes. Uses sbrk
 */
static block_t *extend_heap(size_t size)
{
    void *bp;

    // Allocate an even number of words to maintain alignment
    size = round_up(size, dsize);
    if ((bp = mem_sbrk(size)) == (void *)-1)
    {
        return NULL;
    }

    // Initialize free block header/footer
    block_t *block = payload_to_header(bp);
    write_header(block, size, false);
    write_footer(block, size, false);
    // Create new epilogue header
    block_t *block_next = find_next(block);
    write_header(block_next, 0, true);
    update_prev_alloc(block_next, false);

    // adding free block to list
    if(free_ptr)
    {
        add_free_block(block);
        free_ptr=block;
        // ++free_count;
    }
    else
    {
        // initializing free_ptr if its not set
        free_ptr = block;
        free_ptr->payload.list_node.next = block;
        free_ptr->payload.list_node.prev = block;
        // free_count = 1;
    }


    // Coalesce in case the neighboring blocks are free
    return coalesce(block);

}

/*
 * coalesce: Coalesces (and frees) a block with any already free adjacent
 *           blocks. Returns a pointer to the beginning of that block.
 */
static block_t *coalesce(block_t * block)
{
    block_t* new_block = block;
    size_t size = get_size(block);

    // checking next
    block_t* next_block = find_next(block);
    if(!get_alloc(next_block)) {
        size += get_size(next_block);
        remove_block(next_block);
    }

    // checking previous
    if(!get_prev_alloc(block)) {
        word_t* prev_footer = find_prev_footer(block);
        if(!extract_alloc(*prev_footer)) {
            size += extract_size(*prev_footer);
            new_block = find_prev(block);
            remove_block(new_block);
        }
    }

    add_free_block(new_block);
    ++free_count;

    // edge case where the block being updated is the list root
    if(block == free_ptr || (next_block == free_ptr && !get_alloc(next_block)))
    {
        remove_block(free_ptr);
        free_count++;
        free_ptr = new_block;
    }

    write_header(new_block, size, false);
    write_footer(new_block, size, false);


    return new_block;
}

/*
 * place: Places block in heap. Updates headers and footers for blocks
 */
static void place(block_t *block, size_t asize)
{
    size_t csize = get_size(block);
    block_t *block_next; // pointer to next block in memory

    // pointers neighboring free block in the list
    block_t *free_prev = block->payload.list_node.prev;
    block_t *free_next = block->payload.list_node.next;

    // if we can split the block
    if ((csize - asize) >= min_block_size)
    {
        write_header(block, asize, true);
        // clearing old footer
        *(word_t*)((char*)block+get_size(block)) = 0;

        // the new block split must be free
        block_next = find_next(block);
        write_header(block_next, csize-asize, false);
        write_footer(block_next, csize-asize, false);
        update_prev_alloc(block_next, true);

        //------updating pointers given new block-------
        free_ptr = block_next;
        // updating neighboring pointers
        free_prev->payload.list_node.next = block_next;
        free_next->payload.list_node.prev = block_next;
        // writing new pointers to new block
        if(free_next == block)
            block_next->payload.list_node.next = block_next;
        else
            block_next->payload.list_node.next = free_next;

        if(free_next == block)
            block_next->payload.list_node.prev = block_next;
        else
            block_next->payload.list_node.prev = free_prev;

    }
    else
    {
        // writing new header
        write_header(block, csize, true);

        block_next = find_next(block);
        update_prev_alloc(block_next, true);

        // removing block from list
        remove_block(block);
        free_prev = find_next_free(block);
    }
}

/*
 * find_fit: Given a size in bytes, finds a block in the heap that is large
 *           enough to fit the data. Returns a pointer to the block, or NULL if
 *           no block can fit the data.
 */
static block_t *find_fit(size_t asize)
{
    int i;
    block_t *block = free_ptr;
    // block_t *last_block = free_ptr->payload.list_node.prev;

    for (i=0; i<free_count; ++i)
    {
        if (asize <= get_size(block))
        {
            // free_ptr = block; // updating free_ptr for next_fit policy
            return block;
        }
        block = find_next_free(block);
    }
    return NULL; // no fit found
}

/*
 * add_free_block: adds free block to the explicit list using a LIFO policy.
 */
static void add_free_block(block_t *block) {
    block->payload.list_node.prev = free_ptr;
    block->payload.list_node.next = free_ptr->payload.list_node.next;
    free_ptr->payload.list_node.next->payload.list_node.prev = block;
    free_ptr->payload.list_node.next = block;
    if(free_ptr == free_ptr->payload.list_node.prev)
        free_ptr->payload.list_node.prev = block;
}

/*
 * remove_block: removes block from the list and updates the neighboring nodes
 *               accordingly. This method only unlinks pointers, and does not
 *               overwrite them in memory.
 */
static void remove_block(block_t *block)
{
    block_t* next_blk = block->payload.list_node.next;
    block_t* prev_blk = block->payload.list_node.prev;

    next_blk->payload.list_node.prev = prev_blk;
    prev_blk->payload.list_node.next = next_blk;
    --free_count;
}

/*
 * <what does your heap checker do?>
 * Please keep modularity in mind when you're writing the heap checker!
 */
bool mm_checkheap(int line)
{
    // iterating over the entire heap
    block_t* cur_block;
    bool freed = false;
    bool prev_alloc = true;
    for(cur_block=heap_start; get_size(cur_block) > 0;
        cur_block=find_next(cur_block))
    {
        // checking prev_alloc bit
        if(get_prev_alloc(cur_block) != prev_alloc)
        {
            printf("Prev_alloc bit in block %p don't match allocation in "
                   "previous block. Called at line %i.\n", cur_block, line);
            return false;
        }
        prev_alloc = get_alloc(cur_block);

        // checking for two contiguous free block
        if(freed && !get_alloc(cur_block))
        {
            printf("Two consecutive free blocks %p. Called at line %i.\n",
                    cur_block, line);
            return false;
        }

        // free block specific checks
        freed = !get_alloc(cur_block);
        if(freed)
        {
            // checking if headers and footers match
            word_t* footerp = (word_t *)((cur_block->payload.data) +
                                get_size(cur_block) - dsize);
            if(cur_block->header != *footerp)
            {
                printf("Header and footer do not match for block "
                        "%p. Called at line %i.\n", cur_block, line);
                return false;
            }

            // checking if explicit list pointers are within the heap
            if(cur_block->payload.list_node.next > (block_t*)mem_heap_hi() &&
               cur_block->payload.list_node.prev > (block_t*)mem_heap_hi())
            {
                printf("List nodes for block %p point out of bounds. "
                       "Called at line %i", cur_block, line);
                return false;
            }
        }

        // checking if the blocks are always within range
        if(((char*)cur_block+get_size(cur_block)) > (char*)mem_heap_hi())
        {
            printf("Size of block %p extends past heap range."
                   "Called on line %i", cur_block, line);
            return false;
        }
    }

    return true;
}

/*
 * max: returns x if x > y, and y otherwise.
 */
static size_t max(size_t x, size_t y)
{
    return (x > y) ? x : y;
}

/*
 * round_up: Rounds size up to next multiple of n
 */
static size_t round_up(size_t size, size_t n)
{
    return (n * ((size + (n-1)) / n));
}

/*
 * pack: returns a header reflecting a specified size and its alloc status.
 *       If the block is allocated, the lowest bit is set to 1, and 0 otherwise.
 */
static word_t pack(size_t size, bool alloc, bool prev_alloc)
{
    // return alloc ? (size | alloc_mask) : size;
    return size | alloc | (prev_alloc << 1);
}


/*
 * extract_size: returns the size of a given header value based on the header
 *               specification above.
 */
static size_t extract_size(word_t word)
{
    return (word & size_mask);
}

/*
 * get_size: returns the size of a given block by clearing the lowest 4 bits
 *           (as the heap is 16-byte aligned).
 */
static size_t get_size(block_t *block)
{
    return extract_size(block->header);
}

/*
 * get_payload_size: returns the payload size of a given block, equal to
 *                   the entire block size minus the header and footer sizes.
 */
static word_t get_payload_size(block_t *block)
{
    size_t asize = get_size(block);
    return asize - dsize;
}

/*
 * extract_alloc: returns the allocation status of a given header value based
 *                on the header specification above.
 */
static bool extract_alloc(word_t word)
{
    return (bool)(word & alloc_mask);
}

/*
 * get_alloc: returns true when the block is allocated based on the
 *            block header's lowest bit, and false otherwise.
 */
static bool get_alloc(block_t *block)
{
    return extract_alloc(block->header);
}

/*
 * extract_prev_alloc:
 */
static bool extract_prev_alloc(word_t header)
{
    return (bool)(header & prev_alloc_mask);
}

/*
 * get_prev_alloc:
 */
static bool get_prev_alloc(block_t *block)
{
    return extract_prev_alloc(block->header);
}

/*
 * write_header: given a block and its size and allocation status,
 *               writes an appropriate value to the block header.
 * Note: this method only updates the size and alloc field. It does not effect
 *       the prev_alloc bit at all.
 */
static void write_header(block_t *block, size_t size, bool alloc)
{
    block->header = pack(size, alloc, block->header & prev_alloc_mask);
}

/*
 * write_footer: given a block and its size and allocation status,
 *               writes an appropriate value to the block footer by first
 *               computing the position of the footer.
 * Note: this method only updates the size and alloc field. It does not effect
 *       the prev_alloc bit at all.
 */
static void write_footer(block_t *block, size_t size, bool alloc)
{
    word_t *footerp = (word_t *)((block->payload.data) + get_size(block) - dsize);
    *footerp = pack(size, alloc, (block->header & prev_alloc_mask));
}

/*
 * update_prev_alloc: updates the prev_alloc bit in both header and footer for
 *                    a given block. Only updates footer if the block is free.
 */
static void update_prev_alloc(block_t *block, bool prev_alloc)
{
    // writing prev_alloc for header
    block->header &= ~prev_alloc_mask; // clearing prev_alloc bit
    block->header |= prev_alloc << 1;  // writing the prev_alloc bit

    // writing prev_alloc for footer
    if(!get_alloc(block)) {
        word_t *footerp = (word_t *)((block->payload.data) + get_size(block) - dsize);
        *footerp &= ~prev_alloc_mask;
        *footerp |= prev_alloc << 1;
    }
}

/*
 * find_next: returns the next consecutive block on the heap by adding the
 *            size of the block.
 */
static block_t *find_next(block_t *block)
{
    dbg_requires(block != NULL);
    block_t *block_next = (block_t *)(((char *)block) + get_size(block));

    dbg_ensures(block_next != NULL);
    return block_next;
}

/*
 * find_next_free: returns a pointer to the next free block. This uses the
 *                 explicit list
 */
static block_t *find_next_free(block_t *block)
{
    return block->payload.list_node.next;
}

/*
 * find_prev_footer: returns the footer of the previous block.
 */
static word_t *find_prev_footer(block_t *block)
{
    // Compute previous footer position as one word before the header
    return (&(block->header)) - 1;
}

/*
 * find_prev: returns the previous block position by checking the previous
 *            block's footer and calculating the start of the previous block
 *            based on its size.
 */
static block_t *find_prev(block_t *block)
{
    word_t *footerp = find_prev_footer(block);
    size_t size = extract_size(*footerp);
    return (block_t *)((char *)block - size);
}

/*
 * payload_to_header: given a payload pointer, returns a pointer to the
 *                    corresponding block.
 */
static block_t *payload_to_header(void *bp)
{
    return (block_t *)(((char *)bp) - offsetof(block_t, payload));
}

/*
 * header_to_payload: given a block pointer, returns a pointer to the
 *                    corresponding payload.
 */
static void *header_to_payload(block_t *block)
{
    return (void *)(block->payload.data);
}
