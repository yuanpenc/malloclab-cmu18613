/**
 * @file mm.c
 * @brief A 64-bit struct-based implicit free list memory allocator
 *
 * 15-213: Introduction to Computer Systems
 *
 * TODO: insert your documentation here. :)
 *
 *************************************************************************
 *
 * ADVICE FOR STUDENTS.
 * - Step 0: Please read the writeup!
 * - Step 1: Write your heap checker.
 * - Step 2: Write contracts / debugging assert statements.
 * - Good luck, and have fun!
 *
 *************************************************************************
 *
 * @author Your Name <andrewid@andrew.cmu.edu>
 */

#include <assert.h>
#include <inttypes.h>
#include <stdbool.h>
#include <stddef.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "memlib.h"
#include "mm.h"

/* Do not change the following! */

#ifdef DRIVER
/* create aliases for driver tests */
#define malloc mm_malloc
#define free mm_free
#define realloc mm_realloc
#define calloc mm_calloc
#define memset mem_memset
#define memcpy mem_memcpy
#endif /* def DRIVER */

/* You can change anything from here onward */

/*
 *****************************************************************************
 * If DEBUG is defined (such as when running mdriver-dbg), these macros      *
 * are enabled. You can use them to print debugging output and to check      *
 * contracts only in debug mode.                                             *
 *                                                                           *
 * Only debugging macros with names beginning "dbg_" are allowed.            *
 * You may not define any other macros having arguments.                     *
 *****************************************************************************
 */
#ifdef DEBUG
/* When DEBUG is defined, these form aliases to useful functions */
#define dbg_printf(...) printf(__VA_ARGS__)
#define dbg_requires(expr) assert(expr)
#define dbg_assert(expr) assert(expr)
#define dbg_ensures(expr) assert(expr)
#define dbg_printheap(...) print_heap(__VA_ARGS__)
#else
/* When DEBUG is not defined, no code gets generated for these */
/* The sizeof() hack is used to avoid "unused variable" warnings */
#define dbg_printf(...) (sizeof(__VA_ARGS__), -1)
#define dbg_requires(expr) (sizeof(expr), 1)
#define dbg_assert(expr) (sizeof(expr), 1)
#define dbg_ensures(expr) (sizeof(expr), 1)
#define dbg_printheap(...) ((void)sizeof(__VA_ARGS__))
#endif

/* additional define*/

#define MAX_SEG_LIST_LENGTH 14

/* Basic constants */

typedef uint64_t word_t;

/** @brief Word and header size (bytes) */
static const size_t wsize = sizeof(word_t);

/** @brief Double word size (bytes) */
static const size_t dsize = 2 * wsize;

/** @brief Minimum block size (bytes) */
static const size_t min_block_size = dsize;

/**
 * TODO: explain what chunksize is
 * (Must be divisible by dsize)
 */
static const size_t chunksize = (1 << 12);

/**
 * TODO: explain what alloc_mask is
 */
static const word_t alloc_mask = 0x1;

/**
 * TODO: explain what size_mask is
 */
static const word_t size_mask = ~(word_t)0xF;

/*
New deifined constant
*/

static const word_t pre_alloc_mark = 0x2;

static const word_t pre_min_mark = 0x4;

/** @brief Represents the header and payload of one block in the heap */
typedef struct block {
    /** @brief Header contains size + allocation flag */
    word_t header;
    union {
        struct {
            struct block *next;
            struct block *prev;
        } free_list;
        char payload[0];
    } data;
    /**
     * @brief A pointer to the block payload.
     *
     * TODO: feel free to delete this comment once you've read it carefully.
     * We don't know what the size of the payload will be, so we will declare
     * it as a zero-length array, which is a GCC compiler extension. This will
     * allow us to obtain a pointer to the start of the payload.
     *
     * WARNING: A zero-length array must be the last element in a struct, so
     * there should not be any struct fields after it. For this lab, we will
     * allow you to include a zero-length array in a union, as long as the
     * union is the last field in its containing struct. However, this is
     * compiler-specific behavior and should be avoided in general.
     *
     * WARNING: DO NOT cast this pointer to/from other types! Instead, you
     * should use a union to alias this zero-length array with another struct,
     * in order to store additional types of data in the payload memory.
     */

    /*
     * TODO: delete or replace this comment once you've thought about it.
     * Why can't we declare the block footer here as part of the struct?
     * Why do we even have footers -- will the code work fine without them?
     * which functions actually use the data contained in footers?
     */
} block_t;

/* Global variables */

/** @brief Pointer to first block in the heap */
static block_t *heap_start = NULL;

/** @brief An array keeps pointers point to each free list **/
static block_t *seg_list[MAX_SEG_LIST_LENGTH];

/*
 *****************************************************************************
 * The functions below are short wrapper functions to perform                *
 * bit manipulation, pointer arithmetic, and other helper operations.        *
 *                                                                           *
 * We've given you the function header comments for the functions below      *
 * to help you understand how this baseline code works.                      *
 *                                                                           *
 * Note that these function header comments are short since the functions    *
 * they are describing are short as well; you will need to provide           *
 * adequate details within your header comments for the functions above!     *
 *****************************************************************************
 */

/*
 * ---------------------------------------------------------------------------
 *                        BEGIN SHORT HELPER FUNCTIONS
 * ---------------------------------------------------------------------------
 */

/**
 * @brief Returns the maximum of two integers.
 * @param[in] x
 * @param[in] y
 * @return `x` if `x > y`, and `y` otherwise.
 */
static size_t max(size_t x, size_t y) {
    return (x > y) ? x : y;
}

/**
 * @brief Rounds `size` up to next multiple of n
 * @param[in] size
 * @param[in] n
 * @return The size after rounding up
 */
static size_t round_up(size_t size, size_t n) {
    return n * ((size + (n - 1)) / n);
}

/**
 * @brief Packs the `size` and `alloc` of a block into a word suitable for
 *        use as a packed value.
 *
 * Packed values are used for both headers and footers.
 *
 * The allocation status is packed into the lowest bit of the word.
 *
 * @param[in] size The size of the block being represented
 * @param[in] alloc True if the block is allocated
 * @return The packed value
 */
static word_t pack(size_t size, bool pre_min, bool pre_alloc, bool alloc) {
    word_t word = size;
    if (alloc) {
        word |= alloc_mask;
    }

    if (pre_alloc) {
        word |= pre_alloc_mark;
    }
    if (pre_min) {
        word |= pre_min_mark;
    }

    return word;
}

/**
 * @brief Extracts the size represented in a packed word.
 *
 * This function simply clears the lowest 4 bits of the word, as the heap
 * is 16-byte aligned.
 *
 * @param[in] word
 * @return The size of the block represented by the word
 */
static size_t extract_size(word_t word) {
    return (word & size_mask);
}

/**
 * @brief Extracts the size of a block from its header.
 * @param[in] block
 * @return The size of the block
 */
static size_t get_size(block_t *block) {
    return extract_size(block->header);
}

/**
 * @brief Given a payload pointer, returns a pointer to the corresponding
 *        block.
 * @param[in] bp A pointer to a block's payload
 * @return The corresponding block
 */
static block_t *payload_to_header(void *bp) {
    return (block_t *)((char *)bp - offsetof(block_t, data.payload));
}

/**
 * @brief Given a block pointer, returns a pointer to the corresponding
 *        payload.
 * @param[in] block
 * @return A pointer to the block's payload
 */
static void *header_to_payload(block_t *block) {
    return (void *)(block->data.payload);
}
// CYPTODO: how to handle the datatype of pre and next pointer( word_t* )?
// garble bytes,

/**
 * @brief Given a block pointer, returns a pointer to the corresponding
 *        footer.
 * @param[in] block
 * @return A pointer to the block's footer
 */
static word_t *header_to_footer(block_t *block) {
    return (word_t *)(block->data.payload + get_size(block) - dsize);
}

/**
 * @brief Given a block footer, returns a pointer to the corresponding
 *        header.
 * @param[in] footer A pointer to the block's footer
 * @return A pointer to the start of the block
 */
static block_t *footer_to_header(word_t *footer) {
    size_t size = extract_size(*footer);
    return (block_t *)((char *)footer + wsize - size);
}

/**
 * @brief Returns the payload size of a given block.
 *
 * The payload size is equal to the entire block size minus the sizes of the
 * block's header and footer.
 *
 * @param[in] block
 * @return The size of the block's payload
 */
static size_t get_payload_size(block_t *block) {
    size_t asize = get_size(block);
    return asize - wsize;
}

/**
 * @brief Returns the allocation status of a given header value.
 *
 * This is based on the lowest bit of the header value.
 *
 * @param[in] word
 * @return The allocation status correpsonding to the word
 */
static bool extract_alloc(word_t word) {
    return (bool)(word & alloc_mask);
}

/**
 * @brief Returns the allocation status of a block, based on its header.
 * @param[in] block
 * @return The allocation status of the block
 */
static bool get_alloc(block_t *block) {
    return extract_alloc(block->header);
}

/**
 * @brief Writes an epilogue header at the given address.
 *
 * The epilogue header has size 0, and is marked as allocated.
 *
 * @param[out] block The location to write the epilogue header
 */
static void write_epilogue(block_t *block) {
    dbg_requires(block != NULL);
    dbg_requires((char *)block == mem_heap_hi() - 7);
    block->header = pack(0, false, false, true);
}

/**
 * @brief Writes a block starting at the given address.
 *
 * This function writes both a header and footer, where the location of the
 * footer is computed in relation to the header.
 *
 * TODO: Are there any preconditions or postconditions?
 *
 * @param[out] block The location to begin writing the block header
 * @param[in] size The size of the new block
 * @param[in] alloc The allocation status of the new block
 */

// static void write_block(block_t *block, size_t size, bool alloc) {
//     dbg_requires(block != NULL);
//     dbg_requires(size > 0);
//     block->header = pack(size, alloc);
//     word_t *footerp = header_to_footer(block);
//     *footerp = pack(size, alloc);
// }

/**
 * @brief Finds the next consecutive block on the heap.
 *
 * This function accesses the next block in the "implicit list" of the heap
 * by adding the size of the block.
 *
 * @param[in] block A block in the heap
 * @return The next consecutive block on the heap
 * @pre The block is not the epilogue
 */
// CYPTODO: Would assert cash if dbg_requires(get_size(block) != 0) at position
// of epilogut(size==0)
static block_t *find_next(block_t *block) {
    dbg_requires(block != NULL);
    dbg_requires(get_size(block) != 0);
    return (block_t *)((char *)block + get_size(block));
}

/**
 * @brief Finds the footer of the previous block on the heap.
 * @param[in] block A block in the heap
 * @return The location of the previous block's footer
 */
static word_t *find_prev_footer(block_t *block) {
    // Compute previous footer position as one word before the header
    return &(block->header) - 1;
}

/**
 * @brief Finds the previous consecutive block on the heap.
 *
 * This is the previous block in the "implicit list" of the heap.
 *
 * The position of the previous block is found by reading the previous
 * block's footer to determine its size, then calculating the start of the
 * previous block based on its size.
 *
 * @param[in] block A block in the heap
 * @return The previous consecutive block in the heap
 * @pre The block is not the first block in the heap
 */
static block_t *find_prev(block_t *block) {
    dbg_requires(block != NULL);
    dbg_requires(get_size(block) != 0);
    word_t *footerp = find_prev_footer(block);
    return footer_to_header(footerp);
}

static int find_seg_list_class(size_t size) {
    int seg_list_class;
    size_t class_step = 2 * min_block_size;
    if (size <= min_block_size) {
        seg_list_class = 0;
        return seg_list_class;
    }
    for (seg_list_class = 1; seg_list_class < MAX_SEG_LIST_LENGTH;
         seg_list_class++, class_step <<= 1) {
        if (size <= class_step) {
            return seg_list_class;
        }
    }
    // larger block is placed in the last class
    return MAX_SEG_LIST_LENGTH - 1;
}

/*
new function for last test
*/

static void write_header(block_t *block, size_t size, bool pre_min,
                         bool pre_alloc, bool alloc) {
    dbg_requires(block != NULL);

    block->header = pack(size, pre_min, pre_alloc, alloc);
}

static void write_footer(block_t *block, size_t size, bool pre_min,
                         bool pre_alloc, bool alloc) {
    dbg_requires(block != NULL);

    dbg_requires(get_size(block) == size);
    word_t *footerp = header_to_footer(block);
    *footerp = pack(size, pre_min, pre_alloc, alloc);
}

static bool extract_pre_alloc(word_t word) {
    return (bool)(word & pre_alloc_mark);
}

static bool get_pre_alloc(block_t *block) {
    return extract_pre_alloc(block->header);
}

static bool extract_pre_min(word_t word) {
    return (bool)(word & pre_min_mark);
}

static bool get_pre_min(block_t *block) {
    return extract_pre_min(block->header);
}

static void set_next_block_pre_alloc_pre_min(block_t *block, bool next_pre_min,
                                             bool next_pre_alloc) {
    block_t *block_next = find_next(block);
    size_t size_next = get_size(block_next);
    bool alloc = get_alloc(block_next);
    write_header(block_next, size_next, next_pre_min, next_pre_alloc, alloc);
}

static block_t *find_min_prev(block_t *block) {
    dbg_requires(get_pre_min(block));
    return (block_t *)((char *)block - dsize);
}

/*
 * ---------------------------------------------------------------------------
 *                        END SHORT HELPER FUNCTIONS
 * ---------------------------------------------------------------------------
 */

/******** The remaining content below are helper and debug routines ********/

/**
 * @brief
 *
 * <Insert new free block into free list based on LIFO>
 *
 *
 * @param[in] block
 * @return
 */
static void insert_block_LIFO(block_t *block) {
    // printf("---%d---\n", (int)get_size(block));
    size_t size = get_size(block);
    int class = find_seg_list_class(size);

    if (size == min_block_size) {
        dbg_requires(class == 0);
        if (seg_list[class] == NULL) {
            seg_list[class] = block;
            block->data.free_list.next = NULL;
        } else {
            block->data.free_list.next = seg_list[class];
            seg_list[class] = block;
        }
    }

    else if (size != min_block_size) {
        if (seg_list[class] == NULL) {
            seg_list[class] = block;
            block->data.free_list.prev = NULL;
            block->data.free_list.next = NULL;
        } else {
            // seg_list[class]->data.free_list.prev = NULL;
            seg_list[class]->data.free_list.prev = block;
            block->data.free_list.next = seg_list[class];
            block->data.free_list.prev = NULL;
            seg_list[class] = block;
        }
    }
}

/**
 * @brief
 *
 * <remove the block from the free list and fix the left>
 *
 *
 * @param[in] block
 * @return
 */
static void fix_free_list(block_t *block) {
    dbg_requires(block != NULL);

    size_t size = get_size(block);
    int class = find_seg_list_class(size);

    if (size != min_block_size) {
        block_t *prev = block->data.free_list.prev;
        block_t *nextv = block->data.free_list.next;

        if (prev == NULL) {

            if (nextv != NULL) {
                nextv->data.free_list.prev = NULL;
            }

            seg_list[class] = nextv;
        } else {
            if (nextv != NULL) {
                nextv->data.free_list.prev = prev;
            }
            prev->data.free_list.next = nextv;
        }

        // Initialize the free block
        block->data.free_list.next = NULL;
        block->data.free_list.prev = NULL;
    } else {
        block_t *nextv = block->data.free_list.next;
        block_t *prev = NULL;
        block_t *temp = seg_list[class];
        dbg_requires(seg_list[class] != NULL);
        while (temp != NULL) {
            if (temp->data.free_list.next == block) {
                prev = temp;
            }
            temp = temp->data.free_list.next;
        }
        if (prev != NULL) {
            prev->data.free_list.next = nextv;
        } else {
            seg_list[class] = nextv;
        }
    }
}

/**
 * @brief
 *
 * <What does this function do?>
 * <What are the function's arguments?>
 * <What is the function's return value?>
 * <Are there any preconditions or postconditions?>
 *
 * @param[in] block
 * @return
 */
static block_t *coalesce_block(block_t *block) {

    // CYPTODO: make sure each block has pre and next already set up? not
    // necessary I think.

    dbg_requires(block != NULL);
    // dbg_requires(block->data.free_list.next == NULL);
    // dbg_requires(block->data.free_list.prev == NULL);

    dbg_requires(!get_alloc(block));

    bool pre_flag;
    bool next_flag;

    pre_flag = get_pre_alloc(block);
    next_flag = get_alloc(find_next(block));
    size_t size = get_size(block);

    block_t *next_block = find_next(block);
    block_t *pre_block = NULL;

    if (pre_flag == 0) {
        if (get_pre_min(block)) {
            pre_block = find_min_prev(block);
        } else {
            pre_block = find_prev(block);
        }
    }

    // case 1
    if (pre_flag && next_flag) {
        // printf("%zu",size);
        if (size == min_block_size) {
            set_next_block_pre_alloc_pre_min(block, true, false);
        } else if (size > min_block_size) {
            set_next_block_pre_alloc_pre_min(block, false, false);
        }

    }
    // case 2
    else if (pre_flag == 1 && next_flag == 0) {

        fix_free_list(next_block);
        bool pre_min = get_pre_min(block);
        size += get_size(next_block);
        // write_block(block, size, false);
        write_header(block, size, pre_min, pre_flag, false);
        write_footer(block, size, pre_min, pre_flag, false);
        set_next_block_pre_alloc_pre_min(block, false, false);
    }
    // case 3
    else if (pre_flag == 0 && next_flag == 1) {
        dbg_requires(pre_block != block);

        fix_free_list(pre_block);
        // write_block(find_prev(block), size, false);
        bool pre_min = get_pre_min(pre_block);
        size += get_size(pre_block);
        write_header(pre_block, size, pre_min, true, false);
        write_footer(pre_block, size, pre_min, true, false);
        set_next_block_pre_alloc_pre_min(pre_block, false, false);

        block = pre_block;
    }
    // case 4
    else if (pre_flag == 0 && next_flag == 0) {
        dbg_requires(pre_block != block);

        fix_free_list(pre_block);
        fix_free_list(next_block);
        // write_block(find_prev(block), size, false);
        bool pre_min = get_pre_min(pre_block);
        size = size + get_size(pre_block) + get_size(next_block);
        write_header(pre_block, size, pre_min, true, false);
        write_footer(pre_block, size, pre_min, true, false);
        set_next_block_pre_alloc_pre_min(pre_block, false, false);

        block = pre_block;
    }
    // printf("dbg---checker---2\n");
    insert_block_LIFO(block);

    return block;
}

/**
 * @brief
 *
 * <What does this function do?>
 * <What are the function's arguments?>
 * <What is the function's return value?>
 * <Are there any preconditions or postconditions?>
 *
 * @param[in] size
 * @return
 */
static block_t *extend_heap(size_t size) {
    void *bp;

    // Allocate an even number of words to maintain alignment
    size = round_up(size, dsize);
    if ((bp = mem_sbrk(size)) == (void *)-1) {
        return NULL;
    }

    // Initialize free block header/footer
    block_t *block = payload_to_header(bp);
    // write_block(block, size, false);
    bool pre_min = get_pre_min(block);
    bool pre_alloc = get_pre_alloc(block);
    write_header(block, size, pre_min, pre_alloc, false);
    write_footer(block, size, pre_min, pre_alloc, false);

    // Initialize pre_pointer and next_pointer
    // block->data.free_list.next = NULL;
    // block->data.free_list.prev = NULL;

    // Create new epilogue header
    block_t *block_next = find_next(block);
    write_epilogue(block_next);

    // Coalesce in case the previous block was free
    block = coalesce_block(block);

    return block;
}

/**
 * @brief
 *
 * <What does this function do?>
 * <What are the function's arguments?>
 * <What is the function's return value?>
 * <Are there any preconditions or postconditions?>
 *
 * @param[in] block
 * @param[in] asize
 */
static void split_block(block_t *block, size_t asize) {
    dbg_requires(!get_alloc(block));
    /* TODO: Can you write a precondition about the value of asize? */

    size_t block_size = get_size(block);
    dbg_requires(block_size >= asize);

    fix_free_list(block);

    if ((block_size - asize) >= min_block_size) {
        block_t *block_next;
        // write_block(block, asize, true);
        bool pre_min = get_pre_min(block);
        write_header(block, asize, pre_min, true, true);
        bool next_pre_min;
        if (asize == min_block_size) {
            next_pre_min = true;
        } else {
            next_pre_min = false;
        }

        block_next = find_next(block);
        // write_block(block_next, block_size - asize, false);

        write_header(block_next, block_size - asize, next_pre_min, true, false);
        // printf("block alloc %d\n",get_alloc(block_next));
        write_footer(block_next, block_size - asize, next_pre_min, true, false);
        // block_next->data.free_list.next = NULL;
        // block_next->data.free_list.prev = NULL;
        // printf("block alloc %d\n",get_alloc(block_next));
        bool next_next_pre_min;
        if ((block_size - asize) != min_block_size) {
            next_next_pre_min = false;
        } else {
            next_next_pre_min = true;
        }
        set_next_block_pre_alloc_pre_min(block_next, next_next_pre_min, false);

        coalesce_block(block_next);
        // CYPTODO: make sure you can insert new block, which diffs from the
        // book
    } else {
        bool pre_min = get_pre_min(block);
        write_header(block, block_size, pre_min, true, true);

        bool next_pre_min = get_pre_min(find_next(block));
        set_next_block_pre_alloc_pre_min(block, next_pre_min, true);
    }

    dbg_ensures(get_alloc(block));
}

/**
 * @brief
 *
 * <What does this function do?>
 * <What are the function's arguments?>
 * <What is the function's return value?>
 * <Are there any preconditions or postconditions?>
 *
 * @param[in] asize
 * @return
 */
static block_t *find_fit(size_t asize) {
    // block_t *block;

    // for (block = heap_start; get_size(block) > 0; block = find_next(block)) {

    //     if (!(get_alloc(block)) && (asize <= get_size(block))) {
    //         return block;
    //     }
    // }
    // return NULL; // no fit found

    block_t *class_root;
    int class = find_seg_list_class(asize);

    while (class < MAX_SEG_LIST_LENGTH) {
        class_root = seg_list[class];
        while (class_root != NULL) {
            size_t size = get_size(class_root);

            if (size >= asize) {
                return class_root;
            }
            class_root = class_root->data.free_list.next;
        }
        class ++;
    }
    return NULL;
}

// void print_block(block_t block){

// }

/**
 * @brief
 *
 * <What does this function do?>
 * <What are the function's arguments?>
 * <What is the function's return value?>
 * <Are there any preconditions or postconditions?>
 *
 * @param[in] line
 * @return
 */
bool mm_checkheap(int line) {
    /*
     * TODO: Delete this comment!
     *
     * You will need to write the heap checker yourself.
     * Please keep modularity in mind when you're writing the heap checker!
     *
     * As a filler: one guacamole is equal to 6.02214086 x 10**23 guacas.
     * One might even call it...  the avocado's number.
     *
     * Internal use only: If you mix guacamole on your bibimbap,
     * do you eat it with a pair of chopsticks, or with a spoon?
     */

    // heap level

    word_t prologue_footer;
    block_t *block = heap_start;
    prologue_footer = *(find_prev_footer(heap_start));

    // printf("Heap (%p):\n", heap_start);
    // prologue
    if (extract_size(prologue_footer) != 0 ||
        extract_alloc(prologue_footer) != 1) {
        printf("###############################################################"
               "####\n");
        printf("Bad prologue footer\n");
        printf("###############################################################"
               "####\n");
        return false;
    }

    // check each block
    bool pre_alloc_flag = 1;
    for (block = heap_start; get_size(block) > 0; block = find_next(block)) {

        // if(line) print_block(block);
        size_t size = get_size(block);
        if ((size % dsize) != 0) {
            printf("###########################################################"
                   "########\n");
            printf("Error: %p is not doubleword aligned\n", block);
            printf("###########################################################"
                   "########\n");
            return false;
        }

        if (get_size(block) != min_block_size) {
            if (!get_alloc(block)) {
                size_t footer_size = extract_size(*(header_to_footer(block)));

                if (size != footer_size ||
                    (get_alloc(block) !=
                     extract_alloc(*(header_to_footer(block))))) {
                    printf("###################################################"
                           "########"
                           "########\n");
                    printf("Error: header does not match footer\n");
                    printf("###################################################"
                           "########"
                           "########\n");
                    return false;
                }
            }
        }

        // check no free blocks are consecutive

        if (get_alloc(block) == 0 && pre_alloc_flag == 0) {
            printf("###########################################################"
                   "########\n");
            printf("Error: free blocks are consecutive\n");
            printf("###########################################################"
                   "########\n");
            return false;
        }
        pre_alloc_flag = get_alloc(block);
    }
    // epilogue
    if (extract_size(block->header) != 0 || extract_alloc(block->header) != 1) {
        printf("###############################################################"
               "####\n");
        printf("Bad epilogue header\n");
        printf("size=%lu\n", extract_size(block->header));
        printf("alloc=%d\n", extract_alloc(block->header));
        // CYPTODO: mem_heap_hi() 与epligue关系，而且还可能有错
        printf("%p\n", mem_heap_hi());
        printf("%p\n", block);
        printf("###############################################################"
               "####\n");
        return false;
    }

    // check pointer
    //<=16

    block_t *temp_16 = seg_list[0];
    while (temp_16 != NULL) {
        if (temp_16->data.free_list.next != NULL) {
            if (temp_16->data.free_list.next > (block_t *)mem_heap_hi() ||
                temp_16->data.free_list.next < (block_t *)mem_heap_lo()) {
                printf("#######################################################"
                       "############\n");
                printf("blocks next pointer out of heap range\n");
                printf("class number=0\n");
                printf("#######################################################"
                       "############\n");
            }
        }
        temp_16 = temp_16->data.free_list.next;
    }

    // 17~....
    for (int class = 1; class < MAX_SEG_LIST_LENGTH; class ++) {
        block_t *temp = seg_list[class];
        while (temp != NULL) {
            if (temp->data.free_list.prev != NULL) {
                if (temp->data.free_list.prev > (block_t *)mem_heap_hi() ||
                    temp->data.free_list.prev < (block_t *)mem_heap_lo()) {
                    printf("###################################################"
                           "####"
                           "############\n");
                    printf("blocks previous pointer out of heap range\n");
                    printf("block=%p\n", temp);
                    printf("block _ previous = %p\n",
                           temp->data.free_list.prev);

                    printf("class number=%d\n", class);
                    printf("###################################################"
                           "####"
                           "############\n");
                }
                if (temp->data.free_list.next != NULL) {
                    if (temp->data.free_list.next > (block_t *)mem_heap_hi() ||
                        temp->data.free_list.next < (block_t *)mem_heap_lo()) {
                        printf("###############################################"
                               "########"
                               "############\n");
                        printf("blocks next pointer out of heap range\n");
                        printf("class number=%d\n", class);
                        printf("###############################################"
                               "########"
                               "############\n");
                    }
                }
            }
            temp = temp->data.free_list.next;
        }
    }

    // check next/previous pointers are not consistent
    for (int class = 1; class < MAX_SEG_LIST_LENGTH; class ++) {
        block_t *temp = seg_list[class];
        while (temp != NULL) {
            block_t *pre_block = temp->data.free_list.prev;
            if (pre_block != NULL) {
                if (pre_block->data.free_list.next != temp) {
                    printf("###################################################"
                           "####"
                           "############\n");
                    printf("next/previous pointers are not consistent\n");
                    printf("###################################################"
                           "####"
                           "############\n");
                    return false;
                }
            }
            temp = temp->data.free_list.next;
        }
    }

    // check 16 class block in range;
    block_t *temp_16_2 = seg_list[0];
    while (temp_16_2 != NULL) {
        if (get_size(temp_16_2) > min_block_size) {
            printf("#######################################################"
                   "############\n");
            printf("current size= 16");
            printf("blocks do not fall within bucket size range\n");
            printf("class number=0\n");
            printf("block_size=%zu \n", get_size(temp_16_2));
            block_t *temp = seg_list[0];
            while (temp != NULL) {
                printf("%zu, block---->", get_size(temp));
                temp = temp->data.free_list.next;
            }
            printf("#######################################################"
                   "############\n");
        }
        temp_16_2 = temp_16_2->data.free_list.next;
    }

    // check free list from 16+ size
    for (int class = 1; class < MAX_SEG_LIST_LENGTH; class ++) {
        block_t *temp = seg_list[class];

        size_t size = (2 * min_block_size) << (class - 1);

        while (temp != NULL) {
            size_t block_size = get_size(temp);

            if (class < MAX_SEG_LIST_LENGTH - 1) {
                if (block_size > size) {
                    printf("###################################################"
                           "####"
                           "############\n");
                    printf("current size= %zu", size);
                    printf("blocks do not fall within bucket size range\n");
                    printf("class number=%d\n", class);
                    printf("block_size=%zu \n", block_size);
                    block_t *temp2 = seg_list[class];
                    while (temp2 != NULL) {
                        printf("%zu, block---->", get_size(temp2));
                        temp2 = temp2->data.free_list.next;
                    }
                    printf("###################################################"
                           "####"
                           "############\n");
                    return false;
                }
            }
            temp = temp->data.free_list.next;
        }
    }

    // CYPTODO:All free list pointers are between mem heap lo() and mem heap
    // high().

    // Count free blocks by iterating through every block and traversing free
    // list by pointers and see if they match.

    int free_block_count = 0;
    for (block = heap_start; get_size(block) > 0; block = find_next(block)) {
        if (get_alloc(block) == 0)
            free_block_count++;
    }

    int free_list_count = 0;
    for (int class = 0; class < MAX_SEG_LIST_LENGTH; class ++) {
        block_t *temp = seg_list[class];

        // printf("while count=%d\n", free_list_count);
        while (temp != NULL) {

            free_list_count++;

            temp = temp->data.free_list.next;
        }
    }

    if (free_block_count != free_list_count) {
        printf("###############################################################"
               "####\n");
        printf("free list numbers do not match\n");
        printf("free block count=%d\n", free_block_count);
        printf("free list count=%d\n", free_list_count);
        for (int class = 0; class < MAX_SEG_LIST_LENGTH; class ++) {
            if (seg_list[class] != NULL) {
                printf("-----class=%d", class);
                printf("-----address=%p", seg_list[class]);
            }
        }
        printf("###############################################################"
               "####\n");
        return false;
    }

    // no cycle linklist

    return true;
}

/**
 * @brief
 *
 * <What does this function do?>
 * <What are the function's arguments?>
 * <What is the function's return value?>
 * <Are there any preconditions or postconditions?>
 *
 * @return
 */
bool mm_init(void) {
    // printf("start");
    // Create the initial empty heap
    // printf("start\n");
    word_t *start = (word_t *)(mem_sbrk(2 * wsize));

    if (start == (void *)-1) {
        return false;
    }

    start[0] = pack(0, false, true, true); // Heap prologue (block footer)
    start[1] = pack(0, false, true, true); // Heap epilogue (block header)

    // Heap starts with first "block header", currently the epilogue
    heap_start = (block_t *)&(start[1]);
    // reinitialize seg list
    for (int index = 0; index < MAX_SEG_LIST_LENGTH; index++) {
        seg_list[index] = NULL;
    }

    // Extend the empty heap with a free block of chunksize bytes
    if (extend_heap(chunksize) == NULL) {
        return false;
    }

    return true;
}

/**
 * @brief
 *
 * <What does this function do?>
 * <What are the function's arguments?>
 * <What is the function's return value?>
 * <Are there any preconditions or postconditions?>
 *
 * @param[in] size
 * @return
 */
void *malloc(size_t size) {

    dbg_requires(mm_checkheap(__LINE__));

    // printf("malloc run!!!!!!!!!!!!\n");

    size_t asize;      // Adjusted block size
    size_t extendsize; // Amount to extend heap if no fit is found
    block_t *block;
    void *bp = NULL;

    // Initialize heap if it isn't initialized
    if (heap_start == NULL) {
        mm_init();
    }

    // Ignore spurious request
    if (size == 0) {
        dbg_ensures(mm_checkheap(__LINE__));
        return bp;
    }

    // Adjust block size to include overhead and to meet alignment requirements
    asize = round_up(size + wsize, dsize);

    // if(asize<dsize*2){
    //     asize=2*dsize;
    // }

    // Search the free list for a fit
    block = find_fit(asize);

    // If no fit is found, request more memory, and then and place the block
    if (block == NULL) {
        // Always request at least chunksize
        extendsize = max(asize, chunksize);
        block = extend_heap(extendsize);
        // extend_heap returns an error
        if (block == NULL) {
            return bp;
        }
    }

    // The block should be marked as free
    dbg_assert(!get_alloc(block));

    // Mark block as allocated
    // size_t block_size = get_size(block);
    // write_block(block, block_size, true);

    // Try to split the block if too large

    split_block(block, asize);

    bp = header_to_payload(block);

    dbg_ensures(mm_checkheap(__LINE__));
    return bp;
}

/**
 * @brief
 *
 * <What does this function do?>
 * <What are the function's arguments?>
 * <What is the function's return value?>
 * <Are there any preconditions or postconditions?>
 *
 * @param[in] bp
 */
void free(void *bp) {
    dbg_requires(mm_checkheap(__LINE__));

    if (bp == NULL) {
        return;
    }

    block_t *block = payload_to_header(bp);
    size_t size = get_size(block);

    // The block should be marked as allocated
    dbg_assert(get_alloc(block));

    // Mark the block as free
    // write_block(block, size, false);
    bool pre_alloc = get_pre_alloc(block);
    bool pre_min = get_pre_min(block);
    write_header(block, size, pre_min, pre_alloc, false);

    if (size != min_block_size) {
        write_footer(block, size, pre_min, pre_alloc, false);
        set_next_block_pre_alloc_pre_min(block, false, false);
    } else {
        set_next_block_pre_alloc_pre_min(block, true, false);
    }

    // Try to coalesce the block with its neighbors

    block = coalesce_block(block);

    dbg_ensures(mm_checkheap(__LINE__));
}

/**
 * @brief
 *
 * <What does this function do?>
 * <What are the function's arguments?>
 * <What is the function's return value?>
 * <Are there any preconditions or postconditions?>
 *
 * @param[in] ptr
 * @param[in] size
 * @return
 */
void *realloc(void *ptr, size_t size) {
    block_t *block = payload_to_header(ptr);
    size_t copysize;
    void *newptr;

    // If size == 0, then free block and return NULL
    if (size == 0) {
        free(ptr);
        return NULL;
    }

    // If ptr is NULL, then equivalent to malloc
    if (ptr == NULL) {
        return malloc(size);
    }

    // Otherwise, proceed with reallocation
    newptr = malloc(size);

    // If malloc fails, the original block is left untouched
    if (newptr == NULL) {
        return NULL;
    }

    // Copy the old data
    copysize = get_payload_size(block); // gets size of old payload
    if (size < copysize) {
        copysize = size;
    }
    memcpy(newptr, ptr, copysize);

    // Free the old block
    free(ptr);

    dbg_ensures(mm_checkheap(__LINE__));

    return newptr;
}

/**
 * @brief
 *
 * <What does this function do?>
 * <What are the function's arguments?>
 * <What is the function's return value?>
 * <Are there any preconditions or postconditions?>
 *
 * @param[in] elements
 * @param[in] size
 * @return
 */
void *calloc(size_t elements, size_t size) {
    void *bp;
    size_t asize = elements * size;

    if (asize / elements != size) {
        // Multiplication overflowed
        return NULL;
    }

    bp = malloc(asize);
    if (bp == NULL) {
        return NULL;
    }

    // Initialize all bits to 0
    memset(bp, 0, asize);

    return bp;
}

/*
 *****************************************************************************
 * Do not delete the following super-secret(tm) lines!                       *
 *                                                                           *
 * 53 6f 20 79 6f 75 27 72 65 20 74 72 79 69 6e 67 20 74 6f 20               *
 *                                                                           *
 * 66 69 67 75 72 65 20 6f 75 74 20 77 68 61 74 20 74 68 65 20               *
 * 68 65 78 61 64 65 63 69 6d 61 6c 20 64 69 67 69 74 73 20 64               *
 * 6f 2e 2e 2e 20 68 61 68 61 68 61 21 20 41 53 43 49 49 20 69               *
 *                                                                           *
 * 73 6e 27 74 20 74 68 65 20 72 69 67 68 74 20 65 6e 63 6f 64               *
 * 69 6e 67 21 20 4e 69 63 65 20 74 72 79 2c 20 74 68 6f 75 67               *
 * 68 21 20 2d 44 72 2e 20 45 76 69 6c 0a c5 7c fc 80 6e 57 0a               *
 *                                                                           *
 *****************************************************************************
 */
