# Malloc lab
This malloc implementation was written for CSE361S: Introduction to System Software at Washington University in St. Louis. The end result gave approximately 73.1% utilization when running the
overall test.  
## Implementation
The implementation uses a segmented doubly-linked list structure using a first fit approach. All blocks returned by this malloc implementation return a 16-byte (double word) aligned address.  
### Normal blocks
The typical block in this implementation uses a 32 byte minimum size block with the following structure:  
* Free block
```
Byte | 0      | 8            | 16           | 24      |        |
Data | Header | Next pointer | Prev pointer | Padding | Footer |
```
* Allocated block
```
Byte | 0      | 8       |
Data | Header | Payload |
```
The headers (and footers) are structured in the table below. The sblock bit indicates if the block is small, which is elaborated in the next section.
```
Bit  | 31      | 3           | 2      | 1          | 0     |
Data | Size    | prev_sblock | sblock | prev_alloc | alloc |
```

### Small blocks
Since the pointer returned by `malloc` must be 16 byte aligned, and the minimum block size is 32 bytes, any request for less than 8 bytes can technically be smaller, but actually takes 32 bytes. As such, a different format for small blocks was used.  
Since these small blocks have a fixed size of 16 bytes, there is no need to store the size. Furthermore, the bottom 4 bits of the address of small blocks are always the same, due to the 16-byte alignment requirement. As such, small blocks are structured as such:
```
Word 0
Bit  | 31      | 3           | 2      | 1          | 0     |
Data | Prev    | prev_sblock | sblock | prev_alloc | alloc |
Word 1
Bit  | 0    |
Data | Next |
```

### Testing the implementation
Below is the original documentation given to students.
```
#############################
# CS:APP Malloc Lab
# Handout files for students
#############################

***********
Main Files:
***********

mm.{c,h}
        Your solution malloc package. mm.c is the file that you
        will be handing in, and is the only file you should modify.

Makefile
        Builds the driver

mdriver.c
        The malloc driver that tests your mm.c file
        Once you've run make, run ./mdriver to test
        your solution.

traces/
	Directory that contains the trace files that the driver uses
	to test your solution. Files with names of the form XXX-short.rep
	contain very short traces that you can use for debugging.

**********************************
Other support files for the driver
**********************************
config.h	Configures the malloc lab driver
clock.{c,h}	Low-level timing functions
fcyc.{c,h}	Function-level timing functions
memlib.{c,h}	Models the heap and sbrk function
stree.{c,h}     Data structure used by the driver to check for
		overlapping allocations

*******************************
Building and running the driver
*******************************
To build the driver, type "make" to the shell.

To run the driver on a tiny test trace:

	unix> ./mdriver -V -f traces/syn-array-short.rep

To get a list of the driver flags:

	unix> ./mdriver -h

The -V option prints out helpful tracing information
```
