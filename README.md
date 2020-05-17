# Malloc lab
This was written for CSE361S: Introduction to System Software at Washington University
in St. Louis. The end result gave approximately 73.1% utilization when running the
overall test.  
Below is the original documentation given to students.

# CS:APP Malloc Lab
### Handout files for students

***********
Main Files:
***********

* mm.{c,h}  
    Your solution malloc package. mm.c is the file that you
    will be handing in, and is the only file you should modify.

* Makefile  
    Builds the driver

* mdriver.c  
    The malloc driver that tests your mm.c file
    Once you've run make, run ./mdriver to test
    your solution.

* traces/  
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