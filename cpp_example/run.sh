ldmd2 -betterC -O -inline -release eye.d -I../source -c
g++ main.cpp eye.o -I../include
./a.out
