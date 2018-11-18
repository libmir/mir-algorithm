ldmd2 -betterC -O -inline -release eye.d init_rcarray.d -I../source -c
g++ main.cpp eye.o -std=c++11 -I../include
./a.out
