How to compile wordfreq with HOL 

in the directory with all the theorems run Holmake.
it will run for 1 h and compile all the dependencies.
Result is a file with extesion .S

Copy that file to the directory with cake makefile (cake-x64-64).
Create a sample .txt file with words(test_text_file.txt)

run:
make clean
cc  cake.S basis_ffi.c   -D__EVAL__ -o cake
cc  wordfreq.S basis_ffi.c   -o wordfreq.cake
./wordfreq.cake test_text_file.txt