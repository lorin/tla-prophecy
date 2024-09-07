build:
	c++ -std=c++17 -o hwqueue HWQueue.cpp
	./hwqueue | tee out.txt
#	../dbdiag/ophistory.py out.txt > out.svg

run:
		./queue.py
