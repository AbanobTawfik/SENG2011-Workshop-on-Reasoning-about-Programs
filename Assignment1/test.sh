#!/bin/sh

touch output.txt

for i in 1 2 3 4 5 6 7
do
	time dafny /compile:3 Ex$i.dfy >> output.txt
done