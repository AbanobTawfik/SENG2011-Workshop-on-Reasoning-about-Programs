#!/bin/sh

touch output.txt

for i in 1 2 3 4 5 6 7
do
	echo "---------------------------------------------------------" >> output.txt
	echo "running Ex$i.dfy" >> output.txt
	echo " " >> output.txt
	dafny /compile:3 Ex$i.dfy >> output.txt
	echo "---------------------------------------------------------" >> output.txt
	echo " " >> output.txt
	echo " " >> output.txt
done