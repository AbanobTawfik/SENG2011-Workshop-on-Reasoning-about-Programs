#!/bin/sh

touch output.txt

for i in 1 2 3 4 5
do
	echo "---------------------------------------------------------" >> output.txt
	echo "running Ex$i.dfy" >> output.txt
	echo " " >> output.txt
	time dafny /compile:3 Ex$i.dfy >> output.txt
	echo "---------------------------------------------------------" >> output.txt
	echo " " >> output.txt
	echo " " >> output.txt
done