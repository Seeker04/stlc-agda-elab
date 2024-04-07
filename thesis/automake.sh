#!/bin/sh

while true; do
	inotifywait --event modify elteikthesis.* chapters/
	make
done

