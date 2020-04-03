CC = gcc
FLAGS = 
EXEC = gencnf+

all:
	@echo "Building gencnf ..."
	$(CC) $(FLAGS) genpms.c -O3 -o genpms -lm
	@echo "Done."

clean:
	@echo "Cleaning up"
	rm $(EXEC)
	@echo "Done"

cleantxt:
	@echo "Cleaning generate txt..."
	rm v*
	@echo "Done"
