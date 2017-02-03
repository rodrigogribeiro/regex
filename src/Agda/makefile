STDLIB=~/.agda/libraries
COMPILEDIR=./../../dist
HTMLDIR=./../../html

all:
	agda -i . -i ${STDLIB} -c --compile-dir=${COMPILEDIR} ./Tool/Main.agda
	agda -i . --html --html-dir=${HTMLDIR} ./Everything.agda

clean:
	rm -rf ${COMPILEDIR}
	find . -name "*.agdai" | xargs rm

deepclean:
	rm -rf ${COMPILEDIR}
	rm -rf ${HTMLDIR}
	find . -name "*.agdai" | xargs rm
