
.PHONY: all clean

all: guide.html guide.pdf

guide.html: guide.md
	pandoc -s -N -o $@ -t html5 $^

guide.pdf: guide.md
	pandoc -s -N --toc -o $@ -t latex $^

clean:
	rm -f guide.html guide.pdf
