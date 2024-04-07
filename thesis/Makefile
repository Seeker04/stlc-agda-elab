TITLE    = STLC-elaboration-in-Agda
SRCS     = elteikthesis.* chapters/*
TEXFLAGS = -shell-escape -jobname=$(TITLE)

$(TITLE).pdf: $(SRCS)
	xelatex $(TEXFLAGS) elteikthesis.tex
	biber $(TITLE)
	makeindex $(TITLE).nlo -s nomencl.ist -o $(TITLE).nls
	xelatex $(TEXFLAGS) elteikthesis.tex

clean:
	rm -rf *.aux *.bcf *.idx *.loa *.lof *.log *.lol *.lot *.nlo *.pdf *.run.xml \
	       *.toc *.blg *.bbl *.ilg *.nls nomencl.ist $(TITLE).pdf _minted-$(TITLE) images/*.pdf

