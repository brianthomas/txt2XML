
# My little make file 

$DVISRC =  main.dvi

$MAINDVI = main.dvi

CHAPTERS = part1.tex part2.tex part3.tex 

APPENDICES = appA.tex 

OTHER_TEX = local.sty index.tex

TEX = latex

DOCNAME = "txt2XML_users_guide.ps" 

guide:: $(DOCNAME)

$(DOCNAME): main.dvi
	dvips -o $(DOCNAME) main.dvi

all::

main.dvi: main.aux 
	latex main.tex

main.aux: main.tex $(CHAPTERS) $(APPENDICES) index.tex
	$(RM) main.aux
	$(RM) main.idx
	latex main.tex

ps:	dvi

index.tex:	
	touch main.idx
	$(RM) index.tex
	./make_index.pl main.idx > index.tex
        
dvi:	$(MAINDVI) $(DVISRC)
	dvips -o $(DOCNAME) main.dvi
	@echo The finished postscript document is $(DOCNAME)

clean:	
	rm -f *.dvi *.aux *.toc *.log index.tex *.idx $(DOCNAME)


