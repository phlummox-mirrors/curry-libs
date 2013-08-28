# Makefile for various compilations of the system libraries,
# in particular, to generate the documentation

CYMAKEPARAMS = --extended --no-verb --no-warn --no-overlap-warn -i. -imeta

# directory for HTML documentation files
# LIBDOCDIR = $(DOCDIR)/html
LIBDOCDIR := CDOC
# directory for LaTeX documentation files
TEXDOCDIR := $(DOCDIR)/src/lib

# replacement stuff
comma     := ,
empty     :=
space     := $(empty) $(empty)
# prefix "pre" "dir/file.ext" = "dir/prefile.ext"
prefix     = $(dir $(2))$(1)$(notdir $(2))
# comma_sep "a b c" = "a, b, c"
comma_sep  = $(subst $(space),$(comma)$(space),$(1))

# Curry library files
LIB_CURRY     = $(filter-out Curry_Main_Goal.curry, $(wildcard *.curry meta/*.curry))
# lib names without directory prefix
LIB_NAMES     = $(basename $(notdir $(LIB_CURRY)))
# Generated files
LIB_ACY       = $(foreach lib, $(LIB_CURRY:.curry=.acy), $(call prefix,.curry/,$(lib)))
LIB_FCY       = $(foreach lib, $(LIB_CURRY:.curry=.fcy), $(call prefix,.curry/,$(lib)))
LIB_HS        = $(foreach lib, $(LIB_CURRY:.curry=.hs) , $(call prefix,.curry/kics2/Curry_,$(lib)))
LIB_HTML      = $(patsubst %, $(LIBDOCDIR)/%.html, $(LIB_NAMES))
LIB_TEX       = $(patsubst %, $(TEXDOCDIR)/%.tex , $(LIB_NAMES))
HS_LIB_NAMES  = $(call comma_sep,$(LIB_NAMES:%=Curry_%))

PACKAGE       = kics2-libraries
CABAL_FILE    = $(PACKAGE).cabal
CABAL_LIBDEPS = $(call comma_sep,$(LIBDEPS))

########################################################################
# support for installation
########################################################################

.PHONY: install
install: $(LIB_FCY) $(LIB_ACY) $(LIB_HS) $(CABAL_FILE)
	$(CABAL_INSTALL)

.PHONY: unregister
unregister:
	-$(GHC_UNREGISTER) $(PACKAGE)-$(VERSION)

# clean Haskell intermediate files
.PHONY:
clean:
	-cd .curry/kics2      && rm -f *.hi *.o
	-cd meta/.curry/kics2 && rm -f *.hi *.o

# clean all generated files
.PHONY: cleanall
cleanall:
	rm -rf "$(LIBDOCDIR)"
	rm -rf "$(TEXDOCDIR)"
	rm -rf dist
	rm -f $(CABAL_FILE)
	$(CLEANCURRY)
	cd meta && $(CLEANCURRY)

$(CABAL_FILE): ../Makefile Makefile
	echo "Name:           $(PACKAGE)"                             > $@
	echo "Version:        $(VERSION)"                            >> $@
	echo "Description:    The standard libraries for KiCS2"      >> $@
	echo "License:        OtherLicense"                          >> $@
	echo "Author:         Fabian Reck"                           >> $@
	echo "Maintainer:     fre@informatik.uni-kiel.de"            >> $@
	echo "Build-Type:     Simple"                                >> $@
	echo "Cabal-Version:  >= 1.9.2"                              >> $@
	echo ""                                                      >> $@
	echo "Library"                                               >> $@
	echo "  Build-Depends:"                                      >> $@
	echo "      kics2-runtime == $(VERSION)"                     >> $@
	echo "    , $(CABAL_LIBDEPS)"                                >> $@
	echo "  if os(windows)"                                      >> $@
	echo "    Build-Depends: Win32"                              >> $@
	echo "  else"                                                >> $@
	echo "    Build-Depends: unix"                               >> $@
	echo "  Exposed-modules: $(HS_LIB_NAMES)"                    >> $@
	echo "  hs-source-dirs: ./.curry/kics2, ./meta/.curry/kics2" >> $@

# generate Haskell file in subdirectory .curry/kics2
.curry/kics2/Curry_%.hs: %.curry
	$(COMP) -v0 -i. -imeta $*

meta/.curry/kics2/Curry_%.hs: meta/%.curry
	$(COMP) -v0 -i. -imeta meta/$*

# generate FlatCurry file in subdirectory .curry
.curry/%.fcy: %.curry
	"${CYMAKE}" --flat ${CYMAKEPARAMS} $*

meta/.curry/%.fcy: meta/%.curry
	"${CYMAKE}" --flat ${CYMAKEPARAMS} $*

# generate AbstractCurry file in subdirectory .curry
.curry/%.acy: %.curry
	"${CYMAKE}" --acy ${CYMAKEPARAMS} $*

meta/.curry/%.acy: meta/%.curry
	"${CYMAKE}" --acy ${CYMAKEPARAMS} $*

##############################################################################
# create HTML documentation files for system libraries
##############################################################################

.PHONY: doc
doc: $(LIB_CURRY)
	mkdir -p "$(LIBDOCDIR)"
	$(MAKE) $(LIB_HTML)
	@echo "Generating index pages for Curry libraries:"
	@echo $(LIB_NAMES)
	"$(CURRYDOC)" --onlyindexhtml "$(LIBDOCDIR)" $(LIB_NAMES)

# generate individual documentations for libraries
$(LIBDOCDIR)/%.html: %.curry
	"$(CURRYDOC)" --noindexhtml "$(LIBDOCDIR)" $*

$(LIBDOCDIR)/%.html: meta/%.curry
	"$(CURRYDOC)" --noindexhtml "$(LIBDOCDIR)" $*

##############################################################################
# create LaTeX documentation files for system libraries
##############################################################################

.PHONY: texdoc
texdoc: $(LIB_CURRY)
	mkdir -p "$(TEXDOCDIR)"
	$(MAKE) $(LIB_TEX)

# generate individual LaTeX documentations for libraries
$(TEXDOCDIR)/%.tex: %.curry
	"$(CURRYDOC)" --tex "$(TEXDOCDIR)" $*

$(TEXDOCDIR)/%.tex: meta/%.curry
	"$(CURRYDOC)" --tex "$(TEXDOCDIR)" $*
