###########################################################
# This file builds the mir documentation.
###########################################################

# tags
LATEST:=$(git describe --abbrev=0 --tags | tr -d v)

# binaries
DMD=dmd
RDMD=rdmd
DDOC=$(DMD) -w -c -o- -version=StdDdoc -version=Have_mir

# folders
DOC_OUTPUT_DIR=web
DOC_SOURCE_DIR=doc
GENERATED=.generated
ALGORITHM_DIR=source
DLANGORG_DIR=$(DOC_SOURCE_DIR)/dlang.org
ARTWORK_DIR=$(DOC_SOURCE_DIR)/artwork

###########################################################
# setup packages
##########################################################

# Packages in mir. Just mention the package name here. The contents of package
# xy/zz is in variable PACKAGE_xy_zz. This allows automation in iterating
# packages and their modules.
MIR_PACKAGES = mir mir/ndslice mir/internal mir/math mir/math/func mir/array mir/interpolation

PACKAGE_mir = bitmanip conv functional primitives timeseries utility

PACKAGE_mir_array = primitives
PACKAGE_mir_internal = utility
PACKAGE_mir_interpolation = package linear pchip
PACKAGE_mir_math = constant common sum numeric package
PACKAGE_mir_math_func = expdigamma

PACKAGE_mir_ndslice = \
	algorithm\
	allocation\
	chunks\
	concatenation\
	dynamic\
	field\
	iterator\
	mutation\
	ndfield\
	package\
	slice\
	sorting\
	topology\
	traits\

MOD_EXCLUDES=$(addprefix --ex=,)

###########################################################
# Setup macros + generate dynamic info needed
###########################################################

all: html

DLANGORG_MACROS=$(addprefix $(DLANGORG_DIR)/, macros html dlang.org)
STDDOC=$(addsuffix .ddoc, ${DLANGORG_MACROS} ${GENERATED}/${LATEST} $(DLANGORG_DIR)/std $(DOC_SOURCE_DIR)/custom ${GENERATED}/mir) $(NODATETIME)

${GENERATED}/${LATEST}.ddoc :
	mkdir -p $(dir $@)
	echo "LATEST=${LATEST}" >$@

${GENERATED}/mir.ddoc : $(DOC_SOURCE_DIR)/gen_modlist.d $(ALGORITHM_DIR)
	mkdir -p $(dir $@)
	$(RDMD) --compiler=$(DMD) $< $(ALGORITHM_DIR) $(MOD_EXCLUDES) >$@

###########################################################
# Makefile bootstrapping
# It's mostly about the conversion from mir.foo -> mir_foo
###########################################################

# Given one or more packages, returns the modules they contain
P2MODULES=$(foreach P,$1,$(addprefix $P/,$(PACKAGE_$(subst /,_,$P))))
MIR_MODULES=$(call P2MODULES,$(MIR_PACKAGES))
SRC_DOCUMENTABLES = index.d $(addsuffix .d,$(MIR_MODULES))

# D file to html, e.g. mir/combinatorics -> mir_combinatorics.html
# But "package.d" is special cased: std/range/package.d -> std_range.html
D2HTML=$(foreach p,$1,$(if $(subst package.d,,$(notdir $p)),$(subst /,_,$(subst .d,.html,$p)),$(subst /,_,$(subst /package.d,.html,$p))))

HTMLS=$(addprefix $(DOC_OUTPUT_DIR)/, \
	$(call D2HTML, $(SRC_DOCUMENTABLES)))

$(DOC_OUTPUT_DIR)/. :
	mkdir -p $@

# everything except index.d needs a source path
ADDSOURCE=$(if $(subst index.d,,$1),$(ALGORITHM_DIR)/$1,$1)

# For each module, define a rule e.g.:
# ../web/phobos/std_conv.html : std/conv.d $(STDDOC) ; ...
$(foreach p,$(SRC_DOCUMENTABLES),$(eval \
$(DOC_OUTPUT_DIR)/$(call D2HTML,$p) : $(call ADDSOURCE,$p) $(STDDOC) ;\
  $(DDOC) $(STDDOC) -I$(ALGORITHM_DIR) -Df$$@ $$<))

###########################################################
# Setup all other resources needed by dlang.org
###########################################################

IMAGES=images/mir.svg favicon.ico

JAVASCRIPT=$(addsuffix .js, $(addprefix js/, \
	dlang ddox listanchors run run-main-website jquery-1.7.2.min))

STYLES=$(addsuffix .css, $(addprefix css/, \
	style print custom ))

ALL_FILES = $(addprefix $(DOC_OUTPUT_DIR)/, \
	$(STYLES) $(IMAGES) $(JAVASCRIPT))

$(DOC_OUTPUT_DIR)/css/custom.css: $(DOC_SOURCE_DIR)/custom.css
	@mkdir -p $(dir $@)
	cp $< $@

$(DOC_OUTPUT_DIR)/images/mir.svg: $(ARTWORK_DIR)/logo/mir_site_logo.svg
	@mkdir -p $(dir $@)
	cp $< $@

$(DOC_OUTPUT_DIR)/% : $(DLANGORG_DIR)/%
	@mkdir -p $(dir $@)
	cp $< $@

html : $(DOC_OUTPUT_DIR)/. $(HTMLS) $(ALL_FILES)

clean:
	rm -rf $(DOC_OUTPUT_DIR)
	rm -rf $(GENERATED)

# prints the listed modules and sources
debug:
	@echo $(SRC_DOCUMENTABLES)
	@echo $(STDDOC)
