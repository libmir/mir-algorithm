###########################################################
# This file builds the mir documentation.
###########################################################

# tags
LATEST:=$(shell git describe --abbrev=0 --tags | tr -d v)

# binaries
DMD=dmd
RDMD=rdmd
DDOC=$(DMD) -w -c -o- -version=StdDdoc -version=Have_mir

# folders
DOC_OUTPUT_DIR=web
DOC_SOURCE_DIR=doc
GENERATED=.generated
ALGORITHM_DIR=source
CORE_DIR=subprojects/mir-core/source
DLANGORG_DIR=$(DOC_SOURCE_DIR)/dlang.org
ARTWORK_DIR=$(DOC_SOURCE_DIR)/artwork

###########################################################
# setup packages
##########################################################

# Packages in mir. Just mention the package name here. The contents of package
# xy/zz is in variable PACKAGE_xy_zz. This allows automation in iterating
# packages and their modules.
MIR_PACKAGES = mir mir/rc mir/ndslice mir/ndslice/connect mir/math mir/math/func mir/array mir/interpolate mir/graph mir/combinatorics mir/container mir/algorithm

PACKAGE_mir = \
	range \
	series \
	numeric \
	type_info \
	small_string \
	small_array \
	polynomial \
	format\
	parse\
	appender\
	exception\
	traits\

PACKAGE_mir_algorithm = iteration setops
PACKAGE_mir_array = allocation
PACKAGE_mir_cpp_export = numeric
PACKAGE_mir_combinatorics = package
PACKAGE_mir_container = binaryheap
PACKAGE_mir_graph = tarjan package
PACKAGE_mir_interpolate = package constant linear spline utility polynomial
PACKAGE_mir_math = sum numeric stat
PACKAGE_mir_math_func = expdigamma
PACKAGE_mir_ndslice_connect = cpython
PACKAGE_mir_rc = package ptr array context

PACKAGE_mir_ndslice = \
	allocation\
	chunks\
	concatenation\
	dynamic\
	field\
	filling\
	fuse\
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
	echo "LATEST_STABLE=$(shell git tag | grep -vE "(alpha|beta)" | tail -n1 | tr -d v)" >> $@

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
  $(DDOC) $(STDDOC) -I$(ALGORITHM_DIR) -I$(CORE_DIR)  -Df$$@ $$<))

###########################################################
# Setup all other resources needed by dlang.org
###########################################################

IMAGES=images/mir.svg favicon.ico

JAVASCRIPT=$(addsuffix .js, $(addprefix js/, \
	codemirror-compressed dlang ddox listanchors run run_examples jquery-1.7.2.min))

STYLES=$(addsuffix .css, $(addprefix css/, \
	style print custom codemirror))

ALL_FILES = $(addprefix $(DOC_OUTPUT_DIR)/, \
	$(STYLES) $(IMAGES) $(JAVASCRIPT))

$(DOC_OUTPUT_DIR)/css/custom.css: $(DOC_SOURCE_DIR)/custom.css
	@mkdir -p $(dir $@)
	cp $< $@

$(DOC_OUTPUT_DIR)/js/run_examples.js: $(DOC_SOURCE_DIR)/run_examples_custom.js
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
