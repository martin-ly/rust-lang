# Coq Makefile for Rust Ownership Formalization

COQMAKEFILE := coq_makefile
COQFLAGS := -Q theories RustOwnership

.PHONY: all clean install

all: Makefile.coq
	$(MAKE) -f Makefile.coq

Makefile.coq: _CoqProject
	$(COQMAKEFILE) -f _CoqProject -o Makefile.coq

clean: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq

install: all
	$(MAKE) -f Makefile.coq install

# 验证所有证明
verify: all
	@echo "Verifying all proofs..."
	$(MAKE) -f Makefile.coq validate

# 生成文档
doc:
	coqdoc -toc -html -d html theories/*.v

# 统计代码行数
stats:
	@echo "=== Code Statistics ==="
	@find theories -name "*.v" | xargs wc -l
	@echo "======================="
