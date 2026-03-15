TARGET_DIR ?= .tmp/maturin-target

# In vs code, cargo check is called on save, which makes pyo3 recompile unless I change the target directory
# It also tends to cause a lock
# `--profile release` actually doesn't get smashed but it's a tad slower
# https://github.com/PyO3/maturin/issues/504

develop:
	maturin develop --target-dir $(TARGET_DIR) 

test: develop
	pytest -q
