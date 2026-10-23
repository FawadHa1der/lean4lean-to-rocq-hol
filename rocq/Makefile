# SPDX-License-Identifier: Apache-2.0
# These paths use the parent-managed local toolchain; this file installs nothing.
ROCQ ?= ../toolchain/opam-root/lean4lean/bin/rocq
OCAMLOPT ?= ../toolchain/opam-root/lean4lean/bin/ocamlopt
ROCQFLAGS = -Q . LeanPort

.PHONY: all check extract audit
all: core_regression

Syntax.vo: Syntax.v

Universes.vo: Universes.v Syntax.vo

EagerPolicy.vo: EagerPolicy.v Syntax.vo

NatProbeDispatch.vo: NatProbeDispatch.v Syntax.vo

WhnfPolicy.vo: WhnfPolicy.v Syntax.vo EagerPolicy.vo

Checker.vo: Checker.v Syntax.vo Universes.vo EagerPolicy.vo NatProbeDispatch.vo WhnfPolicy.vo

InductiveUtils.vo: InductiveUtils.v Checker.vo

Primitives.vo: Primitives.v Checker.vo InductiveUtils.vo

Declarations.vo: Declarations.v Checker.vo Primitives.vo

Regression.vo: Regression.v Checker.vo

DeclarationRegression.vo: DeclarationRegression.v Declarations.vo

ExtensionRegression.vo: ExtensionRegression.v Regression.vo

PerformanceRegression.vo: PerformanceRegression.v ExtensionRegression.vo

Extract.vo: Extract.v Regression.vo ExtensionRegression.vo PerformanceRegression.vo Declarations.vo

%.vo: %.v
	"$(ROCQ)" compile $(ROCQFLAGS) "$<"

lean_core.ml lean_core.mli: Extract.vo
	@test -f "$@"

extract: Extract.vo

core_regression: lean_core.ml lean_core.mli core_regression.ml
	"$(OCAMLOPT)" -c lean_core.mli
	"$(OCAMLOPT)" -c lean_core.ml
	"$(OCAMLOPT)" -o core_regression lean_core.cmx core_regression.ml

check: core_regression Regression.vo ExtensionRegression.vo PerformanceRegression.vo DeclarationRegression.vo
	./core_regression

audit: Syntax.vo Universes.vo Checker.vo Regression.vo ExtensionRegression.vo PerformanceRegression.vo Declarations.vo DeclarationRegression.vo
	"$(ROCQ)" check -silent -o $(ROCQFLAGS) LeanPort.Syntax LeanPort.Universes LeanPort.Checker LeanPort.Regression LeanPort.ExtensionRegression LeanPort.PerformanceRegression LeanPort.Declarations LeanPort.DeclarationRegression
