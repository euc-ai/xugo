package gates

import (
	"strings"
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/engine"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/dsl"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/vector/euclidean"
	"github.com/euc-ai/xugo/library/proofs/vector/lattice"
	"github.com/euc-ai/xugo/library/proofs/vector/vec_space"
	"github.com/euc-ai/xugo/library/registry"
	"github.com/euc-ai/xugo/prover/proof"
)

// Implicit structure arguments on the live corpus (ext/dsl/implicit.go,
// registry.DefEntry.Implicit, Family.WithInstance): the vector chapters
// are the tenants the checks below parse, and the topology chapters the
// second — every one-space notion reads the topology T. Under a
// structure law's ∀-prefix and under euclidean's ℝ instance, the short
// and the explicit spellings are one statement; outside both, the short
// form is refused. The census in TestImplicitArgs_VectorChapters covers
// every constant that registers implicit binders, whatever its chapter,
// and checks that record-first algebra APIs register none.

func familyScope(t *testing.T, f *registry.Family) *dsl.ParseScope {
	t.Helper()
	// The statement door's own scope: the family vocabulary and its
	// instance bindings, over the process constant registry.
	mgr := registry.GetConstMetaManager()
	env := &proof.ProverEnv{
		ProofService: &proof.ProofService{
			LoadConstMeta:        mgr.LoadConstMeta,
			LoadOrStoreConstMeta: mgr.LoadOrStoreConstMeta,
			Syntax:               mgr,
		},
		LibraryThms: map[string]core.Thm{},
	}
	ctx := f.ParseScript(env)
	return &ctx.ParseScope
}

func parseIn(t *testing.T, scope *dsl.ParseScope, text string) ext.Prop {
	t.Helper()
	res := dsl.ParsePropTextInScope(text, scope)
	if len(res.Errors) > 0 {
		t.Fatalf("%q: %s", text, res.Errors[0].Message)
	}
	return res.Prop
}

func TestImplicitArgs_VectorChapters(t *testing.T) {
	// Every named definition stays in the census. A record-first API
	// exposes its record explicitly and therefore registers no implicit slots.
	want := map[string][]string{
		// Finite separable covers and the trace pairing.
		"field_trace":            nil,
		"trace_quotient_module":  nil,
		"trace_cofactor":         nil,
		"trace_idempotent":       nil,
		"curve_cover":            nil,
		"cover_degree":           nil,
		"cover_pullback":         nil,
		"cover_pullback_ambient": nil,
		"trace_dual":             nil,
		"inverse_different":      nil,
		"cover_different":        nil,
		"dualizing_model":        nil,
		"dualizing_invertible":   nil,
		"ramification_degree":    nil,
		"riemann_hurwitz_data":   nil,
		"monic_cover":            nil,
		"vec_add":                {"add"}, "vec_neg": {"neg"}, "vec_sub": {"sub"}, "vec_scalar_mul": {"mul"},
		"vec_zero": {"zero"}, "vec": {"zero"}, "basis_vector": {"zero", "one"},
		"vec_linear": {"add", "mul"}, "vec_bilinear": {"add", "mul"}, "dot": {"add", "mul"},
		"adjoint":      {"zero", "one", "add", "mul"},
		"vec_subspace": {"add", "zero", "mul"}, "vec_span": {"add", "mul"},
		// The basis chapter.
		"vec_independent": {"add", "zero", "mul"}, "vec_basis": {"add", "zero", "mul"},
		"vec_dim": {"add", "zero", "mul"},
		// The matrix chapter. `transpose` is absent because it declares
		// none: swapping two indices reads no structure component.
		"matrix": {"zero"}, "matrix_of": {"zero", "one"},
		"matrix_act": {"add", "mul"}, "matrix_mul": {"add", "mul"},
		// The topology chapters: each notion stated over one space reads
		// its topology T. `hausdorff` is absent because it spells T — a
		// property of the space, with the space its one argument.
		"closed_in": {"T"}, "interior": {"T"}, "closure": {"T"}, "subtopology": {"T"},
		"compact_in": {"T"}, "connected_in": {"T"}, "connected_component": {"T"},
		// A base, the limit points and the frontier of a set, and a
		// retract are read in one space the same way.
		"topology_base": {"T"}, "derived_set": {"T"}, "frontier": {"T"}, "retract_of": {"T"},
		// The path chapter's two notions read their space the same way.
		"path_in": {"T"}, "path_connected_in": {"T"}, "path_component": {"T"},
		// The Baire chapter's notions of a set read their space the same
		// way; `baire_space` spells T, the space its one argument.
		"nowhere_dense": {"T"}, "meager": {"T"}, "baire_property": {"T"},
		// Homotopy of paths, their classes and the fundamental group read
		// their space the same way; `fundamental_map` reads the space the
		// image classes live in. `homotopic_rel`, `homotopy_equivalence`
		// and `covering_map` spell both their spaces, and
		// `contractible_space`, `simply_connected_space` and
		// `singular_set` spell the space they are said of.
		"path_homotopic": {"T"}, "loops_at": {"T"}, "path_class": {"T"}, "path_class_join": {"T"},
		"path_class_reverse": {"T"}, "fundamental_group": {"T"}, "fundamental_map": {"S"},
		"singular_simplices": {"T"},
		// The metric chapter: the balls and the open sets read the
		// carrier and the distance.
		"ball": {"M", "d"}, "closed_ball": {"M", "d"}, "metric_topology": {"M", "d"}, "metric_bounded": {"M", "d"},
		// Sequences in a metric space read the same two; completeness is
		// absent because it spells both — it is asked of subsets with the
		// same distance.
		"metric_converges_to": {"M", "d"}, "metric_cauchy": {"M", "d"}, "totally_bounded": {"M", "d"},
		// Group predicates expose their records; cosets and kernels retain
		// their operation and identity slots.
		"subgroup": nil, "normal_subgroup": nil, "group_on": nil, "left_coset": {"mul"}, "group_kernel": {"one'"},
		// Group maps and series expose their source and target records.
		"group_homomorphism": nil,
		"group_isomorphic":   nil,
		"subnormal_series":   nil, "composition_series": nil, "factors_isomorphic": nil, "series_equivalent": nil, "schreier_refinement": {"mul"},
		"group_isomorphism": nil,
		"set_mul":           {"mul"}, "set_inv": {"inv"}, "left_cosets": {"mul"},
		// The monoid spells its carrier first and every component; the
		// abelian group takes a record.
		"comm_monoid_on": nil, "abelian_group_on": nil,
		"comm_ring_on": nil,
		// The ring's alternating sign reads its one and its negation.
		"alternating_sign": {"one", "neg"},
		"field_on":         nil, "subfield": nil,
		// Ring predicates, ideals and maps expose their records. Low-level
		// localization operations retain the components they consume.
		"ring_ideal": nil, "prime_ideal": nil, "maximal_ideal": nil,
		"ideal_span": nil, "ideal_mul": nil, "ring_unit": nil, "ring_kernel": {"zero'"},
		"ring_homomorphism":  nil,
		"ring_isomorphism":   nil,
		"multiplicative_set": {"mul", "one"}, "fraction_relation": {"mul"}, "fraction_class": {"mul"}, "ring_localization": {"mul"},
		"fraction_add": {"add", "mul"}, "fraction_mul": {"mul"}, "fraction_neg": {"neg", "mul"}, "fraction_sub": {"add", "neg", "mul"},
		"fraction_zero": {"zero", "mul", "one"}, "fraction_one": {"mul", "one"}, "to_fraction": {"mul", "one"},
		"local_ring_on": nil, "residue_field": nil,
		// Integral domains and the polynomial predicates expose a record;
		// polynomial and quotient operations retain the arithmetic
		// components they consume.
		"integral_domain_on": nil,
		"polynomial_over":    {"zero"}, "polynomial_mul": {"add", "zero", "mul"}, "polynomial_degree": {"zero"}, "polynomial_eval": {"add", "zero", "mul", "one"},
		"polynomial_roots":   {"add", "zero", "mul", "one"},
		"polynomial_divides": nil, "polynomial_monic": {"zero", "one"}, "polynomial_irreducible": nil, "polynomial_derivative": {"add", "zero", "mul", "one"},
		"polynomial_splits": nil, "polynomial_separable": nil,
		"polynomial_coprime": nil, "polynomial_pow": {"add", "zero", "mul", "one"}, "polynomial_wronskian": {"add", "zero", "mul", "one", "sub"},
		"quotient_mul": {"add", "mul"}, "quotient_sub": {"add", "neg"}, "quotient_inv": {"add", "mul", "one"}, "quotient_div": {"add", "mul", "one"},
		"fraction_inv": {"zero", "mul", "one"}, "fraction_div": {"zero", "mul", "one"}, "fraction_field": {"zero", "mul"},
		// Spectrum and structure-sheaf operations expose the ring record;
		// a germ and stalk operation still read their sheaf.
		"prime_spectrum": nil, "zariski_closed": nil,
		"zariski_open": nil, "zariski_topology": nil,
		"sheaf_germ": {"T", "F", "res"}, "stalk_ring": {"T", "F", "res"}, "stalk": {"T", "F", "res"}, "stalk_map": {"T", "F", "res"},
		"stalk_add": {"T", "F", "res"}, "stalk_mul": {"T", "F", "res"}, "stalk_neg": {"T", "F", "res"},
		"stalk_sub": {"T", "F", "res"}, "stalk_zero": {"T", "F", "res"}, "stalk_one": {"T", "F", "res"},
		"structure_sections": nil, "structure_add": nil, "structure_mul": nil,
		"structure_neg": nil, "structure_sub": nil, "structure_zero": nil,
		"structure_one": nil, "fraction_section": nil, "locally_fraction": nil,
		// The free module's pointwise operations and generators read the
		// ring's components.
		"fun_add": {"add"}, "fun_zero": {"zero"}, "fun_neg": {"neg"}, "fun_smul": {"mul"}, "delta_at": {"zero", "one"},
		// Record-based chain maps and homotopies read only the ring.
		"chain_map": {"R"}, "chain_homotopy": {"R"},
		// Field extensions and algebraic elements expose the field record.
		"finite_extension": nil, "extension_degree": nil,
		"algebraic_over": nil, "minimal_polynomial": nil, "polynomial_image": nil,
		"field_adjoin": nil,
		// Fractional ideals and lattice pairs expose their ring records.
		"fractional_mul": nil, "fractional_inverse": nil, "invertible_fractional": nil,
		"lattice_pair_mul": nil, "lattice_pair_inverse": nil, "invertible_lattice_pair": nil,
		"lattice_pair_scale": {"mul"}, "lattice_pair_twist": nil, "biaffine_regular_point": nil,
		"curve_over_line": nil, "curve_genus": nil,
		"curve_degree": nil, "curve_divisor": nil, "curve_divisor_pair": nil,
		"curve_dualizing_module": nil, "curve_dualizing_pair": nil, "curve_dualizing_maps": nil,
		// Weierstrass record APIs are explicit; the two line formulas
		// retain their arithmetic component slots.
		"weierstrass_chart_zero": nil, "weierstrass_chart_one": nil,
		"weierstrass": nil, "weierstrass_point": nil,
		"weierstrass_origin": nil, "weierstrass_neg_point": nil,
		"weierstrass_line": {"add", "mul", "sub"}, "weierstrass_chart_one_line": {"add", "mul", "sub", "inv"},
		"weierstrass_dual_generator": nil, "weierstrass_point_sum": nil,
		// Curve pairs and Pic⁰ expose their ring records.
		"curve_pair_multiple": nil, "curve_pair_class": nil, "curve_class_mul": nil, "curve_class_inverse": nil,
		"curve_pic_zero": nil, "curve_point_class": nil,
		// Laurent coefficients retain components; projective-line pairs
		// and duality maps expose their field records.
		"laurent_monomial": {"mul", "one", "inv"}, "laurent_polynomial_coefficient": {"add", "zero", "mul", "one", "inv"},
		"projective_line_pair": nil, "projective_line_free_pair": nil,
		"projective_line_duality_map": nil, "projective_line_duality_inverse": nil,
		"normal_over": nil, "separable_over": nil, "galois_over": nil,
		"field_automorphisms": nil,
		"cochain_map":         {"R"}, "cochain_homotopy": {"R"},
		// The simplicial chapters: a sub-simplicial set, a simplicial map and
		// an isomorphism read the simplicial sets they are stated over, each
		// one record; the base simplex reads the degeneracy map, and a cone's
		// parts the face or the degeneracy alone.
		"sub_simplicial_set": {"X"}, "simplicial_map": {"X", "Y"}, "simplicial_isomorphism": {"X", "Y"},
		"base_simplex": {"s"},
		"simplex_cone": {"X"}, "simplex_cone_simplices": {"X"}, "simplex_cone_face": {"d"}, "simplex_cone_degeneracy": {"s"},
		"simplex_boundary_cone": {"X"}, "simplex_boundary_cone_simplices": {"X"}, "simplex_boundary_cone_face": {"d"}, "simplex_boundary_cone_degeneracy": {"s"},
		"simplex_cone_restriction": {"d"}, "simplex_boundary_cone_projection": {"d"},
		"faces_compatible": {"d"}, "face_family": {"X"}, "faces_filler": {"d"},
		// The chain chapter: the face sum and the boundary read the ring and
		// the face map, the chains the ring's zero and the simplicial set.
		"face_sum": {"add", "zero", "one", "neg", "mul", "d"}, "simplicial_chains": {"zero", "X"},
		"simplicial_boundary": {"add", "zero", "one", "neg", "mul", "d"}, "simplicial_chain_map": {"zero", "one", "add", "mul"},
		"simplicial_homology": {"add", "zero", "one", "neg", "mul", "X"},
		// The homotopy chapter: every notion at a vertex reads the simplicial
		// set, the induced map both.
		"simplicial_sphere": {"X"}, "simplicial_homotopic": {"X"}, "simplicial_homotopy_group": {"X"},
		"simplicial_homotopy_unit": {"X"}, "simplicial_homotopy_mul": {"X"}, "simplicial_homotopy_inv": {"X"},
		"simplicial_homotopy_map": {"X", "Y"},
		// The fibration chapter: the fibration, its fibre and the connecting
		// map read both simplicial sets.
		"left_fibration": {"X", "Y"}, "kan_fibration": {"X", "Y"}, "simplicial_fiber": {"X", "Y"}, "simplicial_fiber_simplices": {"X", "Y"}, "simplicial_connecting_map": {"X", "Y"},
		// The nerve and quasi-category chapters: the spines read the face
		// map, the homotopy category the simplicial set.
		"face_iterate_top": {"d"}, "face_iterate_bottom": {"d"}, "simplex_spine": {"d"}, "spine_map": {"d", "s"}, "segal_composite": {"X"},
		"edge_homotopic": {"X"}, "homotopy_category_morphisms": {"X"}, "edge_class_source": {"d"}, "edge_class_target": {"d"},
		"edge_class_identity": {"X"}, "edge_class_compose": {"X"},
		// The monoid power: `x ^ n` reads the operation and the identity.
		"monoid_pow": {"op", "e"}, "monoid_powers": {"op", "e"},
	}
	scopeSpace := familyScope(t, vec_space.VecDef.Entry().Family())
	for name, binders := range want {
		if _, ok := registry.GetConstMetaManager().LoadConstMeta(core.TermName(name)); !ok {
			t.Errorf("%s is not registered", name)
			continue
		}
		var got []string
		if s := scopeSpace.Syntax.ConstSyntax(name); s != nil {
			got = s.Implicit
		}
		if strings.Join(got, ",") != strings.Join(binders, ",") {
			t.Errorf("%s: implicit binders %v, want %v", name, got, binders)
		}
	}
	// … and the table is complete. Checked entry by entry alone, a
	// constant that registered implicit binders and is absent from the
	// table passes by its absence; the census is the manager's own.
	registry.GetConstMetaManager().RangeConstSyntax(func(name string, s *dsl.ConstSyntax) bool {
		if _, listed := want[name]; len(s.Implicit) > 0 && !listed {
			t.Errorf("%s registered implicit binders %v but this gate's table does not list it", name, s.Implicit)
		}
		return true
	})

	// Under a ring-record binder, short calls use the operation fields.
	// They are the same terms as calls with those fields spelled out.
	prefix := "∀R:ring_ops(A). ∀n:num. ∀u v:(num → A). "
	short := parseIn(t, scopeSpace, prefix+"vec⟨n⟩(u) ∧ vec⟨n⟩(v) ⇒ vec⟨n⟩(vec_add(u, v)) ∧ dot⟨n⟩(u, v) = dot⟨n⟩(v, u) ∧ neutral_elem(vec_add) = vec_zero")
	long := parseIn(t, scopeSpace, prefix+"vec⟨n⟩(R.zero, u) ∧ vec⟨n⟩(R.zero, v) ⇒ vec⟨n⟩(R.zero, vec_add(R.add, u, v)) ∧ dot⟨n⟩(R.add, R.mul, u, v) = dot⟨n⟩(R.add, R.mul, v, u) ∧ neutral_elem(vec_add(R.add)) = vec_zero(R.zero)")
	if short.AlphaKey() != long.AlphaKey() {
		t.Fatalf("law scope: short ≠ explicit\n  %s\n  %s", prop.PrintProp(short), prop.PrintProp(long))
	}

	// euclidean binds R and its normalized fields from real_ring.CommRing.
	eucl := euclidean.VecNormDef.Entry().Family()
	bindings := eucl.ImplicitBindings()
	for _, name := range []string{"R", "add", "zero", "neg", "mul", "one", "sub", "carrier"} {
		if bindings[name] == nil {
			t.Fatalf("euclidean binds no %s: %v", name, bindings)
		}
	}
	if s := ext.PrintTerm(bindings["add"]); s != "real_add" {
		t.Errorf("add ↦ %s", s)
	}
	scopeEucl := familyScope(t, eucl)
	realPrefix := "∀m n:num. ∀f:((num → real) → (num → real)). ∀x:(num → real). "
	shortR := parseIn(t, scopeEucl, realPrefix+"vec_linear(f) ⇒ vec⟨m⟩(x) ⇒ vec_norm⟨n⟩(f(x)) ≤ vec_norm⟨n⟩(vec_scalar_mul(vec_norm⟨m⟩(x), basis_vector(0)))")
	longR := parseIn(t, scopeEucl, realPrefix+"vec_linear(real_add, real_mul, f) ⇒ vec⟨m⟩(real_of_num(0), x) ⇒ vec_norm⟨n⟩(f(x)) ≤ vec_norm⟨n⟩(vec_scalar_mul(real_mul, vec_norm⟨m⟩(x), basis_vector(real_of_num(0), real_of_num(1), 0)))")
	if shortR.AlphaKey() != longR.AlphaKey() {
		t.Fatalf("instance scope: short ≠ explicit\n  %s\n  %s", prop.PrintProp(shortR), prop.PrintProp(longR))
	}
	// Outside any binding nothing is completed: the short form is the
	// ill-typed application it spells, and the explicit form still parses.
	bare := familyScope(t, nat_order.LessEq.Entry().Family())
	res := dsl.ParsePropTextInScope("∀n:num. ∀u:(num → A). vec⟨n⟩(u) ⇒ vec⟨n⟩(u)", bare)
	if len(res.Errors) == 0 {
		t.Fatalf("expected the short form to fail outside any binding, parsed %s", prop.PrintProp(res.Prop))
	}
	parseIn(t, bare, "∀zero:A. ∀n:num. ∀u:(num → A). vec⟨n⟩(zero, u) ⇒ vec⟨n⟩(zero, u)")
	parseIn(t, bare, "∀n:num. ∀u v:(num → real). vec_add(real_add, u, v) = vec_add(real_add, v, u)")

	// The printer serves the chapter's spelling back.
	st := euclidean.BilinearBasisBound.Entry().Statement()
	typed, ok := engine.FormatStatementTypedUnder(st.Prop, eucl)
	if !ok {
		t.Fatal("BilinearBasisBound does not round-trip typed")
	}
	for _, frag := range []string{"vec_bilinear(h)", "vec⟨m⟩(x)"} {
		if !strings.Contains(typed, frag) {
			t.Errorf("served spelling lacks %q: %s", frag, typed)
		}
	}
	if strings.Contains(typed, "real_add") {
		t.Errorf("served spelling still names the component: %s", typed)
	}
	// And it parses back to the member's own statement.
	back := parseIn(t, scopeEucl, typed)
	if back.AlphaKey() != st.Prop.AlphaKey() {
		t.Fatalf("served spelling parses to a different statement: %s", typed)
	}

	// The norm's notation: declared at VecNormDef, read in the chapter's
	// scope, folded back by the printer.
	if s := scopeEucl.Syntax.ConstSyntax("vec_norm"); s == nil || s.Outfix == nil || s.Outfix.Open != "‖" || s.Outfix.Sub != 0 {
		t.Fatalf("norm declares no ‖…‖_n notation: %+v", s)
	}
	normShort := parseIn(t, scopeEucl, "∀n:num. ∀u v:(num → real). ‖vec_add(u, v)‖_n ≤ ‖u‖_n + ‖v‖_n")
	normLong := parseIn(t, scopeEucl, "∀n:num. ∀u v:(num → real). vec_norm⟨n⟩(vec_add(real_add, u, v)) ≤ vec_norm⟨n⟩(u) + vec_norm⟨n⟩(v)")
	if normShort.AlphaKey() != normLong.AlphaKey() {
		t.Fatalf("notation: short ≠ explicit\n  %s\n  %s", prop.PrintProp(normShort), prop.PrintProp(normLong))
	}
	if normShort.AlphaKey() != euclidean.NormTriangle.Entry().Statement().Key() {
		t.Fatalf("the notation spelling is not NormTriangle's own statement")
	}
	tri, ok := engine.FormatStatementTypedUnder(euclidean.NormTriangle.Entry().Statement().Prop, eucl)
	if !ok || !strings.Contains(tri, "‖u + v‖_n ≤ ‖u‖_n + ‖v‖_n") {
		t.Fatalf("served spelling of NormTriangle lacks the notation: %q", tri)
	}

	// The operators: declared at the module's definitions, resolved by
	// operand type at ℝ's components under euclidean, at the ring's
	// under a law; a vector `+` beside a real `+` in one statement.
	opsShort := parseIn(t, scopeEucl, "∀n:num. ∀c:real. ∀u v:(num → real). ‖c • u - v‖_n ≤ c * ‖u‖_n + ‖-v‖_n")
	opsLong := parseIn(t, scopeEucl, "∀n:num. ∀c:real. ∀u v:(num → real). vec_norm⟨n⟩(vec_sub(real_sub, vec_scalar_mul(real_mul, c, u), v)) ≤ real_add(real_mul(c, vec_norm⟨n⟩(u)), vec_norm⟨n⟩(vec_neg(real_neg, v)))")
	if opsShort.AlphaKey() != opsLong.AlphaKey() {
		t.Fatalf("operators: short ≠ explicit\n  %s\n  %s", prop.PrintProp(opsShort), prop.PrintProp(opsLong))
	}
	// The law's own form: the ring record, the hypothesis, then the
	// body's binders (registry.Structure.Statement).
	lawPrefix := "∀R:ring_ops(A). comm_ring(R) ⇒ ∀c:A. ∀u v:(num → A). "
	lawShort := parseIn(t, scopeSpace, lawPrefix+"c • (u + v) = c • u + c • v")
	lawLong := parseIn(t, scopeSpace, lawPrefix+"vec_scalar_mul(R.mul, c, vec_add(R.add, u, v)) = vec_add(R.add, vec_scalar_mul(R.mul, c, u), vec_scalar_mul(R.mul, c, v))")
	if lawShort.AlphaKey() != lawLong.AlphaKey() {
		t.Fatalf("operators under a law: short ≠ explicit\n  %s\n  %s", prop.PrintProp(lawShort), prop.PrintProp(lawLong))
	}
	// A member's Key is its NORMALIZED key (registry.ProofEntry.Key), so
	// a hand parse compares through Normalize.
	normKey := func(p core.Prop) core.PropKey {
		n, _ := prop.Normalize(p)
		return n.AlphaKey()
	}
	// A polymorphic law's registered statement carries the door's own
	// type letters, so it is compared through its served spelling,
	// parsed under the same scope as the hand-written text.
	servedIs := func(entry registry.EntryLike, want core.Prop) {
		t.Helper()
		served, ok := engine.FormatStatementTypedUnder(entry.Entry().Statement().Prop, nil)
		if !ok {
			t.Fatalf("%s does not round-trip typed", entry.Entry().Name)
		}
		if normKey(parseIn(t, scopeSpace, served)) != normKey(want) {
			t.Fatalf("the notation spelling is not %s's own statement: served %q", entry.Entry().Name, served)
		}
	}
	servedIs(vec_space.SmulAddLeft, lawShort)

	// The big operator: `sum` at a real body, the fold at `vec_add` at a
	// vector body, the half-open range as the subscript.
	sumShort := parseIn(t, scopeEucl, "∀n:num. ∀u v:(num → real). ⟪u, v⟫_n = Σ_{i<n} u(i) * v(i)")
	sumLong := parseIn(t, scopeEucl, "∀n:num. ∀u v:(num → real). dot⟨n⟩(real_add, real_mul, u, v) = real_sum({i:num | i < n}, λi:num. u(i) * v(i))")
	if sumShort.AlphaKey() != sumLong.AlphaKey() {
		t.Fatalf("Σ at ℝ: short ≠ explicit\n  %s\n  %s", prop.PrintProp(sumShort), prop.PrintProp(sumLong))
	}
	if normKey(sumShort) != euclidean.DotIsSum.Entry().Statement().Key() {
		t.Fatalf("the Σ spelling is not DotIsSum's own statement: %s", prop.PrintProp(sumShort))
	}
	ringPrefix := "∀R:ring_ops(A). comm_ring(R) ⇒ ∀m:num. ∀x:(num → A). "
	foldShort := parseIn(t, scopeSpace, ringPrefix+"vec⟨m⟩(x) ⇒ x = Σ_{i<m} x(i) • basis_vector(i)")
	foldLong := parseIn(t, scopeSpace, ringPrefix+"vec⟨m⟩(R.zero, x) ⇒ x = iterated_op(vec_add(R.add), {i:num | i < m}, λi:num. vec_scalar_mul(R.mul, x(i), basis_vector(R.zero, R.one, i)))")
	if foldShort.AlphaKey() != foldLong.AlphaKey() {
		t.Fatalf("Σ at vectors: short ≠ explicit\n  %s\n  %s", prop.PrintProp(foldShort), prop.PrintProp(foldLong))
	}
	servedIs(vec_space.BasisExpansion, foldShort)

	// The printers fold all of it back.
	for _, want := range []struct {
		entry  registry.EntryLike
		family *registry.Family
		frag   string
	}{
		{euclidean.CauchySchwarz, eucl, "⟪u, v⟫_n ≤ ‖u‖_n * ‖v‖_n"},
		{euclidean.NormSmul, eucl, "‖c • u‖_n = |c| * ‖u‖_n"},
		{euclidean.DotIsSum, eucl, "⟪u, v⟫_n = Σ_{i<n} u(i) * v(i)"},
		{vec_space.BasisExpansion, nil, "x = Σ_{i<m} x(i) • basis_vector(i)"},
		{vec_space.SmulAddRight, nil, "(c + d) • u = c • u + d • u"},
		{vec_space.IterateAt, nil, "(Σ_{i∈s} F(i))(j) = Σ_{i∈s} F(i, j)"},
		{vec_space.SubAddNeg, nil, "u - v = u + -v"},
	} {
		served, ok := engine.FormatStatementTypedUnder(want.entry.Entry().Statement().Prop, want.family)
		if !ok || !strings.Contains(served, want.frag) {
			t.Errorf("served spelling of %s lacks %q: %q", want.entry.Entry().Name, want.frag, served)
		}
	}
}

func TestImplicitArgs_SecondInstance(t *testing.T) {
	// lattice binds the components to ℤ's, read off int_real_lift.CommRing:
	// the second tenant of WithInstance, and the one whose statements cross
	// into ℝⁿ. There the real components are spelled in full, and under ℤ's
	// binding the text can only mean that — the leading argument's type
	// says so (ext/dsl/implicit.go, leadsWithComponent).
	lat := lattice.VecOfIntDef.Entry().Family()
	bindings := lat.ImplicitBindings()
	if s := ext.PrintTerm(bindings["add"]); s != "int_add" {
		t.Fatalf("add ↦ %s", s)
	}
	scopeLat := familyScope(t, lat)
	bare := familyScope(t, nat_order.LessEq.Entry().Family())
	for _, tc := range []struct{ mixed, explicit string }{
		{"∀n:num. ∀u v:(num → int). real_of_int(dot⟨n⟩(u, v)) = dot⟨n⟩(real_add, real_mul, vec_of_int(u), vec_of_int(v))",
			"∀n:num. ∀u v:(num → int). real_of_int(dot⟨n⟩(int_add, int_mul, u, v)) = dot⟨n⟩(real_add, real_mul, vec_of_int(u), vec_of_int(v))"},
		{"∀n:num. ∀u:(num → int). vec⟨n⟩(u) ⇔ vec⟨n⟩(real_of_num(0), vec_of_int(u))",
			"∀n:num. ∀u:(num → int). vec⟨n⟩(int_of_num(0), u) ⇔ vec⟨n⟩(real_of_num(0), vec_of_int(u))"},
		{"vec_of_int(vec_zero) = vec_zero(real_of_num(0))",
			"vec_of_int(vec_zero(int_of_num(0))) = vec_zero(real_of_num(0))"},
		{"∀u v:(num → int). vec_of_int(vec_add(u, v)) = vec_add(real_add, vec_of_int(u), vec_of_int(v))",
			"∀u v:(num → int). vec_of_int(vec_add(int_add, u, v)) = vec_add(real_add, vec_of_int(u), vec_of_int(v))"},
	} {
		mixed := parseIn(t, scopeLat, tc.mixed)
		explicit := parseIn(t, bare, tc.explicit)
		if mixed.AlphaKey() != explicit.AlphaKey() {
			t.Fatalf("instance scope: mixed ≠ explicit\n  %s\n  %s", prop.PrintProp(mixed), prop.PrintProp(explicit))
		}
		// The served spelling is short on the ℤ side, explicit on the ℝ
		// side, and parses back to the statement.
		typed, ok := engine.FormatStatementTypedUnder(mixed, lat)
		if !ok {
			t.Fatalf("%q: no served spelling", tc.mixed)
		}
		t.Logf("served: %s", typed)
		if strings.Contains(typed, "int_add") || strings.Contains(typed, "int_mul") {
			t.Errorf("served spelling names the bound components: %s", typed)
		}
		if back := parseIn(t, scopeLat, typed); back.AlphaKey() != mixed.AlphaKey() {
			t.Fatalf("served spelling parses to a different statement: %s", typed)
		}
	}
	// Where the type decides nothing the bound instance stands.
	short := parseIn(t, scopeLat, "∀u:(num → int). vec_zero(0) = u(0)")
	long := parseIn(t, bare, "∀u:(num → int). vec_zero(int_of_num(0), 0) = u(0)")
	if short.AlphaKey() != long.AlphaKey() {
		t.Fatalf("numeral index: short ≠ explicit\n  %s\n  %s", prop.PrintProp(short), prop.PrintProp(long))
	}
}

// Algebra structures bind one record subject. Record-taking definitions
// keep that argument explicit even when the subject is already in scope.
func TestImplicitArgs_RecordAlgebraChapters(t *testing.T) {
	scope := engine.StatementDoorScope(nil)
	for _, row := range []struct{ name, short, explicit string }{
		{
			"group record subject",
			"∀G:group_on(A). ∀h:set(A). subgroup(G, h) ⇒ h ⊆ G.carrier",
			"∀G:group_ops(A). group_on(G) ⇒ ∀h:set(A). subgroup(G, h) ⇒ h ⊆ group_carrier(G)",
		},
		{
			"abelian group record subject",
			"∀G:abelian_group_on(A). G.one ∈ G.carrier",
			"∀G:group_ops(A). abelian_group_on(G) ⇒ group_one(G) ∈ group_carrier(G)",
		},
		{
			"ring record subject",
			"∀R:comm_ring_on(A). ∀I:set(A). ring_ideal(R, I) ⇒ R.zero ∈ I",
			"∀R:ring_ops(A). comm_ring_on(R) ⇒ ∀I:set(A). ring_ideal(R, I) ⇒ ring_zero(R) ∈ I",
		},
		{
			"field record subject",
			"∀F:field_on(A). ∀K:set(A). subfield(F, K) ⇒ K ⊆ F.carrier ∧ comm_ring_on(field_ring(F))",
			"∀F:field_ops(A). field_on(F) ⇒ ∀K:set(A). subfield(F, K) ⇒ K ⊆ field_carrier(F) ∧ comm_ring_on(field_ring(F))",
		},
		{
			"distinct ring records",
			"∀R S:ring_ops(A). ∀x:A. R.add(R.zero, x) = S.add(S.zero, x)",
			"∀R S:ring_ops(A). ∀x:A. ring_add(R, ring_zero(R), x) = ring_add(S, ring_zero(S), x)",
		},
	} {
		t.Run("roundtrip/"+row.name, func(t *testing.T) {
			short := parseIn(t, scope, row.short)
			explicit := parseIn(t, scope, row.explicit)
			if short.AlphaKey() != explicit.AlphaKey() {
				t.Fatalf("record spellings differ:\n%s\n%s", prop.PrintProp(short), prop.PrintProp(explicit))
			}
			typed, ok := engine.FormatStatementTypedUnder(explicit, nil)
			if !ok {
				t.Fatal("the record statement has no typed roundtrip spelling")
			}
			if back := parseIn(t, scope, typed); back.AlphaKey() != explicit.AlphaKey() {
				t.Fatalf("served spelling changes the record statement: %s", typed)
			}
		})
	}
	t.Run("explicit partial operation beside a field", func(t *testing.T) {
		text := "∀F:field_ops(A). ∀H:set(permutation(A)). group_on(mk_group(set_mul(permutation_compose), H, set_inv(permutation_inverse), left_cosets(permutation_compose, H, H)))"
		statement := parseIn(t, scope, text)
		body := statement.Conclusion()
		for abs := ext.MatchesFORALL(body); !abs.IsZero(); abs = ext.MatchesFORALL(body) {
			body = abs.Body()
		}
		_, subjects := ext.MatchesApply(body)
		if len(subjects) != 1 {
			t.Fatal("the group predicate does not take one record")
		}
		_, fields := ext.MatchesApply(subjects[0])
		if len(fields) != 4 {
			t.Fatal("the group constructor does not have four fields")
		}
		for _, row := range []struct {
			term            core.Term
			head, operation string
		}{
			{fields[0], "set_mul", "permutation_compose"},
			{fields[2], "set_inv", "permutation_inverse"},
		} {
			head, args := ext.MatchesApply(row.term)
			constant, isConst := head.AsConst()
			if !isConst || string(constant.Name()) != row.head || len(args) != 1 {
				t.Fatalf("explicit partial operation was completed with ambient fields: %s", ext.PrintTerm(row.term))
			}
			operation, isConst := args[0].AsConst()
			if !isConst || string(operation.Name()) != row.operation {
				t.Fatalf("the operation supplied to %s changed: %s", row.head, ext.PrintTerm(args[0]))
			}
		}
		typed, ok := engine.FormatStatementTypedUnder(statement, nil)
		if !ok {
			t.Fatal("the partial operation has no typed roundtrip spelling")
		}
		if back := parseIn(t, scope, typed); back.AlphaKey() != statement.AlphaKey() {
			t.Fatalf("served spelling changes the partial operation: %s", typed)
		}
	})
	for _, row := range []struct{ name, prefix, omitted, explicit string }{
		{"subgroup", "∀G:group_ops(A). ∀h:set(A). ", "subgroup(h)", "subgroup(G, h)"},
		{"ring ideal", "∀R:ring_ops(A). ∀I:set(A). ", "ring_ideal(I)", "ring_ideal(R, I)"},
		{"ideal span", "∀R:ring_ops(A). ∀I:set(A). ", "ideal_span(I) = I", "ideal_span(R, I) = I"},
		{"subfield", "∀F:field_ops(A). ∀K:set(A). ", "subfield(K)", "subfield(F, K)"},
		{"polynomial image", "∀R:ring_ops(A). ∀K:set(A). ∀a:A. ", "polynomial_image(K, a) = K", "polynomial_image(R, K, a) = K"},
		{"field trace", "∀F:field_ops(A). ∀K:set(A). ∀a:A. ", "field_trace(K, a) = a", "field_trace(F, K, a) = a"},
	} {
		t.Run("explicit_record/"+row.name, func(t *testing.T) {
			parseIn(t, scope, row.prefix+row.explicit)
			res := dsl.ParsePropTextInScope(row.prefix+row.omitted, scope)
			if len(res.Errors) == 0 {
				t.Fatalf("omitted record argument was silently completed: %s", prop.PrintProp(res.Prop))
			}
		})
	}
}

// Record-based homological definitions expose their records directly. The
// syntax table and the statement door agree on implicit rings, record
// projections, structure subjects and the letters of whole sequences.
func TestImplicitArgs_RecordHomologicalChapters(t *testing.T) {
	mgr := registry.GetConstMetaManager()
	for _, name := range []string{
		"module_on", "submodule", "module_span", "module_independent", "module_basis", "finite_dimensional", "module_dim",
		"tensor_relations", "tensor_product", "tensor", "tensor_module",
		"module_homomorphism", "module_isomorphism", "module_isomorphic", "short_exact_modules",
		"chain_complex", "short_exact_complexes", "cycles", "boundaries", "homology", "homology_map", "connecting_hom",
		"free_resolution", "hom_set", "tensor_boundary", "hom_coboundary", "finite_supp_map", "tor", "ext",
		"cochain_complex", "short_exact_cochain_complexes", "cocycles", "coboundaries", "cohomology", "cohomology_map", "coconnecting_hom",
		"double_complex",
	} {
		t.Run("explicit_records/"+name, func(t *testing.T) {
			if _, ok := mgr.LoadConstMeta(core.TermName(name)); !ok {
				t.Fatalf("%s is not registered", name)
			}
			if syntax := mgr.ConstSyntax(name); syntax != nil && len(syntax.Implicit) != 0 {
				t.Fatalf("%s has implicit binders %v; its record arguments are explicit", name, syntax.Implicit)
			}
		})
	}
	for _, row := range []struct {
		name, params, letter string
		subject              int
	}{
		{"module_homomorphism", "R,M,N,f", "", 3},
		{"short_exact_modules", "R,N',N,N'',i,p", "S", -1},
		{"chain_complex", "R,P", "", 1},
		{"cochain_complex", "R,Q", "", 1},
		{"short_exact_complexes", "R,P',P,P'',i,p", "S", -1},
		{"short_exact_cochain_complexes", "R,Q',Q,Q'',i,p", "S", -1},
		{"free_resolution", "R,M,S,d,eps", "", 2},
		{"double_complex", "R,V,D,h,v", "", 2},
	} {
		t.Run("structure/"+row.name, func(t *testing.T) {
			syntax := mgr.ConstSyntax(row.name)
			if syntax == nil || !syntax.StructurePredicate || syntax.Bundle == nil || !syntax.Bundle.Structure {
				t.Fatalf("%s is not registered as a structure", row.name)
			}
			bundle := syntax.Bundle
			var params []string
			for _, param := range bundle.Params {
				params = append(params, param.Name)
			}
			if strings.Join(params, ",") != row.params || bundle.Subject != row.subject || bundle.Letter != row.letter {
				t.Fatalf("%s: parameters %v, subject %d, letter %q; want %s, %d, %q", row.name, params, bundle.Subject, bundle.Letter, row.params, row.subject, row.letter)
			}
		})
	}

	scope := engine.StatementDoorScope(nil)
	for _, row := range []struct {
		name, short, explicit, folded string
	}{
		{
			"distinct record fields",
			"∀R:ring_ops(A). ∀M N:module_ops(A, B). ∀c:A. ∀x:B. c ∈ R.carrier ∧ x ∈ M.carrier ⇒ M.add(M.smul(R.one, x), N.zero) = N.add(M.zero, N.neg(x))",
			"∀R:ring_ops(A). ∀M N:module_ops(A, B). ∀c:A. ∀x:B. c ∈ ring_carrier(R) ∧ x ∈ mod_carrier(M) ⇒ mod_add(M, mod_smul(M, ring_one(R), x), mod_zero(N)) = mod_add(N, mod_zero(M), mod_neg(N, x))",
			"",
		},
		{
			"homomorphism subject",
			"∀f:module_homomorphism(A, B, C). ∀x:B. x ∈ M.carrier ⇒ f(x) ∈ N.carrier",
			"∀R:ring_ops(A). ∀M:module_ops(A, B). ∀N:module_ops(A, C). ∀f:(B → C). module_homomorphism(R, M, N, f) ⇒ ∀x:B. x ∈ mod_carrier(M) ⇒ f(x) ∈ mod_carrier(N)",
			"∀f:module_homomorphism(",
		},
		{
			"short exact modules letter",
			"∀S:short_exact_modules(A, B, C, D). ∀x:B. x ∈ N'.carrier ⇒ S.p(S.i(x)) = N''.zero",
			"∀R:ring_ops(A). ∀N':module_ops(A, B). ∀N:module_ops(A, C). ∀N'':module_ops(A, D). ∀i:(B → C). ∀p:(C → D). short_exact_modules(R, N', N, N'', i, p) ⇒ ∀x:B. x ∈ mod_carrier(N') ⇒ p(i(x)) = mod_zero(N'')",
			"∀S:short_exact_modules(",
		},
		{
			"chain complex subject and fields",
			"∀P:chain_complex(A, B). ∀n:num. ∀x:B. x ∈ P.terms(n + 2) ⇒ P.d(n + 1, P.d(n + 2, x)) = P.zero",
			"∀R:ring_ops(A). ∀P:complex_ops(A, B). chain_complex(R, P) ⇒ ∀n:num. ∀x:B. x ∈ complex_ops_terms(P, n + 2) ⇒ complex_ops_differential(P, n + 1, complex_ops_differential(P, n + 2, x)) = complex_ops_zero(P)",
			"∀P:chain_complex(",
		},
		{
			"cochain complex subject and fields",
			"∀Q:cochain_complex(A, B). ∀n:num. ∀x:B. x ∈ Q.terms(n) ⇒ Q.d(n + 1, Q.d(n, x)) = Q.zero",
			"∀R:ring_ops(A). ∀Q:complex_ops(A, B). cochain_complex(R, Q) ⇒ ∀n:num. ∀x:B. x ∈ complex_ops_terms(Q, n) ⇒ complex_ops_differential(Q, n + 1, complex_ops_differential(Q, n, x)) = complex_ops_zero(Q)",
			"∀Q:cochain_complex(",
		},
		{
			"chain map and homotopy implicit ring",
			"∀R:ring_ops(A). ∀P:complex_ops(A, B). ∀Q:complex_ops(A, C). ∀f g h:(num → B → C). chain_homotopy(P, Q, f, g, h) ⇒ chain_map(P, Q, f)",
			"∀R:ring_ops(A). ∀P:complex_ops(A, B). ∀Q:complex_ops(A, C). ∀f g h:(num → B → C). chain_homotopy(R, P, Q, f, g, h) ⇒ chain_map(R, P, Q, f)",
			"",
		},
		{
			"cochain map and homotopy implicit ring",
			"∀R:ring_ops(A). ∀P:complex_ops(A, B). ∀Q:complex_ops(A, C). ∀f g h:(num → B → C). cochain_homotopy(P, Q, f, g, h) ⇒ cochain_map(P, Q, f)",
			"∀R:ring_ops(A). ∀P:complex_ops(A, B). ∀Q:complex_ops(A, C). ∀f g h:(num → B → C). cochain_homotopy(R, P, Q, f, g, h) ⇒ cochain_map(R, P, Q, f)",
			"",
		},
		{
			"short exact chain complexes letter",
			"∀S:short_exact_complexes(A, B, C, D). ∀n:num. ∀x:B. x ∈ P'.terms(n) ⇒ S.p(n, S.i(n, x)) = P''.zero",
			"∀R:ring_ops(A). ∀P':complex_ops(A, B). ∀P:complex_ops(A, C). ∀P'':complex_ops(A, D). ∀i:(num → B → C). ∀p:(num → C → D). short_exact_complexes(R, P', P, P'', i, p) ⇒ ∀n:num. ∀x:B. x ∈ complex_ops_terms(P', n) ⇒ p(n, i(n, x)) = complex_ops_zero(P'')",
			"∀S:short_exact_complexes(",
		},
		{
			"short exact cochain complexes letter",
			"∀S:short_exact_cochain_complexes(A, B, C, D). ∀n:num. ∀x:B. x ∈ Q'.terms(n) ⇒ S.p(n, S.i(n, x)) = Q''.zero",
			"∀R:ring_ops(A). ∀Q':complex_ops(A, B). ∀Q:complex_ops(A, C). ∀Q'':complex_ops(A, D). ∀i:(num → B → C). ∀p:(num → C → D). short_exact_cochain_complexes(R, Q', Q, Q'', i, p) ⇒ ∀n:num. ∀x:B. x ∈ complex_ops_terms(Q', n) ⇒ p(n, i(n, x)) = complex_ops_zero(Q'')",
			"∀S:short_exact_cochain_complexes(",
		},
		{
			"free resolution subject",
			"∀S:free_resolution(A, B, I). ∀u:(I → A). u ∈ finite_supp(R.zero, R.carrier, S(0)) ⇒ S.eps(u) ∈ M.carrier",
			"∀R:ring_ops(A). ∀M:module_ops(A, B). ∀S:(num → set(I)). ∀d:(num → (I → A) → I → A). ∀eps:((I → A) → B). free_resolution(R, M, S, d, eps) ⇒ ∀u:(I → A). u ∈ finite_supp(ring_zero(R), ring_carrier(R), S(0)) ⇒ eps(u) ∈ mod_carrier(M)",
			"∀S:free_resolution(",
		},
		{
			"double complex subject",
			"∀D:double_complex(A, B). ∀p q:num. ∀x:B. x ∈ D(p + 1, q + 1) ⇒ D.h(p + 1, q, D.v(p + 1, q + 1, x)) = D.v(p, q + 1, D.h(p + 1, q + 1, x))",
			"∀R:ring_ops(A). ∀V:module_ops(A, B). ∀D:(num → num → set(B)). ∀h v:(num → num → B → B). double_complex(R, V, D, h, v) ⇒ ∀p q:num. ∀x:B. x ∈ D(p + 1, q + 1) ⇒ h(p + 1, q, v(p + 1, q + 1, x)) = v(p, q + 1, h(p + 1, q + 1, x))",
			"∀D:double_complex(",
		},
	} {
		t.Run("roundtrip/"+row.name, func(t *testing.T) {
			short := parseIn(t, scope, row.short)
			explicit := parseIn(t, scope, row.explicit)
			if short.AlphaKey() != explicit.AlphaKey() {
				t.Fatalf("short and explicit spellings differ:\n%s\n%s", prop.PrintProp(short), prop.PrintProp(explicit))
			}
			typed, ok := engine.FormatStatementTypedUnder(explicit, nil)
			if !ok {
				t.Fatal("the explicit statement has no typed roundtrip spelling")
			}
			if row.folded != "" && !strings.Contains(typed, row.folded) {
				t.Errorf("served spelling lacks %q: %s", row.folded, typed)
			}
			if back := parseIn(t, scope, typed); back.AlphaKey() != explicit.AlphaKey() {
				t.Fatalf("served spelling changes the statement: %s", typed)
			}
		})
	}
}
