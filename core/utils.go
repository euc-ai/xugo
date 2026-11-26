package core

import "github.com/euc-ai/xugo/utils"

type (
	VarTypePredicate = utils.Predicate[VarType]
	VarPredicate     = utils.Predicate[VarTerm]
	PropPredicate    = utils.Predicate[Prop]
)

const (
	_TYPE_KEY_HASH_THRES = 128

	_VAR_TYPE_KEY_PREFIX       = "type_var_"
	_COMPOSITE_TYPE_KEY_PREFIX = "type_"
	_VAR_TERM_KEY_PREFIX       = "var_"
	_CONST_TERM_KEY_PREFIX     = "const_"
	_APPLIED_TERM_KEY_PREFIX   = "apply_"
	_ABS_TERM_KEY_PREFIX       = "abs_"
	_PROP_KEY_PREFIX           = "prop_"
)
