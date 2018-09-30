package geneticalgorithm.operator;

/**
 * This class contains all the possible mutations identifiers
 * @author fmolina
 */
public class DynAlloySpecLearnerMutations {

	// Common mutations
	public static final String TO_TRUE = "ToTrue";
	
	// Constant mutations
	public static final String PREVIOUS = "Previous";
	
	// Cardinality expressions mutations
	public static final String ADD_ONE = "AddOne";
	public static final String SUB_ONE = "SubOne";
	
	// Unary expressions mutations
	public static final String SOME = "Some";
	public static final String EMPTYNESS = "Emptyness";
	
	// Binary expressions mutations
	public static final String JOIN_COMPATIBLE_EXPR = "JoinCompatibleExpr";
	
	// Unary and binary expressions mutations
	public static final String NEGATE = "Negate";
	
	// Quantified expressions mutations
	public static final String NEGATE_BODY = "NegateBody";
	public static final String TO_ALL = "ToAll";
	public static final String TO_SOME = "ToSome";
	public static final String INTERSECTION_NULL = "IntersectionNull";
	
	// Quantified expressions which bodies predicates with values
	public static final String REPLACE_VALUE = "ReplaceValue";
	public static final String NEGATE_RIGHT_EQUALITY = "NegateRightEquality";
	
	// Quantified expressions which bodies predicates with int values
	public static final String OP_NOT_EQ = "OperatorNotEqual";
	public static final String OP_LTE = "OperatorLessThanOrEqual";
	public static final String OP_LT = "OperatorLessThan";
	public static final String OP_GTE = "OperatorGreaterThanOrEqual";
	public static final String OP_GT = "OperatorGreaterThan";
}
