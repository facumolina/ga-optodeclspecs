package geneticalgorithm.chromosome;

import java.util.List;
import java.util.Random;

import org.jgap.BaseGene;
import org.jgap.Configuration;
import org.jgap.Gene;
import org.jgap.InvalidConfigurationException;
import org.jgap.RandomGenerator;
import org.jgap.UnsupportedRepresentationException;

import geneticalgorithm.operator.DynAlloySpecLearnerMutations;
import rfm.dynalloy.Err;
import rfm.dynalloyCompiler.ast.Expr;
import rfm.dynalloyCompiler.ast.ExprBinary;
import rfm.dynalloyCompiler.ast.ExprCall;
import rfm.dynalloyCompiler.ast.ExprConstant;
import rfm.dynalloyCompiler.ast.ExprList;
import rfm.dynalloyCompiler.ast.ExprQt;
import rfm.dynalloyCompiler.ast.ExprUnary;
import rfm.dynalloyCompiler.ast.Sig.PrimSig;
import utils.DataStructureInformation;
import utils.DynAlloyExpressionsUtils;
import rfm.dynalloyCompiler.ast.Type;

/**
 * This class represents a gene. A gene is the basic structure used to build chromosomes.
 * A gene basically contains a value, which will contain the Alloy expression represented
 * by the gene.
 * @author fmolina
 */
public class ExprGene extends BaseGene implements Gene, java.io.Serializable {

	private ExprGeneValue value;
	private DataStructureInformation dsi;
	private int amountOfGenesInChromosome = 0;
	private boolean isPartOfSolution;
	
	/**
	 * Default constructor with default value (true)
	 * @param a_conf
	 * @throws InvalidConfigurationException
	 */
	public ExprGene(Configuration a_conf,DataStructureInformation dsi) throws InvalidConfigurationException {
        super(a_conf);
		this.value = new ExprGeneValue();
		this.dsi = dsi;
		isPartOfSolution = false;
	}
	
	/**
	 * Constructor with a given value
	 * @param a_conf
	 * @param expression
	 * @throws InvalidConfigurationException
	 */
	public ExprGene(Configuration a_conf, ExprGeneValue value,DataStructureInformation dsi) throws InvalidConfigurationException {
        super(a_conf);
		this.value = value;
		this.dsi = dsi;
		isPartOfSolution = false;
	}

	/**
	 * Get the Data Structure Information 
	 */
	public DataStructureInformation getDataStructureInformation() {
		return dsi;
	}
	
	/**
	 * Get the amount of genes in the chromosome that contains this gene
	 */
	public int getAmountOfGenesInChromosome() {
		return amountOfGenesInChromosome;
	}
	
	/**
	 * Set the amount of genes in the chromosome that contains this gene
	 */
	public void setAmountOfGenesInChromosome(int n) {
		amountOfGenesInChromosome = n;
	}
	
	/**
	 * Returns true if the gene is part of a solution
	 */
	public boolean isPartOfSolution() {
		return isPartOfSolution;
	}
	
	/**
	 * Set is part of solution
	 */
	public void setIsPartOfSolution(boolean partOfSolution) {
		this.isPartOfSolution = partOfSolution;
	}
	
	@Override
	protected Gene newGeneInternal() {
		try {
			return new ExprGene(getConfiguration(),this.value.clone(),this.dsi);
		} catch (InvalidConfigurationException ex) {
			throw new IllegalStateException(ex.getMessage());
		}
	}
	
	/**
	 * Sets the value of the gene to the newExprGene
	 */
	public void setAllele( Object newExprGeneValue ){
		value = (ExprGeneValue) newExprGeneValue;
	}

	/**
	 * Update the previous expression 
	 * @param expression2
	 */
	private void updatePreviousExpression(ExprGeneValue newValue) {
		if (this.value.getPrevious()==null||!newValue.getExpression().equals(ExprConstant.TRUE)) {
			this.value.setPrevious(newValue);
		}
	}
	
	/**
	 * Retrieves the value represented by this gene
	 */
	public Object getAllele() {
		return value;
	}
	

	/**
	 * Set value
	 */
	public void setValue(ExprGeneValue newValue) {
		updatePreviousExpression(value.clone());
		value = newValue;
	}
	
	/**
	 * Sets the value of this gene to a random legal value
	 */
	public void setToRandomValue(RandomGenerator a_numberGenerator) {
		value = new ExprGeneValue();
	}
	
	/**
	 * Retrieves a string representation of the value of this Gene instance
	 */
	public String getPersistentRepresentation()
			throws UnsupportedOperationException {
		return value.toString();
	}

	/**
	 * Sets the value and internal state of this Gene from the string
     * representation returned by a previous invocation of the
     * getPersistentRepresentation() method.
	 */
	public void setValueFromPersistentRepresentation(String a_representation)
			throws UnsupportedOperationException,
			UnsupportedRepresentationException {
		// TODO Auto-generated method stub
	}
	
	/**
	 * Compares this Gene with the specified object for order.
	 */
	public int compareTo(Object otherExprGene) {
		return value.toString().compareTo(((ExprGene)otherExprGene).getValue().toString());
	}
	
	/**
	 * Gets the value
	 */
	public ExprGeneValue getValue() {
		return value;
	}
	
	/**
	 * Apply mutation according to the gene type
	 */
	public void applyMutation(int index, double a_percentage) {
		try {
			updatePreviousExpression(value.clone());
			switch (value.getGeneType()) {
				case CARDINALITY:
					applyCardinalityMutation();
					break;
				case CONSTANT: 
					applyConstantMutation();
					break;
				case EMPTYNESS:
					applyEmptynessMutation();
					break;
				case EQUALITY:	
					applyEqualityMutation();
					break;
				case NEGATION: 
					applyNegationMutation();
					break;
				case INCLUSION: 
					applyInclusionMutation();
					break;
				case FORALL: 
					applyForAllMutation();
					break;
				case FORALL_VAR_VAR:
					applyForAllVarVarMutation();
					break;
				case FORALL_VAR_VALUE_VAR_VALUE:
					applyForAllVarValueVarValueMutation();
					break;
				case FORALL_VAR_VALUE_VAR_VALUE_INT_COMPARISON:
					applyForAllVarValueVarValueIntComparisonMutation();
					break;
				case FORALL_VAR_VALUES_DOUBLE_INT_COMPARISON:
					applyForAllVarValuesDoubleIntComparisonMutation();
					break;
				case FORALL_VAR_VALUES_DOUBLE_QT_INT_COMPARISON:
					applyForAllVarValuesDoubleQuantificationIntComparisonMutation();
					break;
				case FORALL_VAR_SET:
					applyForAllVarSetMutation();
					break;
				case FORALL_SET_SET:
					applyForAllSetSetMutation();
					break;
				case SOME: 
					applySomeMutation();
					break;
				case SOME_VAR_VAR:
					applySomeVarVarMutation();
					break;
				case SOME_VAR_SET:
					applySomeVarSetMutation();
					break;
				case SOME_SET_SET:
					applySomeSetSetMutation();
					break;
				case SOMEQT:
					applySomeQuantifierMutation();
					break;
				case NO:
					applyNoMutation();
					break;
				default: 
					applyDefaultMutation();
			}
		} catch (Exception e) {
			e.printStackTrace();
		}
	}

	/**
	 * Apply some quantifier mutation
	 */
	private void applySomeQuantifierMutation() throws Err {
		String mutationToApply = getSomeApplicableMutation();
		ExprQt someExpr = (ExprQt)value.getExpression();
		switch (mutationToApply) {
			case DynAlloySpecLearnerMutations.NEGATE_BODY:
				// Negate the body
				Expr negatedBody = DynAlloyExpressionsUtils.negateExpression(someExpr.sub);
				value.setExpression(ExprQt.Op.SOME.make(null, null, someExpr.decls, negatedBody),false);
				break;
			case DynAlloySpecLearnerMutations.TO_ALL:
				// Create a new expression with the all quantifier
				value.setExpression(ExprQt.Op.ALL.make(null, null, someExpr.decls, someExpr.sub),false);
				value.setGeneType(ExprGeneType.FORALL_VAR_VAR);
				break;
			case DynAlloySpecLearnerMutations.TO_TRUE:
				// Set the expression to true
				value.setExpression(ExprConstant.TRUE,false);
				value.setGeneType(ExprGeneType.CONSTANT);
				break;
			default:
				break;
		}
	}

	/**
	 * Apply mutation when the gene expression is a quantification with the operator some
	 * and the body is a predicate about two variables
	 */
	private void applySomeVarVarMutation() throws Err {
		String mutationToApply = getSomeApplicableMutation();
		ExprQt someExpr = (ExprQt)value.getExpression();
		switch(mutationToApply) {
			case DynAlloySpecLearnerMutations.NEGATE_BODY:
				Expr negatedBody = DynAlloyExpressionsUtils.negateExpression(someExpr.sub);
				value.setExpression(ExprQt.Op.SOME.make(null, null, someExpr.decls, negatedBody),false);
				break;
			case DynAlloySpecLearnerMutations.TO_ALL:
				// Create a new expression with the all quantifier
				value.setExpression(ExprQt.Op.ALL.make(null, null, someExpr.decls, someExpr.sub),false);
				value.setGeneType(ExprGeneType.FORALL_VAR_VAR);
				break;
			case DynAlloySpecLearnerMutations.TO_TRUE:
				// Set the expression to true
				value.setExpression(ExprConstant.TRUE,false);
				value.setGeneType(ExprGeneType.CONSTANT);
				break;
			default:
				break;
		}
	}
	
	/**
	 * Apply mutation when the gene expression is a quantification with the operator some
	 * and the body is a predicate about two variables
	 */
	private void applySomeVarSetMutation() throws Err {
		String mutationToApply = getSomeApplicableMutation();
		if (mutationToApply.equals("NegateBody")) {
			ExprQt someExpr = (ExprQt)value.getExpression();
			Expr negatedBody = DynAlloyExpressionsUtils.negateExpression(someExpr.sub);
			value.setExpression(ExprQt.Op.SOME.make(null, null, someExpr.decls, negatedBody),false);
		} else {
			if (mutationToApply.equals("ToAll")) {
				// Create a new expression with the all quantifier
				ExprQt someExpr = (ExprQt)value.getExpression();
				value.setExpression(ExprQt.Op.ALL.make(null, null, someExpr.decls, someExpr.sub),false);
				value.setGeneType(ExprGeneType.FORALL_VAR_SET);
			} else {
				// Set the expression to true
				value.setExpression(ExprConstant.TRUE,false);
				value.setGeneType(ExprGeneType.CONSTANT);
			}
		}
	}
	
	/**
	 * Apply mutation when the gene expression is a quantification with the operator some
	 * and the body is a predicate about two sets
	 */
	private void applySomeSetSetMutation() throws Err {
		String mutationToApply = getSomeApplicableMutation();
		ExprQt someExpr = (ExprQt)value.getExpression();
		switch (mutationToApply) {
			case DynAlloySpecLearnerMutations.NEGATE_BODY:
				// Negate the body
				Expr negatedBody = DynAlloyExpressionsUtils.negateExpression(someExpr.sub);
				value.setExpression(ExprQt.Op.ALL.make(null, null, someExpr.decls, negatedBody),false);
				break;
			case DynAlloySpecLearnerMutations.INTERSECTION_NULL:
				// Take the set s1 and s2 from the body of the expression, and create
				// the body s1 & s2 in Null
				System.out.println("INTERSECTION IN NULL GENERATED");
				ExprBinary expressionWithSets;
				if (someExpr.sub instanceof ExprUnary) {
					expressionWithSets = (ExprBinary)((ExprUnary)someExpr.sub).sub;
				} else {
					expressionWithSets = (ExprBinary)someExpr.sub;
				}
				Expr intersection = ExprBinary.Op.INTERSECT.make(null, null, expressionWithSets.left, expressionWithSets.right);
				Expr intersectionNull = ExprBinary.Op.IN.make(null, null, intersection, DataStructureInformation.nullSig);
				value.setExpression(ExprQt.Op.ALL.make(null, null, someExpr.decls, intersectionNull),false);
				break;
			case DynAlloySpecLearnerMutations.TO_ALL:
				// Create a new expression with the all quantifier
				value.setExpression(ExprQt.Op.ALL.make(null, null, someExpr.decls, someExpr.sub),false);
				value.setGeneType(ExprGeneType.FORALL_SET_SET);
				break;
			case DynAlloySpecLearnerMutations.TO_TRUE:
				// Set the expression to true
				value.setExpression(ExprConstant.TRUE,false);
				value.setGeneType(ExprGeneType.CONSTANT);
				break;
			default:
		}
	}
	
	/**
	 * Apply emptyness mutation
	 */
	private void applyEmptynessMutation() {
		String mutationToApply = getSomeApplicableMutation();
		if (mutationToApply.equals("Some")) {
			// Change some expr to no expr
			ExprUnary emptyExpr = (ExprUnary)value.getExpression();
			value.setExpression(ExprUnary.Op.SOME.make(null, emptyExpr.sub),false);
			value.setGeneType(ExprGeneType.SOME);
		} else {
			// Set the expression to true
			value.setExpression(ExprConstant.TRUE,false);
			value.setGeneType(ExprGeneType.CONSTANT);
		}
	}

	/**
	 * Apply default mutation
	 */
	private void applyDefaultMutation() {
		// TODO Auto-generated method stub
	}

	/**
	 * Apply mutation when the gene expression is some
	 */
	private void applySomeMutation() {
		String mutationToApply = getSomeApplicableMutation();
		if (mutationToApply.equals("Emptyness")) {
			// Change some expr to no expr
			ExprUnary someExpr = (ExprUnary)value.getExpression();
			value.setExpression(ExprUnary.Op.NO.make(null, someExpr.sub),false);
			value.setGeneType(ExprGeneType.EMPTYNESS);
		} else {
			// Set the expression to true
			value.setExpression(ExprConstant.TRUE,false);
			value.setGeneType(ExprGeneType.CONSTANT);
		}
	}

	/**
	 * Apply mutation when the gene expression is no and set the expression to some
	 */
	private void applyNoMutation() {
		String mutationToApply = getSomeApplicableMutation();
		if (mutationToApply.equals("SomeQt")) {
			// Change no expr to some expr
			ExprQt noExpr = (ExprQt)value.getExpression();
			value.setExpression(ExprQt.Op.SOME.make(null, null, noExpr.decls, noExpr.sub),false);
			value.setGeneType(ExprGeneType.SOMEQT);
		} else {
			// Set the expression to true
			value.setExpression(ExprConstant.TRUE,false);
			value.setGeneType(ExprGeneType.CONSTANT);
		}
	}
	
	/**
	 * Apply mutation when the gene expression is a quantification with the operator all
	 */
	private void applyForAllMutation() throws Err {
		String mutationToApply = getSomeApplicableMutation();
		if (mutationToApply.equals("NegateBody")) {
			// Create the for all expression with the negated body
			ExprQt allExpr = (ExprQt)value.getExpression();
			Expr negatedBody = DynAlloyExpressionsUtils.negateExpression(allExpr.sub);
			value.setExpression(ExprQt.Op.ALL.make(null, null, allExpr.decls, negatedBody),false);
		} else {
			if (mutationToApply.equals("ToSome")) {
				// Create a new expression with the some quantifier
				ExprQt allExpr = (ExprQt)value.getExpression();
				value.setExpression(ExprQt.Op.SOME.make(null, null, allExpr.decls, allExpr.sub),false);
				value.setGeneType(ExprGeneType.SOMEQT);
			} else {
				// Set the expression to true
				value.setExpression(ExprConstant.TRUE,false);
				value.setGeneType(ExprGeneType.CONSTANT);
			}
		}
	}

	/**
	 * Apply mutation when the gene expression is a quantification with the operator all
	 * and the body is a predicate about two variables
	 */
	private void applyForAllVarVarMutation() throws Err {
		String mutationToApply = getSomeApplicableMutation();
		ExprQt allExpr = (ExprQt)value.getExpression();
		switch(mutationToApply) {
			case DynAlloySpecLearnerMutations.NEGATE_BODY:
				// Create the for all expression with the negated body
				Expr negatedBody = DynAlloyExpressionsUtils.negateExpression(allExpr.sub);
				value.setExpression(ExprQt.Op.ALL.make(null, null, allExpr.decls, negatedBody),false);
				break;
			case DynAlloySpecLearnerMutations.JOIN_COMPATIBLE_EXPR:
				// Append a compatible expression in the right side of the body
				ExprBinary binaryBody = (ExprBinary)allExpr.sub;
				List<Expr> joineableExprs = dsi.getJoineableExpressionsOfCurrentTypeMaintinigReturnType(binaryBody.right);
				if (joineableExprs.size()>0) {
					Expr expr = joineableExprs.get(0);
					Expr join = ExprBinary.Op.JOIN.make(null, null, binaryBody.right,expr);
					Expr newBody = binaryBody.op.make(null, null, binaryBody.left,join);
					value.setExpression(ExprQt.Op.ALL.make(null, null, allExpr.decls,newBody),false);
				}
				break;
			case DynAlloySpecLearnerMutations.TO_SOME:
				// Create a new expression with the some quantifier
				value.setExpression(ExprQt.Op.SOME.make(null, null, allExpr.decls, allExpr.sub),false);
				value.setGeneType(ExprGeneType.SOME_VAR_VAR);
				break;
			case DynAlloySpecLearnerMutations.TO_TRUE:
				// Set the expression to true
				value.setExpression(ExprConstant.TRUE,false);
				value.setGeneType(ExprGeneType.CONSTANT);
		}
	}
	
	/**
	 * Apply mutation when the gene expression is a quantification with the operator all
	 * and the body is a predicate about some relation of two variables n.value=v0 OP n.g.value=v0
	 */
	private void applyForAllVarValueVarValueMutation() throws Err {
		String mutationToApply = getSomeApplicableMutation();
		ExprQt allExpr = (ExprQt)value.getExpression();
		switch (mutationToApply) {
			case DynAlloySpecLearnerMutations.NEGATE_BODY:
				Expr negatedBody = DynAlloyExpressionsUtils.negateExpression(allExpr.sub);
				value.setExpression(ExprQt.Op.ALL.make(null, null, allExpr.decls, negatedBody),false);
				break;
			case DynAlloySpecLearnerMutations.REPLACE_VALUE:
				Expr expr = ((ExprBinary)allExpr.sub).left;
				if (expr instanceof ExprBinary) {
					ExprBinary binaryLeft = (ExprBinary)expr;
					Type currentType = binaryLeft.left.type();
					Expr newValue = DataStructureInformation.getRandomValueForType(currentType);
					
					Expr newBinaryLeft = binaryLeft.op.make(null, null, binaryLeft.left, ExprUnary.Op.NOOP.make(null, newValue));
					
					Expr right = ((ExprBinary)allExpr.sub).right;
					if (right instanceof ExprList) {
						// Two equalities at right
						ExprList listRight = (ExprList)right;
						ExprBinary fstEquality = (ExprBinary)listRight.args.get(0);
						ExprBinary sndEquality = (ExprBinary)listRight.args.get(1);
						
						Expr newFstEquality = fstEquality.op.make(null,null, fstEquality.left, ExprUnary.Op.NOOP.make(null, newValue));
						Expr newSndEquality = sndEquality.op.make(null, null, sndEquality.left, ExprUnary.Op.NOOP.make(null, newValue));
						
						Expr newList = ExprBinary.Op.AND.make(null, null, newFstEquality, newSndEquality);
						Expr newBody = ((ExprBinary)allExpr.sub).op.make(null, null, newBinaryLeft, newList);
						value.setExpression(ExprQt.Op.ALL.make(null, null, allExpr.decls, newBody),false);
					} else {
						// One equality at right
						ExprBinary binaryRight = (ExprBinary)right;
						Expr newBinaryRight = binaryRight.op.make(null, null, binaryRight.left, ExprUnary.Op.NOOP.make(null, newValue));
						Expr newBody = ((ExprBinary)allExpr.sub).op.make(null, null, newBinaryLeft, newBinaryRight);
						value.setExpression(ExprQt.Op.ALL.make(null, null, allExpr.decls, newBody),false);
					}
				}
				break;
			case DynAlloySpecLearnerMutations.NEGATE_RIGHT_EQUALITY:
				ExprBinary left = (ExprBinary)((ExprBinary)allExpr.sub).left;
				Expr right = ((ExprBinary)allExpr.sub).right;
				if (right instanceof ExprList) {
					// Two equalities at right
					ExprList rightList = (ExprList)right;
					Expr fstEqualityNegated = DynAlloyExpressionsUtils.negateExpression(rightList.args.get(0));
					Expr sndEqualityNegated = DynAlloyExpressionsUtils.negateExpression(rightList.args.get(1));
					Expr newBinary = ((ExprBinary)allExpr.sub).op.make(null, null, left, ExprBinary.Op.AND.make(null, null, fstEqualityNegated, sndEqualityNegated));
					value.setExpression(ExprQt.Op.ALL.make(null, null, allExpr.decls, newBinary), false);
					
				} else {
					// One equality at right
					Expr negatedRight = DynAlloyExpressionsUtils.negateExpression(right);
					Expr newBinary = ((ExprBinary)allExpr.sub).op.make(null, null, left, negatedRight);
					value.setExpression(ExprQt.Op.ALL.make(null, null, allExpr.decls, newBinary), false);
				}
				break;
			case DynAlloySpecLearnerMutations.TO_TRUE:
				// Set the expression to true
				value.setExpression(ExprConstant.TRUE,false);
				value.setGeneType(ExprGeneType.CONSTANT);
				break;
		}
		
	}
	
	/**
	 * Apply mutation when the gene expression is a quantification with the operator all
	 * and the body is a predicate about some relation of two variables values of int type op [n.value,n.g.value]
	 */
	private void applyForAllVarValueVarValueIntComparisonMutation() throws Err {
		String mutationToApply = getSomeApplicableMutation();
		ExprQt allExpr = (ExprQt)value.getExpression();
		ExprBinary body = (ExprBinary)allExpr.sub;
		ExprCall rightExpr = (ExprCall)body.right;
		Expr expr;
		Expr newBody;
		switch (mutationToApply) {
			case DynAlloySpecLearnerMutations.OP_NOT_EQ:
				// Change the operator to !=
				expr = DynAlloyExpressionsUtils.changeOperatorInIntComparison((ExprCall)rightExpr,ExprBinary.Op.NOT_EQUALS);
				newBody = ExprBinary.Op.IMPLIES.make(null,null,body.left, expr);
				value.setExpression(ExprQt.Op.ALL.make(null, null, allExpr.decls, newBody),false); 
				
				break;
			case DynAlloySpecLearnerMutations.OP_LT:
				// Change the operator to <
				expr = DynAlloyExpressionsUtils.changeOperatorInIntComparison((ExprCall)rightExpr,ExprBinary.Op.LT);
				newBody = ExprBinary.Op.IMPLIES.make(null,null,body.left, expr);
				value.setExpression(ExprQt.Op.ALL.make(null, null, allExpr.decls, newBody),false); 
				break;
			case DynAlloySpecLearnerMutations.OP_LTE:
				// Change the operator to <=
				expr = DynAlloyExpressionsUtils.changeOperatorInIntComparison((ExprCall)rightExpr,ExprBinary.Op.LTE);
				newBody = ExprBinary.Op.IMPLIES.make(null,null,body.left, expr);
				value.setExpression(ExprQt.Op.ALL.make(null, null, allExpr.decls, newBody),false); 
				break;
			case DynAlloySpecLearnerMutations.OP_GT:
				// Change the operator to >
				expr = DynAlloyExpressionsUtils.changeOperatorInIntComparison((ExprCall)rightExpr,ExprBinary.Op.GT);
				newBody = ExprBinary.Op.IMPLIES.make(null,null,body.left, expr);
				value.setExpression(ExprQt.Op.ALL.make(null, null, allExpr.decls, newBody),false); 
				break;
			case DynAlloySpecLearnerMutations.OP_GTE:
				// Change the operator to >=
				expr = DynAlloyExpressionsUtils.changeOperatorInIntComparison((ExprCall)rightExpr,ExprBinary.Op.GTE);
				newBody = ExprBinary.Op.IMPLIES.make(null,null,body.left, expr);
				value.setExpression(ExprQt.Op.ALL.make(null, null, allExpr.decls, newBody),false); 
				break;
		}
		
	}
	
	/**
	 * Apply mutation when the gene expression is a quantification with the operator all
	 * and the body is a predicate about some relation like op[n.value,n.f.value] AND op[n.value,n.g.value]
	 */
	private void applyForAllVarValuesDoubleIntComparisonMutation() throws Err {
		String mutationToApply = getSomeApplicableMutation();
		ExprQt allExpr = (ExprQt)value.getExpression();
		ExprList body = (ExprList)allExpr.sub;
		ExprBinary leftExpr = (ExprBinary)body.args.get(0);
		ExprBinary rightExpr = (ExprBinary)body.args.get(1);
		Expr newLeft;
		Expr newRight;
		Expr exprR1;
		Expr exprR2;
		Expr newBody;
		switch (mutationToApply) {
			case DynAlloySpecLearnerMutations.OP_NOT_EQ:
				// Change the operator to != in the left
				exprR1 = DynAlloyExpressionsUtils.changeOperatorInIntComparison((ExprCall)leftExpr.right,ExprBinary.Op.NOT_EQUALS);
				// Change the operator to != in the right
				exprR2 = DynAlloyExpressionsUtils.changeOperatorInIntComparison((ExprCall)rightExpr.right,ExprBinary.Op.NOT_EQUALS);
				newLeft = ExprBinary.Op.IMPLIES.make(null, null, leftExpr.left, exprR1);
				newRight = ExprBinary.Op.IMPLIES.make(null, null, rightExpr.left, exprR2);
				newBody = ExprBinary.Op.AND.make(null,null,newLeft, newRight);
				value.setExpression(ExprQt.Op.ALL.make(null, null, allExpr.decls, newBody),false); 
				
				break;
			case DynAlloySpecLearnerMutations.OP_LT:
				// Change the operator to < in the left
				exprR1 = DynAlloyExpressionsUtils.changeOperatorInIntComparison((ExprCall)leftExpr.right,ExprBinary.Op.LT);
				// Change the operator to < in the right
				exprR2 = DynAlloyExpressionsUtils.changeOperatorInIntComparison((ExprCall)rightExpr.right,ExprBinary.Op.LT);
				newLeft = ExprBinary.Op.IMPLIES.make(null, null, leftExpr.left, exprR1);
				newRight = ExprBinary.Op.IMPLIES.make(null, null, rightExpr.left, exprR2);
				newBody = ExprBinary.Op.AND.make(null,null,newLeft, newRight);
				value.setExpression(ExprQt.Op.ALL.make(null, null, allExpr.decls, newBody),false); 
				break;
			case DynAlloySpecLearnerMutations.OP_LTE: 
				// Change the operator to <= in the left
				exprR1 = DynAlloyExpressionsUtils.changeOperatorInIntComparison((ExprCall)leftExpr.right,ExprBinary.Op.LTE);
				// Change the operator to <= in the right
				exprR2 = DynAlloyExpressionsUtils.changeOperatorInIntComparison((ExprCall)rightExpr.right,ExprBinary.Op.LTE);
				newLeft = ExprBinary.Op.IMPLIES.make(null, null, leftExpr.left, exprR1);
				newRight = ExprBinary.Op.IMPLIES.make(null, null, rightExpr.left, exprR2);
				newBody = ExprBinary.Op.AND.make(null,null,newLeft, newRight);
				value.setExpression(ExprQt.Op.ALL.make(null, null, allExpr.decls, newBody),false); 
				break;
			case DynAlloySpecLearnerMutations.OP_GT:
				// Change the operator to > in the left
				exprR1 = DynAlloyExpressionsUtils.changeOperatorInIntComparison((ExprCall)leftExpr.right,ExprBinary.Op.GT);
				// Change the operator to > in the right
				exprR2 = DynAlloyExpressionsUtils.changeOperatorInIntComparison((ExprCall)rightExpr.right,ExprBinary.Op.GT);
				newLeft = ExprBinary.Op.IMPLIES.make(null, null, leftExpr.left, exprR1);
				newRight = ExprBinary.Op.IMPLIES.make(null, null, rightExpr.left, exprR2);
				newBody = ExprBinary.Op.AND.make(null,null,newLeft, newRight);
				value.setExpression(ExprQt.Op.ALL.make(null, null, allExpr.decls, newBody),false); 
				break;
			case DynAlloySpecLearnerMutations.OP_GTE:
				// Change the operator to >= in the left
				exprR1 = DynAlloyExpressionsUtils.changeOperatorInIntComparison((ExprCall)leftExpr.right,ExprBinary.Op.GTE);
				// Change the operator to >= in the right
				exprR2 = DynAlloyExpressionsUtils.changeOperatorInIntComparison((ExprCall)rightExpr.right,ExprBinary.Op.GTE);
				newLeft = ExprBinary.Op.IMPLIES.make(null, null, leftExpr.left, exprR1);
				newRight = ExprBinary.Op.IMPLIES.make(null, null, rightExpr.left, exprR2);
				newBody = ExprBinary.Op.AND.make(null,null,newLeft, newRight);
				value.setExpression(ExprQt.Op.ALL.make(null, null, allExpr.decls, newBody),false); 
				break;
		}
	}
	
	/**
	 * Apply mutation when the gene expression is a quantification with the operator all
	 */
	private void applyForAllVarValuesDoubleQuantificationIntComparisonMutation() throws Err {
		String mutationToApply = getSomeApplicableMutation();
		if (DynAlloySpecLearnerMutations.TO_TRUE.equals(mutationToApply)) {
			// Set the expression to true
			value.setExpression(ExprConstant.TRUE,false);
			value.setGeneType(ExprGeneType.CONSTANT);
		}
	}
	
	/**
	 * Apply mutation when the gene expression is a quantification with the operator all
	 * and the body is a predicate about a variable and a set
	 */
	private void applyForAllVarSetMutation() throws Err {
		String mutationToApply = getSomeApplicableMutation();
		if (mutationToApply.equals("NegateBody")) {
			// Create the for all expression with the negated body
			ExprQt allExpr = (ExprQt)value.getExpression();
			Expr negatedBody = DynAlloyExpressionsUtils.negateExpression(allExpr.sub);
			value.setExpression(ExprQt.Op.ALL.make(null, null, allExpr.decls, negatedBody),false);
		} else {
			if (mutationToApply.equals("ToSome")) {
				// Create a new expression with the some quantifier
				ExprQt allExpr = (ExprQt)value.getExpression();
				value.setExpression(ExprQt.Op.SOME.make(null, null, allExpr.decls, allExpr.sub),false);
				value.setGeneType(ExprGeneType.SOME_VAR_SET);
			} else {
				// Set the expression to true
				value.setExpression(ExprConstant.TRUE,false);
				value.setGeneType(ExprGeneType.CONSTANT);
			}
		}
	}
	
	/**
	 * Apply mutation when the gene expression is a quantification with the operator all
	 * and the body is a predicate about two sets
	 */
	private void applyForAllSetSetMutation() throws Err {
		String mutationToApply = getSomeApplicableMutation();
		ExprQt allExpr = (ExprQt)value.getExpression();
		switch (mutationToApply) {
			case DynAlloySpecLearnerMutations.NEGATE_BODY:
				// Negate the body just if gene expression is not the intersection in null
				if (!DynAlloyExpressionsUtils.isIntersectionInNullExpr(allExpr.sub)) {
					Expr negatedBody = DynAlloyExpressionsUtils.negateExpression(allExpr.sub);
					value.setExpression(ExprQt.Op.ALL.make(null, null, allExpr.decls, negatedBody),false);
				}
				break;
			case DynAlloySpecLearnerMutations.INTERSECTION_NULL:
				// Take the set s1 and s2 from the body of the expression, and create
				// the body s1 & s2 in Null
				ExprBinary expressionWithSets;
				if (allExpr.sub instanceof ExprUnary) {
					expressionWithSets = (ExprBinary)((ExprUnary)allExpr.sub).sub;
				} else {
					if (((ExprBinary)allExpr.sub).right.equals(DataStructureInformation.nullSig)) {
						expressionWithSets = (ExprBinary)((ExprBinary)allExpr.sub).left;
					} else {
						expressionWithSets = (ExprBinary)allExpr.sub;
					}
				}
				Expr intersection = ExprBinary.Op.INTERSECT.make(null, null, expressionWithSets.left, expressionWithSets.right);
				Expr intersectionNull = ExprBinary.Op.IN.make(null, null, intersection, DataStructureInformation.nullSig);
				value.setExpression(ExprQt.Op.ALL.make(null, null, allExpr.decls, intersectionNull),false);
				break;
			case DynAlloySpecLearnerMutations.TO_SOME:
				// Create a new expression with the some quantifier
				value.setExpression(ExprQt.Op.SOME.make(null, null, allExpr.decls, allExpr.sub),false);
				value.setGeneType(ExprGeneType.SOME_SET_SET);
				break;
			case DynAlloySpecLearnerMutations.TO_TRUE:
				// Set the expression to true
				value.setExpression(ExprConstant.TRUE,false);
				value.setGeneType(ExprGeneType.CONSTANT);
				break;
			default:
		}
	}

	/**
	 * Apply mutation when the gene expression is in
	 */
	private void applyInclusionMutation() {
		// TODO Auto-generated method stub
	}

	/**
	 * Apply mutation when the gene expression is equal or not equal 
	 */
	private void applyEqualityMutation() {
		ExprBinary equalityExpr = (ExprBinary)value.getExpression();
		if (equalityExpr.right instanceof PrimSig) {
			String mutationToApply = getSomeApplicableMutation();
			if (mutationToApply.equals("Negate")) {
				// Negate the expression
				value.setExpression(ExprUnary.Op.NOT.make(null, value.getExpression()),false);
				value.setGeneType(ExprGeneType.NEGATION);
			} else {
				// Set the expression to true
				value.setExpression(ExprConstant.TRUE,false);
				value.setGeneType(ExprGeneType.CONSTANT);
			}
		} else {
			
		}
	}

	/**
	 * Gets randomly an applicable mutation for the current gene type
	 */
	private String getSomeApplicableMutation() {
		List<String> mutations = value.getGeneType().getApplicableMutations(amountOfGenesInChromosome,isPartOfSolution);
		if (mutations.size()>0) {
			Random random = new Random();
			int randomNumber = random.nextInt(mutations.size());
			return mutations.get(randomNumber);
		}
		return "";
	}

	/**
	 * Apply mutation when the gene expression is not
	 */
	private void applyNegationMutation() {
		String mutationToApply = getSomeApplicableMutation();
		if (mutationToApply.equals("Negate")) {
			// Negate the expression, that is remove the not operator
			value.setExpression(((ExprUnary)value.getExpression()).sub,true);
		} else {
			// Set the expression to true
			value.setExpression(ExprConstant.TRUE,false);
			value.setGeneType(ExprGeneType.CONSTANT);
		}
	}

	/**
	 * Apply mutation when the gene expression is constant
	 */
	private void applyConstantMutation() {
		String mutationToApply = getSomeApplicableMutation();
		if (mutationToApply.equals("Previous")) {
			// Get some previous expression
			Random random = new Random();
			int randomNumber = random.nextInt(1);
			value = value.getPrevious();
		} 
	}

	/**
	 * Apply mutation when the gene expression is cardinality
	 */
	private void applyCardinalityMutation() throws Err {
		String mutationToApply = getSomeApplicableMutation();
		if (mutationToApply.equals(DynAlloySpecLearnerMutations.ADD_ONE)) {
			// Add one at the right expression
			Expr expr = DynAlloyExpressionsUtils.addOrSubtractOneToIntComparisson((ExprCall)value.getExpression(), true);
			
			value.setExpression(expr,false); 
			
		} else if (mutationToApply.equals(DynAlloySpecLearnerMutations.SUB_ONE)) {
			// Subtract one at the right expression
			Expr expr = DynAlloyExpressionsUtils.addOrSubtractOneToIntComparisson((ExprCall)value.getExpression(), false);
			
			value.setExpression(expr,false); 
		} else {
			// Set the expression to true
			value.setExpression(ExprConstant.TRUE,false);
			value.setGeneType(ExprGeneType.CONSTANT);
		}	
	}
	
	@Override
	public Object getInternalValue() {
		return (ExprGeneValue)value;
	}
	
	public int compareTo(ExprGene other) {
		if (value.getExpression().equals(other.getValue().getExpression())) {
			return 0;
		} else {
			return 1;
		}
	}

	/**
	 * Returns true if this gene has the default value true.
	 */
	public boolean isDefault() {
		return value.getExpression().equals(ExprConstant.TRUE);
	}

	/**
	 * Retrieves a string representation of the Expr Gene
	 */
	@Override
	public String toString() {
		String representation;
	    if (getInternalValue() == null) {
	      representation = "null";
	    }
	    else {
	      representation = getInternalValue().toString();
	    }
	    return representation;
	}
	
	public ExprGene clone() {
		try {
			return new ExprGene(getConfiguration(),this.value.clone(),this.dsi);
		} catch (InvalidConfigurationException ex) {
			throw new IllegalStateException(ex.getMessage());
		}
	}
	
}
