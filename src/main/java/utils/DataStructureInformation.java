package utils;

import java.util.HashMap;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Random;
import java.util.Set;

import org.jgrapht.DirectedGraph;
import org.jgrapht.graph.DefaultDirectedGraph;
import org.jgrapht.graph.DefaultEdge;

import dynalloyWrapper.DynAlloyRunner;
import rfm.dynalloy.ConstList;
import rfm.dynalloy.SafeList;
import rfm.dynalloyCompiler.ast.Command;
import rfm.dynalloyCompiler.ast.Decl;
import rfm.dynalloyCompiler.ast.ExprHasName;
import rfm.dynalloyCompiler.ast.ExprUnary;
import rfm.dynalloyCompiler.ast.ExprVar;
import rfm.dynalloyCompiler.ast.Sig;
import rfm.dynalloyCompiler.ast.Type;
import rfm.dynalloyCompiler.ast.Expr;
import rfm.dynalloyCompiler.ast.ExprBinary;
import rfm.dynalloyCompiler.ast.Sig.PrimSig;
import rfm.dynalloyCompiler.translator.A4Solution;

/**
 * This class keeps some useful information regarding the data structure being analyzed.
 * @author fmolina
 */
public class DataStructureInformation {

	private DirectedGraph<String,DefaultEdge> structureGraph; // Graph of the relation of the data structure
	
	private Map<String,LinkedList<Expr>> commandExpressions; // Commands
	private Map<String,LinkedList<Expr>> expressionsByEvaluationValue; // Contains the expressions according to its evaluation result
	private final int scope;                      // Scope (defined in the alloy file)
	
	private List<Expr> joinedExpressions;         // Contains expressions of the form e.f
	private List<Expr> joinedExpressionsOfTypeInt;// Contains expressions of the from e.f which type is int
	private List<Expr> simpleClosuredExpressions; // Contains expressions of the form e.*f
	private List<Expr> doubleClosuredExpressions; // Contains expressions of the from e.*(f+g)
	
	public static Sig nullSig;						        // Null signature
	
	private List<Expr> relationsForEvaluation;				// Data structure relations ready to evaluate
	private Map<String,Type> structureRelations;            // Data structure relations with types
	private static List<Sig> structureSignatures;					// All signatures
	private List<Sig> signaturesUsedInRecursiveRelations;   // Signatures used in recursive relations 
	private static Map<Type,List<Expr>> signatureEvaluations;      // Each time that an expression of any type is evaluated, the evaluation value is added to the list.
	private Map<Type,List<Expr>> joineableExpressionsByType;	// Joineable expressions for each type
	
	/**
	 * Constructor
	 * @param decls is the parameter declarations of the data structure
	 * @param commands are the commands to be executed
	 */
	public DataStructureInformation(ConstList<Decl> decls,ConstList<Command> commands) {
		structureRelations = new HashMap<String,Type>();
		expressionsByEvaluationValue = new HashMap<String,LinkedList<Expr>>();
		relationsForEvaluation = new LinkedList<Expr>();
		for (Decl decl : decls) {
			// Get each attribute with the respective type from the specification (RepOK parameters)
			Type declType = decl.expr.type();
			for (int i = 0 ; i < decl.names.size() ; i++) {
				relationsForEvaluation.add(decl.names.get(i));
				String name = decl.names.get(i).label;
				structureRelations.put(name, declType);
			}
		}
		scope = commands.get(0).overall;
 		buildGraph();
 		buildExpressions();
 		buildExpressionsForCommands(commands);
	}
	
	/**
	 * Save signatures information
	 */
	public void saveSignaturesInformation(A4Solution example) {
		SafeList<Sig> signatureList = example.getAllReachableSigs();
		
		Sig nullSig = signatureList.get(5);
		DataStructureInformation.nullSig = nullSig;
		structureSignatures = new LinkedList<Sig>();
		signaturesUsedInRecursiveRelations = new LinkedList<Sig>();
		signatureEvaluations = new HashMap<Type,List<Expr>>();
		// Iterate over all the signatures, and save those that are used in recursive relations.
		for (Sig signature : signatureList) {
			structureSignatures.add(signature);
			boolean found=false;
			for (ExprVar skolem : example.getAllSkolems()) {
				List<List<PrimSig>> foldedType = skolem.type().fold();
				for (List<PrimSig> fold : foldedType) {
					if (fold.size()==2) {
						if (fold.get(0).equals(signature)&&fold.get(0).equals(fold.get(1))) {
							signaturesUsedInRecursiveRelations.add(signature);
							found = true;
						}
					}
					if (found)
						break;
				}
				if (found)
					break;
			}
		}
		
	}
	
	/**
	 * Build a graph where the vertex set is the set of declaration names of the data structure
	 * and there is an edge between a vertex v1 and a vertex v2 iff the type of the declaration
	 * v1 can be joined with the type of the declaration v2.
	 */
	private void buildGraph() {
		// Generate each node from the keys
		structureGraph = new DefaultDirectedGraph<String, DefaultEdge>(DefaultEdge.class);
		for (String node : structureRelations.keySet()){
			structureGraph.addVertex(node);
		}
		// Generate each edge from the key types
		for (String sourceKey : structureRelations.keySet()) {
			for (String targetKey : structureRelations.keySet()) {
				Type sourceType = structureRelations.get(sourceKey);
				Type targetType = structureRelations.get(targetKey);
				if (DynAlloyRunner.joinableTypes(sourceType, targetType)) {
					structureGraph.addEdge(sourceKey, targetKey);
				}
			}
		}
	}
	
	/**
	 * Get evaluable expressions
	 */
	public List<Expr> getEvaluableExpressions() {
		List<Expr> expressionsList = new LinkedList<Expr>();
		expressionsList.addAll(joinedExpressions);
		expressionsList.addAll(joinedExpressionsOfTypeInt);
		expressionsList.addAll(simpleClosuredExpressions);
		expressionsList.addAll(doubleClosuredExpressions);
		return expressionsList;
	}
	
	/**
	 * Returns the evaluable expressions grouped by the evaluation value
	 */
	public Map<String,LinkedList<Expr>> getExpressionsByEvaluationValue() {
		return expressionsByEvaluationValue;
	}
	
	/**
	 * Clear the expression by value map
	 */
	public void clearExpressionsByEvaluationValue() {
		expressionsByEvaluationValue.clear();
	}
	
	/**
	 * Adds evaluation to value
	 * @param evaluableExpr is the expression which evaluation is value 
	 * @param value
	 */
	public void addEvaluationToValue(Expr evaluableExpr,String value) {
		if (!expressionsByEvaluationValue.containsKey(value)) {
			expressionsByEvaluationValue.put(value, new LinkedList<Expr>());
		} 			
		expressionsByEvaluationValue.get(value).add(evaluableExpr);
	}
	
	/**
	 * Add the possible evaluation to the given type
	 */
	public void addEvaluationToSignature(Type type,Expr evaluation) {
		if (!signatureEvaluations.containsKey(type))
			signatureEvaluations.put(type, new LinkedList<Expr>());
		// Add the evaluation if it not exists
		boolean found=false;
		for (Expr expr : signatureEvaluations.get(type)) {
			if (expr.toString().equals(evaluation.toString())){
				found=true;
				break;
			}
		}
		if (!found) {
			signatureEvaluations.get(type).add(evaluation);
		}
	}
	
	/**
	 * Get the expressions that can be evaluated for a command
	 * @param cmdLabel is the command label
	 */
	public List<Expr> getCommandExpressions(String cmdLabel) {
		return commandExpressions.get(cmdLabel);
		
	}
	
	public List<Expr> getCommandExpressions2(Iterable<ExprVar> skolems) {
		List<Expr> expressionsToEval = new LinkedList<Expr>();	
		expressionsToEval.addAll(translateExpressions(joinedExpressions,skolems));
		expressionsToEval.addAll(translateExpressions(joinedExpressionsOfTypeInt,skolems));
		expressionsToEval.addAll(translateExpressions(simpleClosuredExpressions,skolems));
		expressionsToEval.addAll(translateExpressions(doubleClosuredExpressions,skolems));
		return expressionsToEval;
	}
	
	/**
	 * Translate all the joined expressions 
	 */
	public List<Expr> getCommandJoinedExpressions(Iterable<ExprVar> skolems) {
		return translateExpressions(joinedExpressions,skolems);
	}
	
	/**
	 * Translate all the joined expressions of type int
	 */
	public List<Expr> getCommandJoinedExpressionsInt(Iterable<ExprVar> skolems) {
		return translateExpressions(joinedExpressionsOfTypeInt,skolems);
	}
	
	/**
	 * Translate all the simple closured expressions
	 */
	public List<Expr> getCommandSimpleClosuredExpressions(Iterable<ExprVar> skolems) {
		return translateExpressions(simpleClosuredExpressions,skolems);
	}
	
	/**
	 * Translate all the double closured expressions
	 */
	public List<Expr> getCommandDoubleClosuredExpressions(Iterable<ExprVar> skolems) {
		return translateExpressions(doubleClosuredExpressions,skolems);
	}
	
	/**
	 * Translates all the given expressions
	 */
	private List<Expr> translateExpressions(List<Expr> expressions,Iterable<ExprVar> skolems) {
		List<Expr> translatedExpressions = new LinkedList<Expr>();
		for (Expr expr : expressions) {
			translatedExpressions.add(translateExpression(skolems,expr));
		}
		return translatedExpressions;
	}
	
	/**
	 * Given an expression translates to an equivalent expression but with the expression names present in the skolems. 
	 * @param skolems list of expression with correct names
	 * @param expr is the expression to translate
	 * @return the equivalent translated expression
	 */
	private Expr translateExpression(Iterable<ExprVar> skolems,Expr expr) {
		if (expr instanceof ExprVar) {
			// The expression is a expr var
			return getExpression(skolems,((ExprVar)expr).label);
		} else {
			if (expr instanceof ExprUnary) {
				// The expression is closure
				Expr subExpr = ((ExprUnary)expr).sub;
				Expr newSubExpr = translateExpression(skolems,subExpr);
				return ExprUnary.Op.RCLOSURE.make(null, newSubExpr);
			} else {
				// The expression is a joined expr
				Expr leftExpr = ((ExprBinary)expr).left;
				Expr rightExpr = ((ExprBinary)expr).right;
				
				Expr newLeftExpr = translateExpression(skolems,leftExpr);
				Expr newRightExpr = translateExpression(skolems,rightExpr);
				return ((ExprBinary)expr).op.make(null, null, newLeftExpr, newRightExpr);
			}
		}
	}
	
	/**
	 * Returns the expression with the given name and present in the skolems
	 * @param skolems is a list of expressions
	 * @param name is the name of the expression to search
	 * @return the expression with the given name
	 */
	private Expr getExpression(Iterable<ExprVar> skolems,String name) {
		Iterator<ExprVar> skolemsIterator = skolems.iterator();
		while (skolemsIterator.hasNext()) {
			ExprVar skolem = skolemsIterator.next();
			if (skolem.label.contains(name)) {
				return skolem;
			} 
		}
		return null;
	}
	
	/**
	 * Build expressions from graph
	 */
	private void buildExpressions() {
		joinedExpressions = new LinkedList<Expr>();
		joinedExpressionsOfTypeInt = new LinkedList<Expr>();
		simpleClosuredExpressions = new LinkedList<Expr>();
		doubleClosuredExpressions = new LinkedList<Expr>();
		joineableExpressionsByType = new HashMap<Type,List<Expr>>();
	
		ExprVar thizExpr = ExprVar.make(null, "thiz",structureRelations.get("thiz"));
		buildAllExpressions(thizExpr,"thiz",scope);
	}
	
	private void buildAllExpressions(Expr expr,String vertex,int scope) {
		if (expr.type().is_int()) {
			if (allowToCreateCardinalityExpr(expr)) {
				joinedExpressionsOfTypeInt.add(expr);
			}
		} else {
			if (!vertex.equals("thiz"))
				joinedExpressions.add(expr);
		}
		if (scope>0) {
			Set<DefaultEdge> outgoingEdges = structureGraph.outgoingEdgesOf(vertex);
			List<Expr> adjacentClosuredExpressions = new LinkedList<Expr>();
			for (DefaultEdge edge : outgoingEdges) {
				
				String targetVertex = structureGraph.getEdgeTarget(edge);
				ExprVar adjacentExpr = ExprVar.make(null, targetVertex,structureRelations.get(targetVertex));
				
				//if (!expr.type().equals(expr.join(adjacentExpr).type())) {
				if (!joineableExpressionsByType.containsKey(expr.type()))
					joineableExpressionsByType.put(expr.type(), new LinkedList<Expr>());
				joineableExpressionsByType.get(expr.type()).add(getCorrespondingEvaluableExpression(targetVertex));
				//}
				
				if (!isClosure(targetVertex)) {
					// Just join with non closured expressions
					Expr newExpr = expr.join(adjacentExpr);
					buildAllExpressions(newExpr,targetVertex,scope-1);
				}
				if (isClosure(targetVertex)&&(!isClosure(vertex))) {
					adjacentClosuredExpressions.add(adjacentExpr);
					simpleClosuredExpressions.add(expr.join(ExprUnary.Op.RCLOSURE.make(null, adjacentExpr)));
				}
			}
			
			for (int i=0;i<adjacentClosuredExpressions.size()-1;i++) {
				for (int j=i+1;j<adjacentClosuredExpressions.size();j++) {
					doubleClosuredExpressions.add(expr.join(ExprUnary.Op.RCLOSURE.make(null, ExprBinary.Op.PLUS.make(null, null, adjacentClosuredExpressions.get(i), adjacentClosuredExpressions.get(j)))));
				}
			}
			
		}
	}
	
	/**
	 * Given an expression of type int determine if can be used in cardinality expressions
	 * An expressions e.f of type int can used in cardinality expressions if and only if
	 * e: A -> B and A & B = empty. That is, e cannot be closured
	 */
	private boolean allowToCreateCardinalityExpr(Expr intExpr) {
		ExprBinary binary = (ExprBinary)intExpr;
		if (binary.left instanceof ExprVar) 
			return true;
		
		if (binary.left instanceof ExprBinary){
			Expr rightExpr = ((ExprBinary)binary.left).right;
			List<List<PrimSig>> folded = rightExpr.type().fold();
			boolean allow = true;
			int i=0;
			while (allow && i < folded.size()) {
				List<PrimSig> list = folded.get(i);
				if (list.get(0).type().intersects(list.get(1).type())) {
					allow = false;
				}
				i++;
			}
			return allow;
		}
		
		return false;
	}
	
	/**
	 * Get corresponding evaluable expression according to name
	 */
	private Expr getCorrespondingEvaluableExpression(String exprName) {
		for (Expr expr : relationsForEvaluation) {
			if (exprName.equals(((ExprHasName)expr).label)) {
				return expr;
			}
		}
		return null;
	}
	
	/**
	 * Builds all the expressions of a given length
	 * @param expr is the expression being builded
	 * @param vertex is the current vertex being 
	 * @param scope is the length of expressions to be builded
	 * @return a list of expressions
	 */
	private List<Expr> buildExpressionsOfLength(String vertex,int scope) {
		ExprVar currentExpr = ExprVar.make(null, vertex,structureRelations.get(vertex));
		if (scope == 0) {
			LinkedList<Expr> exprList = new LinkedList<Expr>();
			exprList.add(currentExpr);
			if (isClosure(vertex)) {
				exprList.add(ExprUnary.Op.RCLOSURE.make(null, currentExpr));
			}
			return exprList;
		} else {
			Set<DefaultEdge> outgoingEdges = structureGraph.outgoingEdgesOf(vertex);
			List<Expr> adjacentExpressions = new LinkedList<Expr>();
			for (DefaultEdge edge : outgoingEdges) {
				// For each adjacent vertex creates all the expressions starting from that vertex and of length
				// scope-1
				String targetVertex = structureGraph.getEdgeTarget(edge);
				adjacentExpressions.addAll(buildExpressionsOfLength(targetVertex,scope-1));
			}
			
			List<Expr> resultingExpressions = new LinkedList<Expr>();
			for (Expr expr : adjacentExpressions) {
				// For each adjacent expression, join it with the current expression. If the current expression 
				// can be closured, also join the closured current expression with the adjacent.
				resultingExpressions.add(currentExpr.join(expr));
				if (isClosure(vertex)) {
					resultingExpressions.add(ExprUnary.Op.RCLOSURE.make(null, currentExpr).join(expr));
				}
			}
			return resultingExpressions;
		}
	}
	
	/**
	 * Returns true if the current vertex generates an expression than can be closure 
	 * @param vertex
	 * @return
	 */
	private boolean isClosure(String vertex) {
		Set<DefaultEdge> outgoingEdges = structureGraph.outgoingEdgesOf(vertex);
		for (DefaultEdge edge : outgoingEdges) {
			// For each adjacent vertex create an expression, join it with the current expression
			// and try to add it to the expression list
			String targetVertex = structureGraph.getEdgeTarget(edge);
			if (vertex.equals(targetVertex)) {
				return true;
			}
		}
		return false;
	}

	/**
	 * Build the expressions that can be evaluated for a list of commands
	 * @param commands
	 */
	private void buildExpressionsForCommands(ConstList<Command> commands) {
		commandExpressions = new HashMap<String,LinkedList<Expr>>();
		for (Command cmd : commands) {
			commandExpressions.put(cmd.label, new LinkedList<Expr>());
			commandExpressions.get(cmd.label).addAll(buildExpressionsForCommand(cmd,joinedExpressions));
			commandExpressions.get(cmd.label).addAll(buildExpressionsForCommand(cmd,simpleClosuredExpressions));
			commandExpressions.get(cmd.label).addAll(buildExpressionsForCommand(cmd,doubleClosuredExpressions));
		}
	}
	
	/**
	 * Returns all the given expression according to the given command 
	 */
	private List<Expr> buildExpressionsForCommand(Command cmd,List<Expr> expressions) {
		List<Expr> expressionsForCommand = new LinkedList<Expr>();
		for (Expr expr: expressions) {
			expressionsForCommand.add(renameExprAccordingToCommand(cmd.label,expr));
		}
		return expressionsForCommand;
	}
	
	/**
	 * Rename a expressions for make it evaluable according to a command label
	 * @param cmdLabel is the command label
	 * @param expr is the expression to be renamed
	 * @return a expression with a new name
	 */
	private Expr renameExprAccordingToCommand(String cmdLabel,Expr expr) {
		if (expr instanceof ExprVar) {
			// The expression is a expr var
			String currentLabel = ((ExprVar)expr).label;
			String newLabel = "$"+cmdLabel+"_"+currentLabel;
			return ExprVar.make(null, newLabel,expr.type());
		} else {
			if (expr instanceof ExprUnary) {
				// The expression is closure
				Expr subExpr = ((ExprUnary)expr).sub;
				Expr newSubExpr = renameExprAccordingToCommand(cmdLabel,subExpr);
				return ExprUnary.Op.RCLOSURE.make(null,newSubExpr);
			} else {
				// The expression is a joined expr
				Expr leftExpr = ((ExprBinary)expr).left;
				Expr rightExpr = ((ExprBinary)expr).right;
		
				Expr newLeftExpr = renameExprAccordingToCommand(cmdLabel,leftExpr);
				Expr newRightExpr = renameExprAccordingToCommand(cmdLabel,rightExpr);
				return newLeftExpr.join(newRightExpr);
			}
		}
	}

	/**
	 * Calculates all the possible comparisons between expressions (only those expressions which types are not disjoint)
	 */
	public int calculatePossibleComparisonsBetweenExpressions() {
		int possibleComparisons = 0;
		for (int i=0;i<joinedExpressions.size()-1;i++) {
			for (int j=i+1;j<joinedExpressions.size();j++) {
				if (joinedExpressions.get(i).type().intersects(joinedExpressions.get(j).type())) {
					// The i-th expression can be compared with the j-th expression
					possibleComparisons++;
				}	
			}
		}
		return possibleComparisons;
	}
	
	public int calculateAmountCardinalityExpressions() {
		return joinedExpressionsOfTypeInt.size()*(simpleClosuredExpressions.size()+doubleClosuredExpressions.size());
	}
	
	/**
	 * Returns true if the given expression has a closured subexpression
	 * @param evaluableExpr
	 * @return
	 */
	public boolean hasClosuredExpr(Expr evaluableExpr) {
		if (evaluableExpr instanceof ExprVar) {
			return false;
		} else if (evaluableExpr instanceof ExprUnary) {
			if (((ExprUnary)evaluableExpr).op.equals(ExprUnary.Op.RCLOSURE)) {
				return true;
			} else {
				return false;
			}
		} else {
			ExprBinary binary = (ExprBinary)evaluableExpr;
			return hasClosuredExpr(binary.left)||hasClosuredExpr(binary.right);
		}
	}

	/**
	 * Returns the amount of simple closured expressions
	 */
	public int getAmountOfSimpleClosuredExpressions() {
		return simpleClosuredExpressions.size();
	}
	
	/**
	 * Returns the amount of double closured expressions
	 */
	public int getAmountOfDoubleClosuredExpressions() {
		return doubleClosuredExpressions.size();
	}
	
	/**
	 * Returns the amount of closured expressions
	 */
	public int getAmountOfClosuredExpressions() {
		return simpleClosuredExpressions.size()+doubleClosuredExpressions.size();
	}

	/**
	 * Returns the amount of non closured expresssions
	 * @return
	 */
	public int getAmountOfNonClosuredExpressions() {
		return joinedExpressions.size();
	}
	
	/**
	 * Counts the amount of times that the expression appears in the currentExpr
	 */
	private int getTotalOcurrences(String expression,Expr expr) {
		if (expr instanceof ExprVar) {
			// Check is the label is the same that the expression
			ExprVar exprVar = (ExprVar)expr;
			if (exprVar.label.contains(expression)) {
				return 1;
			}
		} else if (expr instanceof ExprUnary) {
			// Count the ocurrences in the subexpression
			ExprUnary exprUnary = (ExprUnary)expr;
			if (exprUnary.op.equals(ExprUnary.Op.RCLOSURE)) {
				if (expression.charAt(0)=='*') {
					return getTotalOcurrences(expression.substring(1, expression.length()),exprUnary.sub);
				} else {
					return 0;
				}
			} else {
				return getTotalOcurrences(expression,exprUnary.sub);
			}
		} else if (expr instanceof ExprBinary) {
			ExprBinary exprBinary = (ExprBinary)expr;
			return getTotalOcurrences(expression,exprBinary.left)+getTotalOcurrences(expression,exprBinary.right);
		} 
		return 0;
	}
	
	/**
	 * Returns true if exists some binary relation r : type -> type + something
	 */
	public boolean typeUsedInRecursiveRelation(Type type) {
		for (List<PrimSig> primSigList : type.fold()) {
			for (PrimSig primSig : primSigList) {
				if (signaturesUsedInRecursiveRelations.contains(primSig))
					return true;
			}
		}
		return false;
	}
	
	/**
	 * Returns all the expression that can be joined with an expression of the given type. That is
	 * expressions of the form: type -> AnotherType
	 */
	public List<Expr> getJoineableExpressionsOfCurrentType(Type type) {
		if (joineableExpressionsByType.containsKey(type))
			return joineableExpressionsByType.get(type);
		return new LinkedList<Expr>();
	}
	
	/**
	 * Returns all the expression that can be joined with an expression of the given type, but keeping
	 * the return type. That is an expression of the form type -> type + something
	 */
	public List<Expr> getJoineableExpressionsOfCurrentTypeMaintinigReturnType(Expr expr) {
		Type type = expr.type();
		if (joineableExpressionsByType.containsKey(type)) {
			List<Expr> joineableToType = joineableExpressionsByType.get(type);
			List<Expr> sameReturnType = new LinkedList<Expr>();
			for (Expr joineable: joineableToType) {
				Type returnType = getReturnType(joineable.type());
				if (type.intersects(returnType) && !expr.toString().contains(joineable.toString()))
					sameReturnType.add(joineable);
			}
			return sameReturnType;
		}
		return new LinkedList<Expr>();
	}
	
	/**
	 * Returns some possible value for the given type
	 */
	public Expr getSomeValueForType(Type type) {
		Expr expr = signatureEvaluations.get(type).iterator().next();
		if (expr instanceof ExprVar) {
			return getCorrespondingSignature((ExprVar)expr);
		} else {
			return expr;
		}
	}
	
	/**
	 * Returns some possible value for the given type
	 */
	public static Expr getRandomValueForType(Type type) {
		Random random = new Random();
		if (signatureEvaluations.get(type)!=null) {
			int randomNumber = random.nextInt(signatureEvaluations.get(type).size());
			Expr expr=signatureEvaluations.get(type).get(randomNumber);
			if (expr instanceof ExprVar) {
				return getCorrespondingSignature((ExprVar)expr);
			} else {
				return expr;
			}
		}
		return null;
	}
	
	/**
	 * Returns a non-null return type for the given type.
	 */
	public Type getReturnType(Type type) {
		// Get the first resulting non-null type
		Type t=null;
		for (List<PrimSig> primSigList : type.fold()) {
			if (primSigList.size()==2) {
				t = primSigList.get(1).type();
				break;
			}
		}
		return t;
	}
	
	/**
	 * Returns true if the type1 contains the type2
	 */
	public boolean typeContains(Type type1,Type type2) {
		List<PrimSig> sigsType2 = type2.fold().get(0);
		for (List<PrimSig> primSigList : type1.fold()) {
			if (sigsType2.equals(primSigList))
				return true;
		}
		return false;
	}
	
	/**
	 * Given an expr var, returns the corresponding signature. If is not found, then return the null signature
	 */
	public static Sig getCorrespondingSignature(ExprVar var) {
		String sigName = "this/"+var.label.substring(0, var.label.length()-2);
		for (Sig signature : structureSignatures) {
			if (signature.label.equals(sigName))
				return signature;
		}
		return nullSig;
	}
	
}
