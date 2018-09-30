package utils;

/**
 * This class contains parameters for the learning process
 * @author fmolina
 */
public class DynAlloySpecLearnerParameters {

	// Evolutionary process parameters
	private int populationSize;
	private int generations;
	private double mutationProb;
	private double crossoverProb;
	
	// Chromosomes related parameters
	private int examplesConsideredForInitialChromosomesGeneration;
	private boolean initialChromosomesUnary;
	
	
	// Expressions generation related parameters
	private boolean considerJoinedExpressions;
	private boolean considerIntEvaluations;
	private boolean considerCardinalityExpressions;
	private boolean considerSimpleClosuredExpressions;
	private boolean considerDoubleClosuredExpressions;

	/**
	 * Constructor. Initialize the parameters with default value
	 */
	public DynAlloySpecLearnerParameters() {
		
		// Evolutionary process parameters
		populationSize = 100;
		generations = 50;
		mutationProb = 0.3;
		crossoverProb = 1;
		
		// Chromosomes related parameters
		examplesConsideredForInitialChromosomesGeneration = 4;
		initialChromosomesUnary = true;
		
		// Expressions generation related parameters
		considerJoinedExpressions = true;
		considerIntEvaluations = true;
		considerCardinalityExpressions = true;
		considerSimpleClosuredExpressions = true;
		considerDoubleClosuredExpressions = true;
	}
	
	/**
	 * Get the number of generations
	 */
	public int getNumberOfGenerations() {
		return generations;
	}
	
	/**
	 * Set the number of generations
	 */
	public void setNumberOfGenerations(int n) {
		if (n<1)
			throw new IllegalArgumentException("The number of generations must be positive");
		generations = n;
	}
	
	/**
	 * Get the amount of examples considered for the initial chromosomes generation
	 */
	public int getAmountOfExamplesForInitialChromosomesGeneration() {
		return examplesConsideredForInitialChromosomesGeneration;
	}
	
	/**
	 * Set the amount of examples considered for the initial chromosomes generation
	 */
	public void setAmountOfExamplesForInitialChromosomesGeneration(int n) {
		if (n<1 || n%2!=0)
			throw new IllegalArgumentException("The amount of examples considered for the initial chromosomes generation must be a positive pair number");
		examplesConsideredForInitialChromosomesGeneration = n;
	}
	
	/**
	 * Get initial chromosomes unary
	 */
	public boolean getInitialChromosomesUnary() {
		return initialChromosomesUnary;
	}
	
	/**
	 * Set initial chromosomes unary
	 */
	public void setInitialChromosomesUnary(boolean b) {
		initialChromosomesUnary = b;
	}
	
	/**
	 * Get the population size
	 */
	public int getPopulationSize() {
		return populationSize;
	}
	
	/**
	 * Set the population size
	 */
	public void setPopulationSize(int n) {
		if (n<1)
			throw new IllegalArgumentException("The population size must be a positive number");
		populationSize = n;
	}
	
	/**
	 * Get consider joined expressions
	 */
	public boolean getConsiderJoinedExpressions() {
		return considerJoinedExpressions;
	}
	
	/**
	 * Set consider joiner expressions value
	 */
	public void setConsiderJoinedExpressions(boolean b) {
		considerJoinedExpressions = b;
	}
	
	/**
	 * Get consider int evaluations
	 */
	public boolean getConsiderIntEvaluations() {
		return considerIntEvaluations;
	}
	
	/**
	 * Set consider int evaluations
	 */
	public void setConsiderIntEvaluations(boolean b) {
		considerIntEvaluations = b;
	}
	
	/**
	 * Get consider cardinality expressions
	 */
	public boolean getConsiderCardinalityExpressions() {
		return considerCardinalityExpressions;
	}
	
	/**
	 * Set consider cardinality expressions
	 */
	public void setConsiderCardinalityExpressions(boolean b) {
		considerCardinalityExpressions = b;
	}
	
	/**
	 * Get consider simple closured expressions
	 */
	public boolean getConsiderSimpleClosuredExpressions() {
		return considerSimpleClosuredExpressions;
	}
	
	/**
	 * Set consider simple closured expressions
	 */
	public void setConsiderSimpleClosuredExpressions(boolean b) {
		considerSimpleClosuredExpressions = b;
	}
	
	/**
	 * Get consider double closured expressions
	 */
	public boolean getConsiderDoubleClosuredExpressions() {
		return considerDoubleClosuredExpressions;
	}
	
	/**
	 * Set consider double closured expressions
	 */
	public void setConsiderDoubleClosuredExpressions(boolean b) {
		considerDoubleClosuredExpressions = b;
	}
	
	/**
	 * Get the mutation probability
	 */
	public double getMutationProbability() {
		return mutationProb;
	}
	
	/**
	 * Set the mutation probability
	 */
	public void setMutationProbabilty(double mProb) {
		if (mProb<0 || mProb >1)
			throw new IllegalArgumentException("Invalid probability");
		mutationProb = mProb;
	}
	
	/**
	 * Get the crossover probability
	 */
	public double getCrossoverProbability() {
		return crossoverProb;
	}
	
	/**
	 * Set the crossover probability
	 */
	public void setCrossoverProbabilty(double cProb) {
		if (cProb<0 || cProb >1)
			throw new IllegalArgumentException("Invalid probability");
		mutationProb = cProb;
	}
	
}
