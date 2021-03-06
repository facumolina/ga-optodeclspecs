package geneticalgorithm.fitnessfunction;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Set;

import org.jgap.FitnessFunction;
import org.jgap.Gene;
import org.jgap.IChromosome;
import org.jgap.impl.IntegerGene;

import rfm.dynalloyCompiler.ast.Expr;
import dynalloyWrapper.DynAlloyRunner;
import geneticalgorithm.chromosome.ExprGene;
import geneticalgorithm.chromosome.ExprGeneValue;
import geneticalgorithm.chromosome.InvariantChromosome;
import main.ConfigurationProperties;

/**
 * Fitness function that computes the value according to the amount
 * of negative and positive counterexamples of the chromosome.
 * @author fmolina
 */
public class DynAlloyEquivalenceSpecCounter extends FitnessFunction {

	private final DynAlloyRunner runner;
	private int counterexamplesValues;
	private int amountOfGenes;
	private double[][] fitnessMatrix;
	private boolean initialSpecEmpty;
	private HashMap<String,Double> calculatedFitness;
	private long itime;
	private double bestFitness;
	
	/**
	 * Constructor
	 * @param targetNumberOfAssertions is the amount of assertions 
	 */
	public DynAlloyEquivalenceSpecCounter(DynAlloyRunner runner,int genes_num,boolean initialSpecEmpty) {
		if (runner.getNumberOfAssertions() == 0) {
			throw new IllegalArgumentException();
		}
		this.runner = runner;
		counterexamplesValues = ((Double)runner.getNumberOfCounterexamplesAllowed()).intValue()+1;
		amountOfGenes = genes_num;
		this.initialSpecEmpty = initialSpecEmpty;
		calculatedFitness = new HashMap<String,Double>();
		initializeFitnessMatrix();
		itime = System.currentTimeMillis();
		bestFitness = 0;
	}
	
	/**
	 * Initialize the fitness matrix with the amount of genes
	 */
	private void initializeFitnessMatrix() {
		fitnessMatrix = new double[counterexamplesValues][amountOfGenes];
		
		double maxValue = (counterexamplesValues)*amountOfGenes;
		
		for (int i=0;i<counterexamplesValues;i++) {
			for (int j=0;j<amountOfGenes;j++) {
				fitnessMatrix[i][j] = maxValue;
				maxValue--;
			}
		}
		
	}

	/**
	 * Returns the minimum value which represents a possible solution
	 */
	public int minimumSolutionValue() {
		return ((Double)fitnessMatrix[0][amountOfGenes-1]).intValue();
	}
	
	@Override
	protected double evaluate(IChromosome chromosome) {
		InvariantChromosome invChromosome = (InvariantChromosome)chromosome;
		Gene[] genes = invChromosome .getGenes();
		double res = 0;
		if (genes[0] instanceof IntegerGene) {
			int[] runnerParam = new int[genes.length];
			for (int i = 0; i< genes.length; i++) {
				runnerParam[i] = ((IntegerGene) genes[i]).intValue();	
			}
			runner.setRepOKbody(runnerParam);
		} else {
			// Gene is instanceof ExprGene
			ArrayList<Expr> list = new ArrayList<Expr>();
			for (int i = 0; i < genes.length ; i++) {
				ExprGene gene = (ExprGene)genes[i];
				list.add(((ExprGeneValue)gene.getInternalValue()).getExpression());
			}
			runner.setRepOkbodyFromExpressionList(list);
		}

		// If the chromosome has not genes return 0
		if (invChromosome.toString().contains("Alleles:[]")) {
			return 0;
		}
		// If the chromosome has positive counterexamples return 0
		if (runner.hasPositiveCounterexamples()) {
			return 0;
		}
		
		// Get the amount of negative couterexamples of the current chromosome
		Double c = getAmountOfNegativeCounterexamples(invChromosome);
		invChromosome.setAmountOfCounterexamples(c);

		//if (!containsRepeatedGenes(invChromosome)||c==0) {
		// Evaluates just if not contains repeated genes. But if it is a solution, also evaluate it :)
		Double a = runner.totalActiveExpressions(initialSpecEmpty);
		res = (1000 - c) + (1 / (a+1));
		//} else {
		//	res = 0;
		//}
			
		System.out.print(".");
		if (c==0 && res>bestFitness) {
			bestFitness = res;
			int currentTime = (int)(System.currentTimeMillis()-itime)/1000;
			System.out.println();
			System.out.println("SPECIFICATION LEARNED AT: "+currentTime+" seconds.");
			System.out.println("CHROMOSOME FITNESS: "+res);
			//invChromosome.printGenes();
			if (genes[0] instanceof IntegerGene) {
				System.out.println(genesAsSpec(invChromosome));
			} else {
				invChromosome.printGenes();
			}
			System.out.println();
			runner.writeRepOkInFile(ConfigurationProperties.getOutputFileLocation()+"/");
		}
		return res;
		
	}
	public String genesAsSpec(IChromosome chromosome) {
		Gene[] genes = chromosome.getGenes();
		int[] res = new int[chromosome.size()];
		for (int i=0; i< res.length; i++) {
			res[i] = ((IntegerGene) genes[i]).intValue();
		}
		String genesString = "";
		for (int i=0; i<res.length;i++) {
			if (res[i]==1) {
				genesString += runner.getRepOkElementsAsString()[i]+" AND \n";
			} 
			if (res[i]==0) {
				genesString += "NOT "+ runner.getRepOkElementsAsString()[i] +" AND \n";
			}
		}
		return genesString;
	}
	
	/**
	 * Get the counterexamples of the current chromosome
	 */
	private Double getAmountOfNegativeCounterexamples(InvariantChromosome invChromosome) {
		Double fieldExahustiveExamples;
		// Just calculate the amount of counterexamples if the fitness of the current chromosome has not been calculated previously.
		if (calculatedFitness.containsKey(invChromosome.toString())) {
			fieldExahustiveExamples = calculatedFitness.get(invChromosome.toString());
		} else {
			fieldExahustiveExamples = new Double(runner.getCounterexamplesFieldExhaustive());
			calculatedFitness.put(invChromosome.toString(), fieldExahustiveExamples);
		}
		return fieldExahustiveExamples;
	}
	
	/**
	 * Returns true if the given chromosome contains repeated genes
	 */
	private boolean containsRepeatedGenes(InvariantChromosome invChromosome) {
		boolean repeated=false;
		Set<String> genes = new HashSet<String>();
		for (int i =0; i < invChromosome.getGenes().length && !repeated; i++) {
			Gene gene = invChromosome.getGenes()[i];
			if (gene instanceof IntegerGene)
				return false;
			ExprGene exprGene = (ExprGene)gene;
			if (!	exprGene.isDefault() && genes.contains(gene.toString())) {
				repeated=true;
			} else {
				genes.add(gene.toString());
			}
		}
		return repeated;
	}
	
}