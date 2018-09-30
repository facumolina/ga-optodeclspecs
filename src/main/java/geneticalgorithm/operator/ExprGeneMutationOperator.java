package geneticalgorithm.operator;

import java.util.LinkedList;
import java.util.List;
import java.util.Vector;

import org.jgap.BaseGeneticOperator;
import org.jgap.Configuration;
import org.jgap.Gene;
import org.jgap.IGeneticOperatorConstraint;
import org.jgap.InvalidConfigurationException;
import org.jgap.Population;
import org.jgap.RandomGenerator;
import org.jgap.data.config.Configurable;

import geneticalgorithm.chromosome.ExprGene;
import geneticalgorithm.chromosome.ExprGeneType;
import geneticalgorithm.chromosome.ExprGeneValue;
import geneticalgorithm.chromosome.InvariantChromosome;
import rfm.dynalloyCompiler.ast.ExprConstant;

/**
 * Mutation operator
 * @author fmolina
 */
public class ExprGeneMutationOperator extends BaseGeneticOperator implements Configurable {

	private double mutationProb;
	
	/**
	 * Constructor
	 * @param a_configuration
	 * @throws InvalidConfigurationException
	 */
	public ExprGeneMutationOperator(Configuration a_configuration)
			throws InvalidConfigurationException {
		super(a_configuration);
	}

	public void setMutationProb(double mProb) {
		if (mProb<0 || mProb>1)
			throw new IllegalArgumentException("Invalid probabilty");
		
		mutationProb = mProb;
	}
	
	public void operate(Population a_population, List a_candidateChromosomes) {
		 if (a_population == null || a_candidateChromosomes == null) {
		      // Population or candidate chromosomes list empty:
		      // nothing to do.
		      // -----------------------------------------------
		      return;
		 }
		
		 int size = a_population.size();
		 IGeneticOperatorConstraint constraint = getConfiguration().getJGAPFactory().getGeneticOperatorConstraint();

		 RandomGenerator generator = getConfiguration().getRandomGenerator();
		 for (int i = 0; i < size; i++) {
			 InvariantChromosome chrom = (InvariantChromosome)a_population.getChromosome(i);
		     Gene[] genes = chrom.getGenes();
		     InvariantChromosome copyOfChromosome = null;
		     // For each Chromosome in the population...
		     		      
		     // Get the positions with active genes (genes which expression is not true)
		     List<Integer> activeGenesPositions = getActivePositions(genes);
		     boolean mutate=false; 
		     double m_mutationRate = chrom.getAmountOfCounterexamples()==0?0.3:1.0;
		     for (int j = 0; j < activeGenesPositions.size(); j++) {		    	 
		    	 mutate = (generator.nextDouble() <= mutationProb);
		    	 if (mutate) {
		    		 int positionToMutate = activeGenesPositions.get(j);
		    		 if (constraint != null) {
		    			 List v = new Vector();
		    			 v.add(chrom);
		    			 if (!constraint.isValid(a_population, v, this)) {
		    				 continue;
		    			 }
		    		 }
		    		 
		    		 if (copyOfChromosome == null) {
		    			 // ...take a copy of it...
		    			 copyOfChromosome = (InvariantChromosome) chrom.clone();
		    			 // ...add it to the candidate pool...
		    			 a_candidateChromosomes.add(copyOfChromosome);

		    			 genes = copyOfChromosome.getGenes();
		    		 }

		    		 // Set the new chromosome with fitness -1 so it will be recalculated
		    		 copyOfChromosome.setFitnessValueDirectly(-1);

		    		 //if (chrom.getAmountOfCounterexamples().compareTo(new Double(0))==0) {
		    		 //	 try {
		    		//	 genes[positionToMutate] = new ExprGene(chrom.getConfiguration(),new ExprGeneValue(ExprConstant.TRUE),null); 
		    			// } catch (InvalidConfigurationException e) {
		    			//	 e.printStackTrace();
		    			// }
		    		 //} else {
		    			 ExprGene toMutate = (ExprGene)genes[positionToMutate];
		    			 toMutate.setAmountOfGenesInChromosome(chrom.getAmountOfActiveGenes());
		    			 toMutate.setIsPartOfSolution(chrom.getAmountOfCounterexamples()==0);
		    			 mutateGene(toMutate, generator);
		    		 //}

		    		 if (activeGenesPositions.size()>1) {
		    			 // The cloned chromosome has more than one gene. So create one new chromosome that
		    			 // contains just the new gene 
		    			 try {
		    				 ExprGeneValue geneValue = (ExprGeneValue)genes[positionToMutate].getAllele();
		    				 if (!geneValue.getExpression().equals(ExprConstant.TRUE)) {
		    					 ExprGene newGene = new ExprGene(copyOfChromosome.getConfiguration(), geneValue.clone(),((ExprGene)genes[positionToMutate]).getDataStructureInformation());
		    					 Gene[] newGenes = new Gene[genes.length];
		    					 newGenes[0]=newGene;
		    					 for (int k=1;k<newGenes.length;k++){
		    						 newGenes[k]=new ExprGene(copyOfChromosome.getConfiguration(),new ExprGeneValue(ExprConstant.TRUE),null);
		    					 }
		    					 InvariantChromosome newUnitaryChromosome = new InvariantChromosome(copyOfChromosome.getConfiguration(),newGenes);
		    					 newUnitaryChromosome.setFitnessValueDirectly(-1);
		    					 a_candidateChromosomes.add(newUnitaryChromosome);
		    					 if (newGene.getValue().getGeneType().equals(ExprGeneType.FORALL_VAR_VALUES_DOUBLE_INT_COMPARISON)) {
		    					 }
		    				 }
		    			 } catch (InvalidConfigurationException e) {
		    				 e.printStackTrace();
		    			 }
		    		 }
		    	 }
		     }
		 }
		 
	}

	/**
	 * Print all the chromosomes
	 */
	private void printChromosomes(List a_candidateChromosomes) {
		System.out.println("Total: "+a_candidateChromosomes.size());
		for (int i=0;i<a_candidateChromosomes.size();i++) {
			Object o = a_candidateChromosomes.get(i);
			System.out.println("Pos"+i+" "+o.toString());
		}
	}
	
	/**
	 * Returns all the positions of the genes array in which the expression is not true
	 * @param genes
	 * @return
	 */
	private List<Integer> getActivePositions(Gene[] genes) {
		LinkedList<Integer> activePositions = new LinkedList<Integer>();
		for (int j = 0; j < genes.length; j++) {
			ExprGene gene = (ExprGene)genes[j];
			if (!gene.getValue().getExpression().equals(ExprConstant.TRUE)) {
				activePositions.add(j);
	    	}
		}
		return activePositions;
	}

	private void mutateGene(final Gene a_gene, final RandomGenerator a_generator) {
		for (int k = 0; k < a_gene.size(); k++) {
			// Retrieve value between 0 and 1 (not included) from generator.
			// Then map this value to range -1 and 1 (-1 included, 1 not).
			// -------------------------------------------------------------
			double percentage = -1 + a_generator.nextDouble() * 2;
			// Mutate atomic element by calculated percentage.
			// -----------------------------------------------
			a_gene.applyMutation(k, percentage);
		}
	}
	  
	public int compareTo(Object arg0) {
		// TODO Auto-generated method stub
		return 0;
	}

}