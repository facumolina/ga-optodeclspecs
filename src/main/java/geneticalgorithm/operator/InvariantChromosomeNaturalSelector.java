package geneticalgorithm.operator;

import java.util.Collections;
import java.util.Comparator;
import java.util.HashSet;
import java.util.Set;

import org.jgap.Configuration;
import org.jgap.Genotype;
import org.jgap.IChromosome;
import org.jgap.InvalidConfigurationException;
import org.jgap.NaturalSelector;
import org.jgap.Population;

import geneticalgorithm.chromosome.InvariantChromosome;

/**
 * The InvariantChromosomeNaturalSelector implements a NaturalSelector. This selector
 * ensure that the best chromosomes and the best unary chromosomes (those of size one)
 * are preserved in the population for the next generation
 * @author fmolina
 */
public class InvariantChromosomeNaturalSelector extends NaturalSelector {

	/**
   * Stores the chromosomes to be taken into account for selection
   */
  private Population m_chromosomes;
  
  /**
   * Comparator that is concerned about both age and fitness values
   */
  private Comparator m_fitnessValueComparator;
  
  /**
   * Set of already added unary chromosomes
   */
  private Set<String> addedChromosomes;
  
  /**
   * Default constructor.
   * @throws InvalidConfigurationException
   */
  public InvariantChromosomeNaturalSelector()
      throws InvalidConfigurationException {
    this(Genotype.getStaticConfiguration());
  }
  
  public InvariantChromosomeNaturalSelector(final Configuration a_config) throws InvalidConfigurationException {
  	super(a_config);
  	m_chromosomes = new Population(a_config);
  	m_fitnessValueComparator = new FitnessAgeValueComparator();
  	addedChromosomes = new HashSet<String>();
  }
  
  
	@Override
	public void select(int a_howManyToSelect, Population a_from_population, Population a_to_population) {
		int canBeSelected;
		m_chromosomes = a_from_population;
    int chromsSize = m_chromosomes.size();
    if (a_howManyToSelect > chromsSize) {
      canBeSelected = chromsSize;
    }
    else {
      canBeSelected = a_howManyToSelect;
    }
    // Sort the collection of chromosomes previously added for evaluation.
    // Only do this if necessary.
    Collections.sort(m_chromosomes.getChromosomes(),m_fitnessValueComparator);

    // To select a chromosome, we just go thru the sorted list.
    InvariantChromosome selectedChromosome;
    Set<String> unarySelectedGenes = new HashSet<String>();
    for (int i = 0; i < canBeSelected; i++) {
      selectedChromosome = (InvariantChromosome)m_chromosomes.getChromosome(i);
      selectedChromosome.setIsSelectedForNextGeneration(true);
      a_to_population.addChromosome(selectedChromosome);
      if (selectedChromosome.isUnaryAndValid()) {
      	unarySelectedGenes.add(selectedChromosome.getGenes()[0].toString());
      }
    }

    // Also keep in the population the unary chromosomes 
    int i = canBeSelected;
    //System.out.println();
    //System.out.println("UNARY ADDED IN SELECTION");
    while (i < chromsSize) {
    	selectedChromosome = (InvariantChromosome)m_chromosomes.getChromosome(i);
    	if (selectedChromosome.isUnaryAndValid() 
    			//&& !addedChromosome(selectedChromosome) 
    			&& !unarySelectedGenes.contains(selectedChromosome.getGenes()[0].toString())) {
    		selectedChromosome.setIsSelectedForNextGeneration(true);
    		a_to_population.addChromosome(selectedChromosome);
    		unarySelectedGenes.add(selectedChromosome.getGenes()[0].toString());
    		//System.out.println(selectedChromosome.toString());
    	}
    	i++;
    }
    //System.out.println("Total chromosomes to next generation: "+a_to_population.getChromosomes().size());
	}

	/**
	 * Returns true if the given chromosome already was added in a previous selection
	 */
	private boolean addedChromosome(InvariantChromosome iChromosome) {
		String stringGene = iChromosome.getGenes()[0].toString();
		if (addedChromosomes.contains(stringGene))
				return true;
		addedChromosomes.add(stringGene);
		return false;
	}
	
	@Override
	public void empty() {
		// Clear the list of chromosomes
    m_chromosomes.getChromosomes().clear();
	}

	@Override
	public boolean returnsUniqueChromosomes() {
		return true;
	}

	@Override
	protected void add(IChromosome a_chromosomeToAdd) {
		// Check if chromosome already added
    if (m_chromosomes.getChromosomes().contains(a_chromosomeToAdd)) {
      return;
    }
    // New chromosome, insert it into the sorted collection of chromosomes
    a_chromosomeToAdd.setIsSelectedForNextGeneration(false);m_chromosomes.addChromosome(a_chromosomeToAdd);
    // Indicate that the list of chromosomes to add needs sorting.
	}

}
