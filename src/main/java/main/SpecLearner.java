package main;

import org.jgap.Chromosome;
import org.jgap.Configuration;
import org.jgap.Gene;
import org.jgap.Genotype;
import org.jgap.InvalidConfigurationException;
import org.jgap.impl.BooleanGene;
import org.jgap.impl.DefaultConfiguration;

import geneticalgorithm.fitnessfunction.PassingAssertionsCounter;

public class SpecLearner {
	
	private Configuration conf = new DefaultConfiguration();
	
	private Chromosome foundChromosome = null;

	/**
	 * Constructor
	 * @param boolVectorSize 
	 * @param numberOfAssertions
	 * @throws InvalidConfigurationException
	 */
	public SpecLearner(int boolVectorSize, int numberOfAssertions) throws InvalidConfigurationException {
		if (boolVectorSize <=0 || numberOfAssertions <=0) throw new IllegalArgumentException();
		Gene[] sampleGenes = new Gene[boolVectorSize];
		for (int i = 0; i<boolVectorSize; i++) {
			sampleGenes[i] = new BooleanGene(conf, false);
		}
		Chromosome sampleChromosome = new Chromosome(conf, sampleGenes);
		conf.setSampleChromosome( sampleChromosome );
		conf.setPopulationSize( 2^boolVectorSize/100 ); // setting population size to 1%
													    // of state space size.
		conf.setKeepPopulationSizeConstant(false);
		conf.setFitnessFunction(new PassingAssertionsCounter(numberOfAssertions));
	}
	
	
	public void learnSpec() throws InvalidConfigurationException {
		Genotype population = Genotype.randomInitialGenotype(conf);
		for (int i = 0; i < 100000; i++) {
			population.evolve();
			System.out.println(conf.getFitnessFunction().getFitnessValue(population.getFittestChromosome()));
		}
		foundChromosome = (Chromosome) population.getFittestChromosome();
	}
	
	public boolean[] learnedSpec() {
		Gene[] genes = foundChromosome.getGenes();
		boolean[] res = new boolean[foundChromosome.size()];
		for (int i=0; i< res.length; i++) {
			if (((BooleanGene) genes[i]).booleanValue())
				res[i] = true;
		}
		return res;
	}
}
