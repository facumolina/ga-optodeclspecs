package main;

import java.io.File;
import java.io.FileInputStream;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.InputStream;
import java.io.OutputStream;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

import org.jgap.Configuration;
import org.jgap.Gene;
import org.jgap.Genotype;
import org.jgap.InvalidConfigurationException;
import org.jgap.RandomGenerator;
import org.jgap.impl.DefaultConfiguration;
import org.jgap.impl.IntegerGene;

import rfm.dynalloy.Err;
import rfm.dynalloy.SafeList;
import rfm.dynalloyCompiler.ast.Expr;
import rfm.dynalloyCompiler.ast.ExprBinary;
import rfm.dynalloyCompiler.ast.ExprCall;
import rfm.dynalloyCompiler.ast.ExprConstant;
import rfm.dynalloyCompiler.ast.ExprQt;
import rfm.dynalloyCompiler.ast.ExprUnary;
import rfm.dynalloyCompiler.ast.ExprVar;
import rfm.dynalloyCompiler.ast.Sig;
import rfm.dynalloyCompiler.ast.Type;
import rfm.dynalloyCompiler.translator.A4Solution;
import rfm.dynalloyCompiler.translator.A4Tuple;
import rfm.dynalloyCompiler.translator.A4TupleSet;
import utils.DataStructureInformation;
import utils.DynAlloyExpressionsUtils;
import utils.DynAlloySpecLearnerParameters;
import dynalloyWrapper.DynAlloyRunner;
import geneticalgorithm.chromosome.ExprGene;
import geneticalgorithm.chromosome.ExprGeneType;
import geneticalgorithm.chromosome.ExprGeneValue;
import geneticalgorithm.chromosome.ExprGeneValueCloneHandler;
import geneticalgorithm.chromosome.InvariantChromosome;
import geneticalgorithm.fitnessfunction.DynAlloyEquivalenceSpecCounter;
import geneticalgorithm.fitnessfunction.DynAlloyPassingAssertionsCounter;
import geneticalgorithm.operator.ChromosomeCrossoverOperator;
import geneticalgorithm.operator.ExprGeneMutationOperator;
import geneticalgorithm.operator.InvariantChromosomeNaturalSelector;

/**
 * This class represents the specification learner. 
 * @author fmolina
 */
public class DynAlloySpecLearner {
	
	//private Configuration conf = new DefaultConfiguration();
	private Configuration conf = new CustomConfiguration();
	private DynAlloyRunner runner;
	private int genes_num;
	private boolean empty_spec;
	private InvariantChromosome foundChromosome = null;
	private DataStructureInformation dataStructureInformation;
	private DynAlloySpecLearnerParameters parameters;
	
	/**
	 * Constructor
	 * @param filePath 
	 * @throws InvalidConfigurationException
	 */
	public DynAlloySpecLearner(String filePath) throws InvalidConfigurationException {
		//DefaultConfiguration.reset();
		CustomConfiguration.reset();
		File f = new File(filePath);
		if(!f.exists() || f.isDirectory()) throw new IllegalArgumentException();
		//setup a DynAlloyRunner with the file and the default "repOK" name
		runner = new DynAlloyRunner(f,"catalog","repOK");
		setUpFile(f);
		dataStructureInformation = runner.getStructureInformation();
		parameters = new DynAlloySpecLearnerParameters();
		updateParametersAccordingToDataStructureInformation();
		setUpGeneticAlgorithm();
	}
	
	/**
	 * Constructor with parameters
	 */
	public DynAlloySpecLearner(String filePath,DynAlloySpecLearnerParameters parameters) throws InvalidConfigurationException {
		if (parameters==null)
			throw new IllegalArgumentException("The parameters cannot be null");
		//DefaultConfiguration.reset();
		CustomConfiguration.reset();
		File f = new File(filePath);
		if(!f.exists() || f.isDirectory()) throw new IllegalArgumentException();
		//setup a DynAlloyRunner with the filename and the default "repOK" name
		runner = new DynAlloyRunner(f,"catalog","repOK");
		setUpFile(f);
		dataStructureInformation = runner.getStructureInformation();
		this.parameters = parameters;
		updateParametersAccordingToDataStructureInformation();
		setUpGeneticAlgorithm();
	}
	
	/**
	 * Update the parameters according to the data structure information
	 */
	private void updateParametersAccordingToDataStructureInformation() {
		if (dataStructureInformation.getAmountOfDoubleClosuredExpressions()>0)
			parameters.setConsiderSimpleClosuredExpressions(false);
	}
	
	/**
	 * Set up file
	 */
	private void setUpFile(File f)  {
		// The file will be placed in the adequate location for the field exhaustive technique
		// And for the output file
		File destFieldExhaustive = new File(ConfigurationProperties.getFieldExhaustiveDirectory()+"/learning-spec/"+f.getName());
		File dest = new File(ConfigurationProperties.getOutputFileLocation()+"/"+f.getName());
		try {
			copyFileUsingStream(f,destFieldExhaustive);
			copyFileUsingStream(f,dest);
		} catch (Exception e) {
			e.printStackTrace();
		}
	}
	
	/**
	 * Copy the content of the source file to the dest file.
	 */
	private static void copyFileUsingStream(File source, File dest) throws IOException {
    InputStream is = null;
    OutputStream os = null;
    try {
    	is = new FileInputStream(source);
    	os = new FileOutputStream(dest);
    	byte[] buffer = new byte[1024];
    	int length;
    	while ((length = is.read(buffer)) > 0) {
    		os.write(buffer, 0, length);
    	}
    } finally {
    	is.close();
    	os.close();
    }
	}
	
	/**
	 * Set up the genetic algorithm
	 * @throws InvalidConfigurationException
	 */
	private void setUpGeneticAlgorithm() throws InvalidConfigurationException {
		genes_num = runner.getRepOkElements().size();
		empty_spec = genes_num==0?true:false;
		Gene[] sampleGenes;
		if (empty_spec) {
			// Use ExprGene
			genes_num = determineAmountOfGenes();
			sampleGenes =  new Gene[genes_num];
			for (int i = 0; i<genes_num; i++) {
				sampleGenes[i] = new ExprGene(conf,dataStructureInformation);
			}
		} else {
			sampleGenes =  new Gene[genes_num];
			// Use IntegerGene
			for (int i = 0; i<genes_num; i++) {
				sampleGenes[i] = new IntegerGene(conf, 0, 2);
			}
		}
		
		InvariantChromosome sampleChromosome = new InvariantChromosome(conf, sampleGenes);
		conf.setSampleChromosome( sampleChromosome );
		conf.setKeepPopulationSizeConstant(false);
		conf.setPreservFittestIndividual(true);
	}
	
	/**
	 * Set parameters
	 */
	public void setParameters(DynAlloySpecLearnerParameters parameters) {
		this.parameters = parameters;
	}
	
	/**
	 * Determines the amount of genes to be used in the chromosomes
	 */
	private int determineAmountOfGenes() {
		int amountOfEvaluableExpressions = parameters.getConsiderJoinedExpressions()?dataStructureInformation.getAmountOfNonClosuredExpressions():0; 
		int cardinalityExpr = parameters.getConsiderCardinalityExpressions()?dataStructureInformation.calculateAmountCardinalityExpressions():0;
		int amountOfQuantifiedExpressions = (parameters.getConsiderSimpleClosuredExpressions()?dataStructureInformation.getAmountOfSimpleClosuredExpressions()*2:0)+
				(parameters.getConsiderDoubleClosuredExpressions()?dataStructureInformation.getAmountOfDoubleClosuredExpressions()*2:0);
		int n =  amountOfEvaluableExpressions+amountOfQuantifiedExpressions+cardinalityExpr;
		return n*2;
	}
	
	/**
	 * Get the initial chromosomes
	 */
	private List<InvariantChromosome> getInitialChromosomes() throws InvalidConfigurationException{
		LinkedList<InvariantChromosome> chromosomes = new LinkedList<InvariantChromosome>();
		if (empty_spec) {
			// The initial specification is empty
			A4Solution positiveExample = runner.generateExample(true);
			A4Solution negativeExample = runner.generateExample(false);
			// Save the null signature
			dataStructureInformation.saveSignaturesInformation(positiveExample);
			int examplesConsidered = 0;
			while (examplesConsidered < parameters.getAmountOfExamplesForInitialChromosomesGeneration()) {
				if (positiveExample.satisfiable()&&negativeExample.satisfiable()) {
					try {
						chromosomes.addAll(generateChromosomesFromExample(positiveExample,true));
						chromosomes.addAll(generateChromosomesFromExample(negativeExample,false));
						positiveExample = positiveExample.next();
						negativeExample = negativeExample.next();
						examplesConsidered += 2;
					} catch (Err e) {
						e.printStackTrace();
					}
				} else {
					break;
				}
			}
		} else {
			// The initial specification is not empty. So for each gene g creates one chromosome
			// in which g is active and all the other genes are not considered (using the true expression). 
			Gene[] genes;
			for (int i = 0; i<genes_num; i++) {
				genes = new Gene[genes_num];
				for (int j=0; j < genes_num; j++) {
					IntegerGene gene = new IntegerGene(conf, 0, 2);
					if (i==j) {
						gene.setAllele(new Integer(1));
					} else {
						gene.setAllele(new Integer(2));
					}
					genes[j] = gene;
				}
				InvariantChromosome chromosome = new InvariantChromosome(conf,genes);
				chromosomes.add(chromosome);
			}
		}
		return chromosomes;
	}
	
	/**
	 * Generates a list of chromosomes from an example 
	 * @param example is the structure example from which the chromosomes will be built
	 * @param isPositive is true if the example is positive
	 */
	private List<InvariantChromosome> generateChromosomesFromExample(A4Solution example, boolean isPositive) throws InvalidConfigurationException,Err {
		LinkedList<InvariantChromosome> chromosomes = new LinkedList<InvariantChromosome>();
		List<Gene> genes = createGenesFromExample(example,isPositive);
		
		if (parameters.getInitialChromosomesUnary()) {
			// For each gene create one chromosome that contains just one gene at the first position: [gene, true, true, ... , true]
	 		for (int i=0;i<genes.size();i++) {
				Gene[] new_genes = new Gene[genes_num];
				ExprGene exprGene = (ExprGene)genes.get(i);
				ExprGene newExprGene = new ExprGene(conf,exprGene.getValue().clone(),dataStructureInformation);
				if (!isPositive && !(exprGene.getValue().getExpression() instanceof ExprQt) && !(exprGene.getValue().getExpression() instanceof ExprCall)) {
					// Negate the expression
					newExprGene.getValue().setExpression(DynAlloyExpressionsUtils.negateExpression(newExprGene.getValue().getExpression()),true);
				}
				// Always the gene must be in the first position
				new_genes[0]=newExprGene;
				// The rest of the genes vales is  : true
				for (int j=1;j<new_genes.length;j++) {
					new_genes[j]= new ExprGene(conf,new ExprGeneValue(ExprConstant.TRUE),dataStructureInformation);
				}
				InvariantChromosome chromosome = new InvariantChromosome(conf,new_genes);
				chromosome.setFitnessValueDirectly(-1);
				chromosomes.add(chromosome);
			}
		} else {
			// Create chromosomes with each gene randomly picked.
	 		genes.add(new ExprGene(conf,new ExprGeneValue(ExprConstant.TRUE), dataStructureInformation));
	 		int chromosomesToCreate = parameters.getPopulationSize()/parameters.getAmountOfExamplesForInitialChromosomesGeneration();
	 		for (int i=0; i < chromosomesToCreate;i++) {
	 			Gene[] new_genes = new Gene[genes_num];
	 			Set<Integer> usedGenes = new HashSet<Integer>();
	 			for (int j=0;j<genes_num;j++) {
	 				RandomGenerator generator = conf.getRandomGenerator();
	 				int r = generator.nextInt(genes.size());
	 				if (usedGenes.add(r)) 
	 					new_genes[j] = genes.get(r);
	 				else
	 					new_genes[j] = ((ExprGene)genes.get(r)).clone();
	 			}
	 			InvariantChromosome chromosome = new InvariantChromosome(conf,new_genes);
				chromosome.setFitnessValueDirectly(-1);
				chromosomes.add(chromosome);
	 		}
		}
		return chromosomes;
	}

	/**
	 * Creates the genes that represents the example
	 */
	private List<Gene> createGenesFromExample(A4Solution example,boolean isPositive) {
		// Get the evaluable expressions for the current example
		List<Expr> evaluableJoinedExpressions = dataStructureInformation.getCommandJoinedExpressions(example.getAllSkolems());
		List<Expr> evaluableJoinedExpressionsOfTypeInt = dataStructureInformation.getCommandJoinedExpressionsInt(example.getAllSkolems());
		evaluableJoinedExpressions.addAll(evaluableJoinedExpressionsOfTypeInt);
		List<Expr> evaluableSimpleClosuredExpressions = dataStructureInformation.getCommandSimpleClosuredExpressions(example.getAllSkolems());
		List<Expr> evaluableDoubleClosuredExpressions = dataStructureInformation.getCommandDoubleClosuredExpressions(example.getAllSkolems());
		List<Gene> genes = new LinkedList<Gene>();
		try {
			// Create the chromosome genes 
				
			// Create the genes according to the evaluation of each evaluable expression
			if (parameters.getConsiderJoinedExpressions())
				genes.addAll(createsGenesFromEvaluableJoinedExpressions(evaluableJoinedExpressions,example,isPositive));
						
			// Create genes quantifying the simple closured expressions
			if (parameters.getConsiderSimpleClosuredExpressions()) 
				genes.addAll(createsGenesFromSimpleClosuredExpressions(evaluableSimpleClosuredExpressions,evaluableJoinedExpressionsOfTypeInt));
				
			// Create genes quantifying the double closured expressions
			if (parameters.getConsiderDoubleClosuredExpressions())
				genes.addAll(createsGenesFromDoubleClosuredExpressions(evaluableDoubleClosuredExpressions,evaluableJoinedExpressionsOfTypeInt));	
					
		} catch (Exception e) {
			e.printStackTrace();
		} 
		dataStructureInformation.clearExpressionsByEvaluationValue();
		return genes;
	}
	
	/**
	 * Creates genes from joined expressions and its evaluation result.
	 * Given an expression e, the gene expression built from e can be:
	 *  - e = null   when the evaluation result is null
	 *  - e != null  when the evaluation result is not null
	 *  - no e       when the evaluation result is empty
	 */
	private List<Gene> createsGenesFromEvaluableJoinedExpressions(List<Expr> evaluableJoinedExpressions,A4Solution example,boolean isPositive) throws Exception {
		List<Gene> genes = new LinkedList<Gene>();
		for (int j = 0; j < evaluableJoinedExpressions.size(); j++) {
			Expr evaluableExpr = evaluableJoinedExpressions.get(j);
			A4TupleSet evaluation = (A4TupleSet)example.eval(evaluableExpr);
			Expr correctedExpr = correctExpressionName(evaluableExpr);
			if (!correctedExpr.type().is_int()) {
			 genes.add(buildExprGeneFromEvaluation(example,correctedExpr,evaluation,isPositive));  
			}
		}
		return genes;
	}
	
	/**
	 * Creates genes according to the equality or inequality between the values of each pair of expressions
	 * only if the intersection between the types of the expressions being compared is not empty.
	 * Given the expressions e and f, creates genes with the following expressions:
	 *  - e = f
	 *  - e != f
	 */
	private List<Gene> createsGenesComparingEvauableExpressions(List<Expr> evaluableJoinedExpressions) throws InvalidConfigurationException {
		List<Gene> genes = new LinkedList<Gene>();
		Object[] values = dataStructureInformation.getExpressionsByEvaluationValue().keySet().toArray();
		for (int j = 0; j < values.length ; j++ ) {
			List<Expr> expressionsThatEvaluateToValue = dataStructureInformation.getExpressionsByEvaluationValue().get(values[j]);
			// Add a equality gene for each pair of expressions that evaluate to the same value
			for (int k = 0; k < expressionsThatEvaluateToValue.size() - 1; k++) {
				Expr leftExpression = expressionsThatEvaluateToValue.get(k);
				for (int l = k+1; l < expressionsThatEvaluateToValue.size() ; l++) {
					Expr rightExpression = expressionsThatEvaluateToValue.get(l);
					Expr geneExpression = ExprBinary.Op.EQUALS.make(null, null, leftExpression, rightExpression);
					ExprGeneValue newValue = new ExprGeneValue(geneExpression,ExprGeneType.EQUALITY);
					genes.add(new ExprGene(conf,newValue,dataStructureInformation));
				}
			}

			// Add an inequality gene for each of pair in which the left side expression evaluates to the current value
			// and the right side expression evaluates to some other value
			for (Expr leftExpression : expressionsThatEvaluateToValue) {
				for (int k = j+1 ; k < values.length ; k++) {
					List <Expr> rightExpressions = dataStructureInformation.getExpressionsByEvaluationValue().get(values[k]);
					for (Expr rightExpression : rightExpressions) {
						if (leftExpression.type().intersects(rightExpression.type())) {
							Expr geneExpression = ExprBinary.Op.NOT_EQUALS.make(null, null, leftExpression, rightExpression);
							ExprGeneValue newValue = new ExprGeneValue(geneExpression,ExprGeneType.EQUALITY);
							genes.add(new ExprGene(conf,newValue,dataStructureInformation));
						}
					}
				}
			}
					
		}
		return genes;
	}
	
	/**
	 * Creates genes from simple closured expressions considering:
	 * - Quantified expressions with body predicating about shapes
	 * - Quantified expressions with body predicating about values
	 */
	private List<Gene> createsGenesFromSimpleClosuredExpressions(List<Expr> simpleClosuredExpressions,List<Expr> joinedExpressionsOfTypeInt) throws InvalidConfigurationException,Err {
		List<Gene> genes = new LinkedList<Gene>();
		for (int j = 0; j < simpleClosuredExpressions.size(); j++) {
			Expr evaluableExpr = simpleClosuredExpressions.get(j);
			Expr correctedEvaluableExpr = correctExpressionName(evaluableExpr);
			
			// Create genes with expressions which body is a predicate about shapes
			genes.addAll(createsGenesFromSimpleClosuredExpressionsForShape(correctedEvaluableExpr));
			
			// Create genes with expressions which body is a predicate about values
			genes.addAll(createsGenesFromSimpleClosuredExpressionsForValues(correctedEvaluableExpr));
			
			if (parameters.getConsiderCardinalityExpressions()) {
				// For each expression i of type int: #(e.*f)=i 
				for(int k = 0; k < joinedExpressionsOfTypeInt.size(); k++) {
				
					Expr correctedIntExpr = correctExpressionName(joinedExpressionsOfTypeInt.get(k));
					ExprGeneValue geneValue = createsCardinalityExpression(correctedEvaluableExpr,correctedIntExpr);
					genes.add(new ExprGene(conf,geneValue,dataStructureInformation));
					
				}
			}
		}
		return genes;
	}
	
	/**
	 * Creates genes from simple closured expressions. 
	 * Given a simple closured expression e.*f creates genes with the following expressions:
	 * - (all + some) n : e.*f : n != null
	 * - (all + some) n : e.*f : n.f != null
	 * - (all + some) n : e.*f : n != n.f
	 * - (all + some) n : e.*f : n in n.^f 
	 * @throws InvalidConfigurationException 
	 */
	private List<Gene> createsGenesFromSimpleClosuredExpressionsForShape(Expr simpleClosuredExpr) throws InvalidConfigurationException {
		List<Gene> genes = new LinkedList<Gene>();
		ExprGeneValue geneValue;
		
		// (all + some) n : e.*f : n != null
		//geneValue = createsQtExpressionVarPredicate(correctedEvaluableExpr,"all");
			
		// (all + some) n : e.*f : n.f != null
		//geneValue = createsQtExpressionNextVarPredicate(correctedEvaluableExpr,"all");
			
		// (all + some) n : e.*f : n != n.f
		geneValue = createsQtExpressionVarVarPredicate(simpleClosuredExpr,"all");
		genes.add(new ExprGene(conf,geneValue,dataStructureInformation));
			
		// (all + some) n : e.*f : n in n.^f
		geneValue = createsQtExpressionVarSetPredicate(simpleClosuredExpr, "all");
		genes.add(new ExprGene(conf,geneValue,dataStructureInformation));
		
		return genes;
	}
	
	/**
	 * Creates genes from simple closured expressions for values
	 * If the type of the variable n is T, then for each relation r : T -> AnotherType
	 * creates the following quantified expressions:
	 * - all n : e.*f : (n.next != Null) -> n.value = n.next.value 
	 */
	private List<Gene> createsGenesFromSimpleClosuredExpressionsForValues(Expr simpleClosuredExpr) throws InvalidConfigurationException,Err {
		
		Type typeOfElementsInSet = DynAlloyExpressionsUtils.getTypeOfElementsInSet(simpleClosuredExpr);
		List<Expr> joinableExpressions = dataStructureInformation.getJoineableExpressionsOfCurrentType(typeOfElementsInSet);
		
		List<Gene> genes = new LinkedList<Gene>();
		ExprGeneValue geneValue;
		
		// For each joineable expr generate the quantified expressions
		for (Expr joineableExpr : joinableExpressions) {
			
			if (typeOfElementsInSet.equals(joineableExpr.type()))
				continue;
			
			Type returnType = dataStructureInformation.getReturnType(joineableExpr.type());

			if (returnType.is_int()) {
				// The return type is int
				if (ConfigurationProperties.getIntEvaluations()) {
					// Generates expressions comparing the integer values
					geneValue = createsSimpleQtExpressionVarValueVarValueComparisonPredicate(simpleClosuredExpr,joineableExpr,returnType,ExprQt.Op.ALL);
					genes.add(new ExprGene(conf,geneValue,dataStructureInformation));			
				}
			} else {
				// The return type is not int
				//Expr value = DataStructureInformation.getRandomValueForType(returnType);
			}
		}
		return genes;
	}

	/**
	 * Creates genes from double closured expressions considering:
	 * - Quantified expressions with body predicating about shapes
	 * - Quantified expressions with body predicating about values
	 */
	private List<Gene> createsGenesFromDoubleClosuredExpressions(List<Expr> doubleClosuredExpressions,List <Expr> joinedExpressionsOfIntType) throws InvalidConfigurationException,Err {
		List<Gene> genes = new LinkedList<Gene>();
		for (int j = 0; j < doubleClosuredExpressions.size() ;j++) {
			Expr evaluableExpr = doubleClosuredExpressions.get(j);
			Expr correctedEvaluableExpr = correctExpressionName(evaluableExpr);
			
			// Create genes with expressions which body is a predicate about shapes
			genes.addAll(createsGenesFromDoubleClosuredExpressionsForShape(correctedEvaluableExpr));
			
			// Create genes with expressions which body is a predicate about values
			genes.addAll(createsGenesFromDoubleClosuredExpressionsForValues(correctedEvaluableExpr));
			
			if (parameters.getConsiderCardinalityExpressions()) {
				// For each expression i of type int: #(e.*f)=i 
				for(int k = 0; k < joinedExpressionsOfIntType.size(); k++) {	
					Expr correctedIntExpr = correctExpressionName(joinedExpressionsOfIntType.get(k));
					ExprGeneValue geneValue = createsCardinalityExpression(correctedEvaluableExpr,correctedIntExpr);
					genes.add(new ExprGene(conf,geneValue,dataStructureInformation));		
				}
			}
		}
		return genes;
	}
	
	/**
	 * Creates genes from double closured expressions for shape
	 * - all n: e.*(f+g) : n != null
	 * - all n: e.*(f+g) : n.f != null
	 * - all n: e.*(f+g) : n.g != null
	 * - all n: e.*(f+g) : n != n.f
	 * - all n: e.*(f+g) : n != n.g
	 * - all n: e.*(f+g) : n.f != n.g
	 * - all n: e.*(f+g) : n in n.^f
	 * - all n: e.*(f+g) : n in n.^g
	 * - all n: e.*(f+g) : n in n.^(f+g)
	 * - all n: e.*(f+g) : n.f.*(f+g) in n.g.*(f+g)
	 */
	private List<Gene> createsGenesFromDoubleClosuredExpressionsForShape(Expr doubleClosuredExpr) throws InvalidConfigurationException,Err {
		List<Gene> genes = new LinkedList<Gene>();
		ExprGeneValue geneValue;
			
		// (all + some) n: e.*(f+g) : n != null
		// geneValue = createsQtExpressionVarPredicate(correctedEvaluableExpr, "all");
		// (all + some) n: e.*(f+g) : n.f != null
		// (all + some) n: e.*(f+g) : n.g != null
			
		// (all + some) n: e.*(f+g) : n != n.f
		//geneValue = createsQtExpressionVarVarPredicate(doubleClosuredExpr, "all",1);
		//genes.add(new ExprGene(conf,geneValue,dataStructureInformation));
		// (all + some) n: e.*(f+g) : n != n.g
		geneValue = createsQtExpressionVarVarPredicate(doubleClosuredExpr, "all",2);
		genes.add(new ExprGene(conf,geneValue,dataStructureInformation));
		// (all + some) n: e.*(f+g) : n.f != n.g
		/*geneValue = createsQtExpressionVarVarPredicate(doubleClosuredExpr, "all",3);
		genes.add(new ExprGene(conf,geneValue));
			
		// (all + some) n : e.*(f+g) : n = n.f.g
		
		// (all + some) n: e.*(f+g) : n in n.^f
		geneValue = createsQtExpressionVarSetPredicate(doubleClosuredExpr,"all",1);
		genes.add(new ExprGene(conf,geneValue));
		// (all + some) n: e.*(f+g) : n in n.^g
		geneValue = createsQtExpressionVarSetPredicate(doubleClosuredExpr,"all",2);
		genes.add(new ExprGene(conf,geneValue));*/
		// (all + some) n: e.*(f+g) : n in n.^(f+g)
		geneValue = createsQtExpressionVarSetPredicate(doubleClosuredExpr,"all");
		genes.add(new ExprGene(conf,geneValue,dataStructureInformation));
			
		//geneValue = createsQtExpressionVarSetPredicate(correctedEvaluableExpr,"some");
		//genes.add(new ExprGene(conf,geneValue));
				
		// all n: e.*(f+g) : n.f.*(f+g) != n.g.*(f+g)
		geneValue = createsQtExpressionSetSetPredicate(doubleClosuredExpr,"all");
		genes.add(new ExprGene(conf,geneValue,dataStructureInformation));
	
		return genes;
	}
	
	/**
	 * Creates genes from double closured expressions for values
	 * If the type of the variable n is T, then for each relation r : T -> AnotherType
	 * creates the following quantified expressions
	 * - all n: e.*(f+g) : n.r != null
	 * - all n: e.*(f+g) : n.r != n.f.r
	 * - all n: e.*(f+g) : n.r != n.g.r
	 * - all n: e.*(f+g) : n.f.r != n.g.r
	 * - all n: e.*(f+g) : (n.r = v) => (n.f.r = v)
	 * - all n: e.*(f+g) : (n.r = v) => (n.g.r = v)  
	 * - all n: e.*(f+g) : n.r in n.^f.r
	 * - all n: e.*(f+g) : n.r in n.^g.r
	 * - all n: e.*(f+g) : n.r in n.^(f+g).r
	 * - all n: e.*(f+g) : n.f.*(f+g).r in n.g.*(f+g).r
	 */
	private List<Gene> createsGenesFromDoubleClosuredExpressionsForValues(Expr doubleClosuredExpr) throws InvalidConfigurationException,Err {
		
		Type typeOfElementsInSet = DynAlloyExpressionsUtils.getTypeOfElementsInSet(doubleClosuredExpr,1);
		List<Expr> joinableExpressions = dataStructureInformation.getJoineableExpressionsOfCurrentType(typeOfElementsInSet);
		
		List<Gene> genes = new LinkedList<Gene>();
		ExprGeneValue geneValue;
		
		// For each joineable expr generate the quantified expressions
		for (Expr joineableExpr : joinableExpressions) {
			
			Type returnType = dataStructureInformation.getReturnType(joineableExpr.type());
			
			if (dataStructureInformation.typeContains(typeOfElementsInSet, returnType))
				continue;
			
			if (returnType.is_int()) {
				
				if (ConfigurationProperties.getIntEvaluations()) {
					// all n: e.*(f+g) : (n.f != Null) => (n.r = n.f.r) AND (n.g != Null) => n.r = n.g.r
					geneValue = createsDoubleQtExpressionVarValueVarValueComparisonPredicate(doubleClosuredExpr,joineableExpr,returnType,ExprQt.Op.ALL);
					genes.add(new ExprGene(conf,geneValue,dataStructureInformation));
					
					// all n: e.*(f+g) : 
					//   (all m: n.f.*(f+g)-Null : n.r = m.r)
					//   and
					//   (all m: n.g.*(f+g)-Null : n.r = m.r)
					geneValue = createsDoubleQtExpressionWithTwoQuantificationsAboutValuesPredicate(doubleClosuredExpr,joineableExpr,returnType,ExprQt.Op.ALL);
					genes.add(new ExprGene(conf,geneValue,dataStructureInformation));
				}
			} else {
				Expr value = DataStructureInformation.getRandomValueForType(returnType);
				if (value!=null){
					// all n: e.*(f+g) : (n.r = v) => (n.f.r = v)
					//geneValue = createsQtExpressionVarValueVarValuePredicate(doubleClosuredExpr,joineableExpr,returnType,value,"all",1);
					//genes.add(new ExprGene(conf,geneValue));
			
					// all n: e.*(f+g) : (n.r = v) => (n.g.r = v)
					//geneValue = createsQtExpressionVarValueVarValuePredicate(doubleClosuredExpr,joineableExpr,returnType,value,"all",2);
					//genes.add(new ExprGene(conf,geneValue));
				
					// all n: e.*(f+g) : (n.r = v) => (n.f.r = v) and (n.g.r = v)
					geneValue = createsQtExpressionVarValueVarValuePredicate(doubleClosuredExpr,joineableExpr,returnType,value,"all",3);
					genes.add(new ExprGene(conf,geneValue,dataStructureInformation));
				}
			
			}
		}
		return genes;
	}
	
	/**
	 * Given a closured expression e.*f and an expression i of type int
	 * creates the gene value with the expression #(e.*f) = i
	 */
	private ExprGeneValue createsCardinalityExpression(Expr closuredExpression,Expr intExpr) throws Err {
		Expr cardinalityExpression = DynAlloyExpressionsUtils.createsCardinalitySetEqualsToIntExpr(closuredExpression,intExpr);
		return new ExprGeneValue(cardinalityExpression,ExprGeneType.CARDINALITY);
	}
	
	/**
	 * Given a closured expression e.*f and a quantification operator
	 * creates the expression op n : e.*f : n != null
	 */
	private ExprGeneValue createsQtExpressionVarPredicate(Expr closuredExpression, String op) {
		// TODO Auto-generated method stub
		return null;
	}
	
	/**
	 * Given a closured expression e.*f and a quantification operator
	 * creates the expression op n : e.*f : n.f != null
	 */
	private ExprGeneValue createsQtExpressionNextVarPredicate(Expr closuredExpression, String op) {
		// TODO Auto-generated method stub
		return null;
	}

	/**
	 * Given a closured expression e.*f and a quantification operator
	 * creates the gene value with the expression op n : e.*f : n != n.f
	 */	
	private ExprGeneValue createsQtExpressionVarVarPredicate(Expr closuredExpression, String op) {
		ExprQt qtExpr;
		ExprGeneType geneType;
		if (op.equals("all")) {
			qtExpr = (ExprQt)DynAlloyExpressionsUtils.createsQuantifiedExpressionCurrentAndNextNotEquals(closuredExpression, ExprQt.Op.ALL);
			geneType = ExprGeneType.FORALL_VAR_VAR;
		} else {
			qtExpr = (ExprQt)DynAlloyExpressionsUtils.createsQuantifiedExpressionCurrentAndNextNotEquals(closuredExpression, ExprQt.Op.SOME);
			geneType = ExprGeneType.SOME_VAR_VAR;
		}
		ExprGeneValue geneValue = new ExprGeneValue(qtExpr,geneType);
		return geneValue;
	}
	
	/**
	 * Given a closured expression e.*(f+g), a quantification operator and an int i
	 * creates a gene value with expression:
	 *  - op n : e.*(f+g) : n != n.f if i = 1
	 *  - op n : e.*(f+g) : n != n.g if i = 2
	 *  - op n : e.*(f+g) : n.f != n.g if i = 3
	 */	
	private ExprGeneValue createsQtExpressionVarVarPredicate(Expr closuredExpression, String op,int i) {
		ExprQt qtExpr;
		ExprGeneType geneType;
		if (op.equals("all")) {
			qtExpr = (ExprQt) DynAlloyExpressionsUtils.createsQuantifiedExpressionCurrentAndNextNotEquals(closuredExpression,ExprQt.Op.ALL,i);
			geneType = ExprGeneType.FORALL_VAR_VAR;
		} else {
			qtExpr = (ExprQt) DynAlloyExpressionsUtils.createsQuantifiedExpressionCurrentAndNextNotEquals(closuredExpression,ExprQt.Op.SOME,i);
			geneType = ExprGeneType.SOME_VAR_VAR;
		}
		ExprGeneValue geneValue = new ExprGeneValue(qtExpr,geneType);
		return geneValue;
	}
	
	/**
	 * Given a closured expression e.*(f+g), an expression r, a quantification operator and an int i
	 * creates a gene value with expression
	 * - op n : e.*(f+g) : n.r = v => n.f.r = v if i = 1
	 * - op n : e.*(f+g) : n.r = v => n.g.r = v if i = 2
	 * where v is possiblev value for an expression like r
	 */
	private ExprGeneValue createsQtExpressionVarValueVarValuePredicate(Expr closuredExpression,Expr toJoinWithVarExpr,Type returnTypeExpr,Expr value,String op,int i) throws Err {
		ExprQt qtExpr;
		ExprGeneType geneType;
		if (op.equals("all")) {
			qtExpr = (ExprQt) DynAlloyExpressionsUtils.createsQuantifiedExpressionCurrentValueImpliesNextValueEqual(closuredExpression,toJoinWithVarExpr,returnTypeExpr,value,ExprQt.Op.ALL,i);
			geneType = ExprGeneType.FORALL_VAR_VALUE_VAR_VALUE;
		} else {
			qtExpr=null;
			geneType=null;
		}
		ExprGeneValue geneValue = new ExprGeneValue(qtExpr,geneType);
		return geneValue;
	}
	
	/**
	 * Given a simple closured expression e.*f, an expression r and a quantification operator creates a gene value with expression
	 * - op n : e.*f : n.r = n.f.r
	 */
	private ExprGeneValue createsSimpleQtExpressionVarValueVarValueComparisonPredicate(Expr closuredExpr,Expr toJoinWithVarExpr,Type returnTypeExpr,ExprQt.Op op) throws Err{
		
		Expr qtExpr = (ExprQt) DynAlloyExpressionsUtils.createsQuantifiedExpressionCurrentValueOpNextValue(closuredExpr,toJoinWithVarExpr,op,DataStructureInformation.nullSig);
		ExprGeneType geneType =ExprGeneType.FORALL_VAR_VALUE_VAR_VALUE_INT_COMPARISON;

		ExprGeneValue geneValue = new ExprGeneValue(qtExpr,geneType);
		return geneValue;
	}
	
	/**
	 * Given a double closured expression e.*(f+g), an expression r and a quantification operator creates a gene value with expression
	 * - op n : e.*(f+g) | ((n.f!=Null)=> n.r = n.f.r) AND ((n.g!=Null)=> n.r = n.g.r)
	 */
	private ExprGeneValue createsDoubleQtExpressionVarValueVarValueComparisonPredicate(Expr closuredExpr,Expr toJoinWithVarExpr,Type returnTypeExpr,ExprQt.Op op) throws Err {
		
		Expr qtExpr = (ExprQt) DynAlloyExpressionsUtils.createsQuantifiedExpressionCurrentValueOpFstNextValueCurrentValueOpSndNextValue(closuredExpr,toJoinWithVarExpr,op,DataStructureInformation.nullSig);
		ExprGeneType geneType =ExprGeneType.FORALL_VAR_VALUES_DOUBLE_INT_COMPARISON;

		ExprGeneValue geneValue = new ExprGeneValue(qtExpr,geneType);
		return geneValue;
	}
	
	/**
	 * Given a double closured expression e.*(f+g), an expression r and a quantification operator creates a gene value with expression
	 * - op n : e.*(f+g) | (op m: e.f.*(f+g)-Null : n.r=m.r) AND (op m: e.g.*(f+g)-Null : n.r=m.r)
	 */
	private ExprGeneValue createsDoubleQtExpressionWithTwoQuantificationsAboutValuesPredicate(Expr closuredExpr,Expr toJoinWithVarExpr,Type returnTypeExpr,ExprQt.Op op) throws Err {
		Expr qtExpr = (ExprQt) DynAlloyExpressionsUtils.createsQuantifiedExpressionQtCurrentValueOpFstNextValueQtCurrentValueOpSndNextValue(closuredExpr,toJoinWithVarExpr,op,DataStructureInformation.nullSig);
		ExprGeneType geneType = ExprGeneType.FORALL_VAR_VALUES_DOUBLE_QT_INT_COMPARISON;

		ExprGeneValue geneValue = new ExprGeneValue(qtExpr,geneType);
		return geneValue;
	}
	
	/**
	 * Given an evaluable closured expression e.*f and a quantification operator  
	 * creates the gene value op n : e.*f : n in n.^f
	 */
	private ExprGeneValue createsQtExpressionVarSetPredicate(Expr closuredExpression,String op) {
		ExprQt qtExpr;
		ExprGeneType geneType;
		if (op.equals("all")) {
			qtExpr = (ExprQt) DynAlloyExpressionsUtils.createsQuantifiedExpressionVarInSet(closuredExpression, ExprQt.Op.ALL);
			geneType = ExprGeneType.FORALL_VAR_SET;
		} else {
			qtExpr = (ExprQt) DynAlloyExpressionsUtils.createsQuantifiedExpressionVarInSet(closuredExpression, ExprQt.Op.SOME);
			geneType = ExprGeneType.SOME_VAR_SET;
		}
		ExprGeneValue geneValue = new ExprGeneValue(qtExpr,geneType);
		return geneValue;
	}
	
	/**
	 * Given an evaluable closured expression e.*(f+g), a quantification operator and an int i
	 * creates a gene value with the expression :
	 *  - op n : e.*f : n in n.^f if i=1 
	 *  - op n : e.*f : n in n.^g if i=2
	 */
	private ExprGeneValue createsQtExpressionVarSetPredicate(Expr closuredExpression,String op,int i) {
		// Create expression
		ExprQt qtExpr;
		ExprGeneType geneType;
		if (op.equals("all")) {
			qtExpr = (ExprQt) DynAlloyExpressionsUtils.createsQuantifiedExpressionVarInSet(closuredExpression, ExprQt.Op.ALL, i);
			geneType = ExprGeneType.FORALL_VAR_SET;
		} else {
			qtExpr = (ExprQt) DynAlloyExpressionsUtils.createsQuantifiedExpressionVarInSet(closuredExpression, ExprQt.Op.SOME, i);
			geneType = ExprGeneType.SOME_VAR_SET;
		}
		ExprGeneValue geneValue = new ExprGeneValue(qtExpr,geneType); 
		return geneValue;
	}
	
	/**
	 * Given a double closured expression e.*(f+g) and a quantification operator
	 * creates the expression op n : e.*(f+g) : e.f.*(f+g) != e.g.*(f+g) 
	 */
	private ExprGeneValue createsQtExpressionSetSetPredicate(Expr closuredExpression,String op) {
		ExprQt qtExpr;
		ExprGeneType geneType;
		if (op.equals("all")) {
			qtExpr = (ExprQt) DynAlloyExpressionsUtils.createsQuantifiedtExpressionSetNotEqualSet(closuredExpression, ExprQt.Op.ALL);
			geneType = ExprGeneType.FORALL_SET_SET;
		} else {
			qtExpr = (ExprQt) DynAlloyExpressionsUtils.createsQuantifiedtExpressionSetNotEqualSet(closuredExpression, ExprQt.Op.SOME);
			geneType = ExprGeneType.SOME_SET_SET;
		}
		ExprGeneValue geneValue = new ExprGeneValue(qtExpr,geneType);
		return geneValue;
	}
	
	/**
	 * Corrects the expression name of the given expression for allow to evaluate it 
	 * @param expression 
	 * @return the same expression with a evaluable name
	 */
	private Expr correctExpressionName(Expr expression) {
		if (expression instanceof ExprVar) {
			return runner.translateExpression((ExprVar)expression);
		} else {
			if (expression instanceof ExprUnary) {
				// The expression is closure
				ExprUnary closure = ((ExprUnary)expression);
				return closure.op.make(null, correctExpressionName(closure.sub));
			} else {
				// The expression is a joined expr
				Expr leftExpr = ((ExprBinary)expression).left;
				Expr rightExpr = ((ExprBinary)expression).right;
					
				Expr newLeftExpr = correctExpressionName(leftExpr);
				Expr newRightExpr = correctExpressionName(rightExpr);
				return ((ExprBinary)expression).op.make(null, null, newLeftExpr, newRightExpr);
			}
			
		}
	}
	
	/**
	 * Given an evaluated expression and the evaluation result, build an exprgene which expression = evaluatedExpression op null if the evaluation result
	 * is a value or expression = no evaluatedExpression if the evaluation result is empty. 
	 * @param expression
	 * @param evaluation
	 * @param isPositive
	 * @return
	 */
	private Gene buildExprGeneFromEvaluation(A4Solution example,Expr evaluatedExpression,A4TupleSet evaluation,boolean isPositive) throws InvalidConfigurationException {
		ExprVar nullExpr = example.getAllAtoms().iterator().next();
		SafeList<Sig> signatureList = example.getAllReachableSigs();
		Sig nullSig = signatureList.get(5);
		
		Expr evaluationExpr = evaluationToExpression(example,evaluation);
		// Add the expression to the list of expressions which value is evaluationExpr
		dataStructureInformation.addEvaluationToValue(evaluatedExpression, evaluationExpr.toString());
		// Add the possible evaluation to the current type
		dataStructureInformation.addEvaluationToSignature(evaluatedExpression.type(), evaluationExpr);
		
		// Build the new gene
		Expr geneExpression;
		ExprGene exprGene = null;
		ExprGeneValue geneValue;
		
		if (evaluatedExpression.type().is_int()) {
			// The evaluated expression type is int.
			geneExpression = ExprBinary.Op.EQUALS.make(null, null, evaluatedExpression, evaluationExpr);
			geneValue = new ExprGeneValue(geneExpression,ExprGeneType.EQUALITY);
			exprGene = new ExprGene(conf,geneValue,dataStructureInformation);
			
		} else {
			if (evaluationExpr.equals(nullExpr)) {
				// The evaluation was null
				geneExpression = ExprBinary.Op.EQUALS.make(null, null, evaluatedExpression, nullSig);
				geneValue = new ExprGeneValue(geneExpression,ExprGeneType.EQUALITY);
				exprGene = new ExprGene(conf,geneValue,dataStructureInformation);
			} else {
				if (evaluationExpr.equals(ExprConstant.EMPTYNESS)) {
					geneExpression = ExprUnary.Op.NO.make(null, evaluatedExpression);
					geneValue = new ExprGeneValue(geneExpression,ExprGeneType.EMPTYNESS);
					exprGene = new ExprGene(conf,geneValue,dataStructureInformation);
				} else {
					if (dataStructureInformation.typeUsedInRecursiveRelation(evaluatedExpression.type())) {
						// The evaluation type is used in some recursive relation
						geneExpression = ExprBinary.Op.NOT_EQUALS.make(null, null, evaluatedExpression, nullSig);
						geneValue = new ExprGeneValue(geneExpression,ExprGeneType.EQUALITY);
						exprGene = new ExprGene(conf,geneValue,dataStructureInformation);
					} else {
						geneExpression = ExprBinary.Op.EQUALS.make(null, null, evaluatedExpression, dataStructureInformation.getCorrespondingSignature((ExprVar)evaluationExpr));
						geneValue = new ExprGeneValue(geneExpression,ExprGeneType.EQUALITY);
						exprGene = new ExprGene(conf,geneValue,dataStructureInformation);
					}
				}
			}
		}
		return exprGene;
	}

	/**
	 * Get the correct expression from a evaluation
	 * @param example is the example in which the evaluation was performed
	 * @param evaluation is the evaluation performed
	 * @return the expression corresponding to the evaluation result
	 */
	private Expr evaluationToExpression(A4Solution example,A4TupleSet evaluation) {
		if (evaluation.iterator().hasNext()) {
			A4Tuple firstEval = evaluation.iterator().next();
			Expr expr = ExprConstant.TRUE;
			if (firstEval.type().toString().equals("{seq/Int}")||firstEval.type().toString().equals("{Int}")) {
				// The evaluation is of type int
				expr = ExprConstant.makeNUMBER(Integer.parseInt(firstEval.toString()));
			} else {
				for (ExprVar e : example.getAllAtoms()) {
					if (e.toString().equals(firstEval.toString())) {
						expr = e;
						break;
					}
				}
			}
			return expr;
		} else {
			return ExprConstant.EMPTYNESS;
		}
		
	}

	/**
	 * Learns the specification
	 * @throws InvalidConfigurationException
	 */
	public void learnSpec() throws InvalidConfigurationException {
		conf.setFitnessFunction(new DynAlloyPassingAssertionsCounter(runner));
		List<InvariantChromosome> initialChromosomes = getInitialChromosomes(); 
		conf.setPopulationSize( initialChromosomes.size() );
		
		Genotype population = Genotype.randomInitialGenotype(conf);
		population.getPopulation().setChromosomes(initialChromosomes);
		
		double current=0;
		int iterations = 30;
		int i=0;
		//evolve and end if reach max iterations or max value found (all assert pass)
		while ((i<iterations) && (current<runner.getNumberOfAssertions())){ 
			population.evolve();
			current=conf.getFitnessFunction().getFitnessValue(population.getFittestChromosome());
			System.out.println("Fittest Chromosome value: "+current) ;
			i++;
		};
		System.out.println("SPECIFICATION LEARNED");
		foundChromosome = (InvariantChromosome) population.getFittestChromosome();
	}
	
	/**
	 * Learns a more friendly specification from a set of propositions, equivalent to a given specification
	 * @throws InvalidConfigurationException
	 */
	public void learnSpecFromSpec() throws InvalidConfigurationException {
		
		conf.setFitnessFunction(new DynAlloyEquivalenceSpecCounter(runner,genes_num,empty_spec));
		List<InvariantChromosome> initialChromosomes = getInitialChromosomes(); 
		conf.setPopulationSize( parameters.getPopulationSize() );
		
		Genotype population = Genotype.randomInitialGenotype(conf);
		population.getPopulation().setChromosomes(initialChromosomes);
		InvariantChromosome bestChromosome=null;
		
		double current=0;
		//int iterations = 100;
		System.out.println("Max iterarations: "+parameters.getNumberOfGenerations());
		System.out.println("Amount of genes per Chromosome: "+initialChromosomes.get(0).getGenes().length);
		System.out.println("Initial population size: "+initialChromosomes.size());
		System.out.println("Total population size: "+conf.getPopulationSize());
		
		int i=0;
		double bestSolution = 0;
		//int minimumSolutionValue = ((DynAlloyEquivalenceSpecCounter)conf.getFitnessFunction()).minimumSolutionValue();
		//System.out.println("Minimum solution value "+minimumSolutionValue);
		System.out.println();
		// Evolve and end if reach max iterations or max value found (all assert pass)
		while (i < parameters.getNumberOfGenerations()) {
			/*population.evolve();
			current=conf.getFitnessFunction().getFitnessValue(population.getFittestChromosome());
			foundChromosome = (InvariantChromosome)population.getFittestChromosome();	
			i++;
			if (current>=minimumSolutionValue) {
				if (current>bestSolution) {
					bestSolution=current;
					bestChromosome=(InvariantChromosome)foundChromosome.clone();
					System.out.println("A best solution was found with value "+bestSolution+" in generation "+i);
					System.out.println(learnedSpec());
				} else {
					System.out.println("The solution is the same as before with value "+current+" in generation "+i);
				}
			} else {
				System.out.println("Fittest Chromosome value: "+current+" generation "+i) ;
			}*/
			System.out.println("GENERATION "+(i+1)+"/"+parameters.getNumberOfGenerations());
			population.evolve();
			current=conf.getFitnessFunction().getFitnessValue(population.getFittestChromosome());
			foundChromosome = (InvariantChromosome)population.getFittestChromosome();	
			i++;
			if (foundChromosome.getAmountOfCounterexamples().compareTo(new Double(0))==0){	
				if (current>bestSolution) {
					bestSolution=current;
					bestChromosome=(InvariantChromosome)foundChromosome.clone();
				} 
				if (ConfigurationProperties.getStopCriterion().equals("first")) {
					System.out.println();
					System.out.println("FIRST INVARIANT FOUND");
					break;
				}
			} else {
				System.out.println();
				System.out.println("BEST CHROMOSOME FITNESS: "+current) ;
				//foundChromosome.printGenes();
				System.out.println(learnedSpec());
				System.out.println();
			}
			System.out.println();
		};
		System.out.println("Done!");
		foundChromosome = bestChromosome;
	
	}
	
	/**
	 * Learns a specification from an empty set of propositions, equivalent to a given specification 
	 * @return
	 */
	public void learnSpecFromEmptySpec() throws InvalidConfigurationException {
		
		// Add the custom genetic operators 
		conf.getGeneticOperators().remove(1); // Delete mutation
		conf.getGeneticOperators().remove(0); // Delete crossover
		ExprGeneMutationOperator mutationOp = new ExprGeneMutationOperator(conf);
		mutationOp.setMutationProb(parameters.getMutationProbability());
		conf.getGeneticOperators().add(0, mutationOp);
		ChromosomeCrossoverOperator crossoverOp = new ChromosomeCrossoverOperator(conf);
		conf.getGeneticOperators().add(crossoverOp);
		
		conf.removeNaturalSelectors(false);
		conf.addNaturalSelector(new InvariantChromosomeNaturalSelector(conf), false);
		
		conf.getJGAPFactory().registerCloneHandler(new ExprGeneValueCloneHandler());
		conf.setFitnessFunction(new DynAlloyEquivalenceSpecCounter(runner,genes_num,empty_spec));
		List<InvariantChromosome> initialChromosomes = getInitialChromosomes(); 
		System.out.println("Amount of genes per Chromosome: "+initialChromosomes.get(0).getGenes().length);
		conf.setPopulationSize(parameters.getPopulationSize());
		System.out.println("Initial population size: "+initialChromosomes.size());
		System.out.println("Total population size: "+conf.getPopulationSize());
		Genotype population = Genotype.randomInitialGenotype(conf);
		population.getPopulation().setChromosomes(initialChromosomes);
		
		InvariantChromosome bestChromosome=null;
		
		double current=0;
		int i=0;
		double bestSolution = 0;
		System.out.println();
		// Evolve and end if reach max iterations or max value found (all assert pass)
		long itime = System.currentTimeMillis();
		while (i < parameters.getNumberOfGenerations()) {
			System.out.println("GENERATION "+(i+1)+"/"+parameters.getNumberOfGenerations());
			population.evolve();
			current=conf.getFitnessFunction().getFitnessValue(population.getFittestChromosome());
			foundChromosome = (InvariantChromosome)population.getFittestChromosome();	
			i++;
			if (foundChromosome.getAmountOfCounterexamples().compareTo(new Double(0))==0){	
				if (current>bestSolution) {
					bestSolution=current;
					bestChromosome=(InvariantChromosome)foundChromosome.clone();
				} 
				if (ConfigurationProperties.getStopCriterion().equals("first")) {
					System.out.println();
					System.out.println("FIRST INVARIANT FOUND");
					break;
				}
			} else {
				System.out.println();
				System.out.println("BEST CHROMOSOME FITNESS: "+current) ;
				foundChromosome.printGenes();
				System.out.println();
			}
			System.out.println();
		};
		int totalTime = (int)(System.currentTimeMillis()-itime)/1000;
		if (bestSolution==0) {
			System.out.println("SPECIFICATION NOT LEARNED");
		}
	}
	
	/**
	 * Get the learned specification.
	 * @return
	 */
	public String learnedSpec() {
		if (foundChromosome!=null) {
			Gene[] genes = foundChromosome.getGenes();
			int[] res = new int[foundChromosome.size()];
			for (int i=0; i< res.length; i++) {
				res[i] = ((IntegerGene) genes[i]).intValue();
			}
			String genesString = "";
			for (int i=0; i<res.length;i++) {
				if (res[i]==1) {
					genesString += getGenesDescription()[i]+" AND \n";
				} 
				if (res[i]==0) {
					genesString += "NOT "+ getGenesDescription()[i] +" AND \n";
				}
			}
			return genesString;
		}
		return "Invariant not learned";
	}
	
	/**
	 * Get the learned specification from an empty spec.
	 * @return
	 */
	public String learnedSpecFromEmptySpec() {
		Gene[] genes = foundChromosome.getGenes();
		String[] res = new String[foundChromosome.size()];
		String stringExpr="";
		for (int i=0; i < res.length; i++) {
			if (!((ExprGene)genes[i]).getValue().getExpression().equals(ExprConstant.TRUE)) {
				stringExpr += ((ExprGene)genes[i]).getInternalValue().toString();
				if (i < res.length-1) {
					stringExpr += "\n AND \n";
				}
			}
			res[i] = ((ExprGene)genes[i]).getInternalValue().toString();
		}
		return stringExpr;
	}
			
	//--- Rerport support
	public String[] getGenesDescription (){
		return runner.getRepOkElementsAsString();
	}

}
