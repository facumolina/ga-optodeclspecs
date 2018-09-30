package main;

import utils.DynAlloySpecLearnerParameters;

/**
 * Main class with the main methods. It takes an Alloy file containing a repOKOK pred which is a 
 * representation invariant of some data structure, and also contains a repOK pred which is empty 
 * and will be filled with a representation invariant equivalent to the repOKOK. 
 * @author fmolina
 */
public class SpecTranslator {
	
	public static void main(String[] args) {
		try {
			if (args.length!=1){
				System.out.println("Error: correct usage is java -jar alloy-learning.jar file.als");
			} else {
				String filePath = args[0];		
				ConfigurationProperties.loadFile("alearning.properties");
				processFile(filePath);
			}
		} catch (Exception e) {
			e.printStackTrace();
		}
	}

	/**
	 * Process the given file
	 */
	public static int processFile(String filePath) throws Exception {
		System.out.println("STARTING LEARNING PROCESS FROM FILE: "+filePath);
		DynAlloySpecLearnerParameters params = new DynAlloySpecLearnerParameters();
		DynAlloySpecLearner learner = new DynAlloySpecLearner(filePath,params);
		learner.learnSpecFromEmptySpec();
		return 1;
	}
	
	/**
	 * Process the given file with the given parameters
	 */
	public static int processFile(String filePath,DynAlloySpecLearnerParameters params) throws Exception {
		System.out.println("STARTING LEARNING PROCESS FROM FILE: "+filePath);
		DynAlloySpecLearner learner = new DynAlloySpecLearner(filePath,params);
		learner.learnSpecFromEmptySpec();
		return 1;
	}
	
}
