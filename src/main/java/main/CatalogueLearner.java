package main;

import utils.DynAlloySpecLearnerParameters;

public class CatalogueLearner {
	
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
		learner.learnSpecFromSpec();
		return 1;
	}
	
}