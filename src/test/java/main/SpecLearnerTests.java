package main;

import static org.junit.Assert.*;

import org.junit.Test;

public class SpecLearnerTests {

	@Test
	public void test() throws Exception {
		SpecLearner learner = new SpecLearner(11, 4);
		learner.learnSpec();
		boolean[] result = learner.learnedSpec();
		assertTrue(result != null);
		for (int i=0; i<result.length;i++) {
			System.out.println(result[i]);
		}
	}

}
