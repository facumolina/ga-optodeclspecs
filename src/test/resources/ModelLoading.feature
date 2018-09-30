Feature: Basic model loading

Scenario: Loading an Alloy model and checking repOK existence
	Given that the user provides a file called filename
	When I open the file 
	Then the system should check whether the file contains a valid Alloy model
	And the system should check that the model contains a repOK predicate.
	
Scenario: Checking number of assertions
	Given that the user provides a file called filename
	And the file contains a valid Alloy model with 5 assertions 
	When I load the file 
	Then the system should inform that the number of assertions is 5.

Scenario: Launching learning process
	Given that the user provides a file called filename
	And the file contains a valid Alloy model with 5 assertions 
	And I load the file
	When I start the learning process 
	Then the system should create an initial population of length-5 chromosomes
	