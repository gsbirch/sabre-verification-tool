package edu.uky.cs.nil.sabre;

import java.io.File;
import java.lang.reflect.Array;
import java.util.ArrayList;
import java.util.Collections;
import java.util.Dictionary;
import java.util.HashMap;
import java.util.List;
import java.util.Scanner;

import edu.uky.cs.nil.sabre.comp.CompiledAction;
import edu.uky.cs.nil.sabre.comp.CompiledProblem;
import edu.uky.cs.nil.sabre.etree.EventSet;
import edu.uky.cs.nil.sabre.graph.StateGraph;
import edu.uky.cs.nil.sabre.graph.StateNode;
import edu.uky.cs.nil.sabre.io.Parser;
import edu.uky.cs.nil.sabre.logic.Expression;
import edu.uky.cs.nil.sabre.logic.False;
import edu.uky.cs.nil.sabre.logic.True;
import edu.uky.cs.nil.sabre.prog.GraphHeuristic;
import edu.uky.cs.nil.sabre.prog.ProgressionCostFactory;
import edu.uky.cs.nil.sabre.prog.ProgressionPlanner;
import edu.uky.cs.nil.sabre.prog.ProgressionPlanner.Method;
import edu.uky.cs.nil.sabre.prog.ProgressionSearch;
import edu.uky.cs.nil.sabre.prog.ReachabilityHeuristic;
import edu.uky.cs.nil.sabre.prog.RelaxedPlanHeuristic;
import edu.uky.cs.nil.sabre.prog.SearchNode;
import edu.uky.cs.nil.sabre.prog.WeightedCost;
import edu.uky.cs.nil.sabre.search.Planner;
import edu.uky.cs.nil.sabre.search.Result;
import edu.uky.cs.nil.sabre.search.Search;
import edu.uky.cs.nil.sabre.util.CommandLineArguments;
import edu.uky.cs.nil.sabre.util.Worker;

/**
 * Configures a {@link Session session} according to command line arguments,
 * runs a {@link Search search}, and prints the {@link Result result} to
 * standard output.
 * 
 * @author Stephen G. Ware
 */
public class Main {

	/** The command line key for the usage message */
	public static final String HELP_KEY = "-help";
	
	/** The command line key for verbose output */
	public static final String VERBOSE_KEY = "-v";
	
	/** The command line key for the problem file URL */
	public static final String PROBLEM_KEY = "-p";
	
	/** The command line key for the goal utility */
	public static final String GOAL_KEY = "-g";
	
	/** The command line key for the {@link Planner#getSearchLimit() search limit} */
	public static final String SEARCH_LIMIT_KEY = "-vl";
	
	/** The command line key for the {@link Planner#getSpaceLimit() space limit} */
	public static final String SPACE_LIMIT_KEY = "-gl";
	
	/** The command line key for the {@link Planner#getTimeLimit() time limit} */
	public static final String TIME_LIMIT_KEY = "-tl";
	
	/**
	 * The command line key for the {@link Planner#getAuthorTemporalLimit()
	 * author temporal limit}
	 */
	public static final String AUTHOR_TEMPORAL_LIMIT_KEY = "-atl";
	
	/**
	 * The command line key for the {@link Planner#getCharacterTemporalLimit()
	 * character temporal limit}
	 */
	public static final String CHARACTER_TEMPORAL_LIMIT_KEY = "-ctl";
	
	/**
	 * The command line key for the {@link Planner#getEpistemicLimit() epistemic
	 * limit}
	 */
	public static final String EPISTEMIC_LIMIT_KEY = "-el";
	
	/**
	 * The command line key for the {@link ProgressionPlanner#getMethod() search
	 * method}
	 */
	public static final String METHOD_KEY = "-m";
	
	/**
	 * The command line key for the {@link ProgressionPlanner#getCost() cost
	 * function}
	 */
	public static final String COST_KEY = "-c";
	
	/**
	 * The command line key for the {@link WeightedCost weight} to apply to the
	 * cost function
	 */
	public static final String COST_WEIGHT_KEY = "-cw";
	
	/**
	 * The command line key for the {@link ProgressionPlanner#getHeuristic()
	 * heuristic function}
	 */
	public static final String HEURISTIC_KEY = "-h";
	
	/**
	 * The command line key for the {@link WeightedCost weight} to apply to the
	 * heuristic function
	 */
	public static final String HEURISTIC_WEIGHT_KEY = "-hw";
	
	/**
	 * The command line key for {@link
	 * ProgressionPlanner#getExplanationPruning() explanation pruning}
	 */
	public static final String EXPLANATION_PRUNING_KEY = "-ep";
	
	
	/**
	 * SABRE EXPLANATION TOOL
	 * The command line key for the plan to attempt to explain
	 */
	public static final String PLAN_KEY = "-pl";
	
	/**
	 * The abbreviation for {@link ProgressionPlanner.Method#BEST_FIRST
	 * best-first search}
	 */
	public static final String BEST_FIRST_OPTION = "bf";
	
	/**
	 * The abbreviation for {@link ProgressionPlanner.Method#EXPLANATION_FIRST
	 * explanation-first search}
	 */
	public static final String EXPLANATION_FIRST_OPTION = "ef";
	
	/**
	 * The abbreviation for {@link ProgressionPlanner.Method#GOAL_FIRST
	 * goal-first search}
	 */
	public static final String GOAL_FIRST_OPTION = "gf";
	
	/**
	 * The abbreviation for {@link
	 * edu.uky.cs.nil.sabre.prog.ProgressionCost#ZERO the zero cost function}
	 */
	public static final String ZERO_COST_OPTION = "0";
	
	/**
	 * The abbreviation for {@link
	 * edu.uky.cs.nil.sabre.prog.ProgressionCost#PLAN_SIZE the plan size
	 * function}
	 */
	public static final String PLAN_SIZE_COST_OPTION = "n";
	
	/**
	 * The abbreviation for {@link
	 * edu.uky.cs.nil.sabre.prog.ProgressionCost#EXPLANATION the explanation
	 * depth function}
	 */
	public static final String EXPLANATION_COST_OPTION = "x";
	
	/**
	 * The abbreviation for {@link
	 * edu.uky.cs.nil.sabre.prog.ProgressionCost#TEMPORAL the temporal depth
	 * function} */
	public static final String TEMPORAL_COST_OPTION = "t";
	
	/**
	 * The abbreviation for {@link
	 * edu.uky.cs.nil.sabre.prog.ProgressionCost#ZERO the zero heuristic}
	 */
	public static final String ZERO_HEURISTIC_OPTION = "0";
	
	/**
	 * The abbreviation for {@link ReachabilityHeuristic the reachability
	 * heuristic}
	 */
	public static final String REACHABILITY_HEURISTIC_OPTION = "r";
	
	/**
	 * The abbreviation for {@link GraphHeuristic.MaxGraphHeuristic the max
	 * graph heuristic}
	 */
	public static final String MAX_HEURISTIC_OPTION = "hmax";
	
	/**
	 * The abbreviation for {@link GraphHeuristic.SumGraphHeuristic the sum
	 * graph heuristic}
	 */
	public static final String SUM_HEURISTIC_OPTION = "h+";
	
	/**
	 * The abbreviation for {@link RelaxedPlanHeuristic the relaxed plan
	 * heuristic}
	 */
	public static final String RELAXED_PLAN_HEURISTIC_OPTION = "rp";
	
	private static final String pad(String string) {
		return String.format("%-13s", string);
	}
	
	/**
	 * A string explaining the command line arguments that can be passed to
	 * {@link #main(String[]) the main method}
	 */
	public static final String USAGE =
		Settings.CREDITS + "\n" +
		pad(HELP_KEY) +									"print this message and halt\n" +
		pad(VERBOSE_KEY) +								"verbose output gives details of the search and results\n" +
		pad(PROBLEM_KEY + " PATH") +					"problem file to parse\n" +
		pad(PLAN_KEY + " PATH") +						"plan file to parse\n" +
		pad(GOAL_KEY + " NUMBER") +						"utility a solution much reach (default round up or +1)\n" +
		pad(METHOD_KEY + " OPTION") +					"heuristic search method; options include:\n" +
		pad("   " + BEST_FIRST_OPTION) +				"A* best-first (default)\n" +
		pad("   " + EXPLANATION_FIRST_OPTION) +			"explanation-first: explain actions before achieving the goal\n" +
		pad("   " + GOAL_FIRST_OPTION) +				"goal-first: achieve the goal before explaining actions\n" +
		pad(COST_KEY + " OPTION") +						"how plan cost is measured; options include:\n" +
		pad("   " + ZERO_COST_OPTION) +					"always zero\n" +
		pad("   " + PLAN_SIZE_COST_OPTION) +			"number of actions in the plan\n" +
		pad("   " + EXPLANATION_COST_OPTION) +			"number of actions in the explanation\n" +
		pad("   " + TEMPORAL_COST_OPTION) +				"number of actions before the plan and in the plan (default)\n" +
		pad(COST_WEIGHT_KEY + " NUMBER") +				"a weight to multiply the cost by\n" +
		pad(HEURISTIC_KEY + " OPTION") +				"how distance to the goal is estimated; options include:\n" +
		pad("   " + ZERO_HEURISTIC_OPTION) +			"always zero\n" +
		pad("   " + REACHABILITY_HEURISTIC_OPTION) +	"prevent some searches with impossible goals\n" +
		pad("   " + MAX_HEURISTIC_OPTION) +				"estimate cost when a conjunction costs the max of its arguments\n" +
		pad("   " + SUM_HEURISTIC_OPTION) +				"estimate cost when a conjunction costs the sum of its arguments\n" +
		pad("   " + RELAXED_PLAN_HEURISTIC_OPTION) +	"build a relaxed plan to approximate the solution (default)\n" +
		pad(HEURISTIC_WEIGHT_KEY + " NUMBER") +			"a weight to multiply the heuristic by\n" +
		pad(EXPLANATION_PRUNING_KEY + " {y|n}") +		"once one explanation has been found for an action, do not search for more (default y)\n" +
		pad(SEARCH_LIMIT_KEY + " NUMBER") +				"max nodes the search can visit; " + Planner.UNLIMITED_NODES + " for unlimited (default " + Planner.UNLIMITED_NODES + ")\n" +
		pad(SPACE_LIMIT_KEY + " NUMBER") +				"max nodes the search can generate; " + Planner.UNLIMITED_NODES + " for unlimited (default " + Planner.UNLIMITED_NODES + ")\n" +
		pad(TIME_LIMIT_KEY + " NUMBER") +				"max milliseconds the search can run; " + Planner.UNLIMITED_TIME + " for unlimited (default " + Planner.UNLIMITED_TIME + ")\n" +
		pad(AUTHOR_TEMPORAL_LIMIT_KEY + " NUMBER") +	"max actions in a plan; " + Planner.UNLIMITED_DEPTH + " for unlimited (default " + Planner.UNLIMITED_DEPTH + ")\n" +
		pad(CHARACTER_TEMPORAL_LIMIT_KEY + " NUMBER") +	"max actions in a character's explanation for an action; " + Planner.UNLIMITED_DEPTH + " for unlimited (default " + Planner.UNLIMITED_DEPTH + ")\n" +
		pad(EPISTEMIC_LIMIT_KEY + " NUMBER") +			"max depth to explore theory of mind; " + Planner.UNLIMITED_DEPTH + " for unlimited (default " + Planner.UNLIMITED_DEPTH + ")";
	
	/**
	 * A functional interface for changing a setting in a {@link Session
	 * session}.
	 * 
	 * @param <T> the type of the value that will be set
	 * @author Stephen G. Ware
	 */
	@FunctionalInterface
	private interface Setter<T> {
		
		/**
		 * Calls the appropriate setter function for the given session with the
		 * given value.
		 * 
		 * @param session the session where the setting will be set
		 * @param value the value to set
		 * @throws Exception if an exception is thrown by the session while
		 * setting the value
		 */
		public void set(Session session, T value) throws Exception;
	}
	
	/**
	 * Holds a list of named options that are the possible values that can be
	 * passed to a setter function in a {@link Session session}.
	 * 
	 * @param <T> the type of value that will be set
	 * @author Stephen G. Ware
	 */
	private static final class OptionSetter<T> {
		
		/** The command line argument key whose options this setter defines */
		public final String key;
		
		/**
		 * The list of names for each option; the object is in the corresponding
		 * index in {@link #values}
		 */
		public final String[] codes;
		
		/**
		 * The list of values; the name is in the corresponding index in {@link
		 * #codes}
		 */
		public final T[] values;
		
		/**
		 * A function that calls the appropriate setter function in the session
		 */
		private final Setter<T> setter;
		
		/**
		 * Constructs a new option setter.
		 * 
		 * @param key the command line argument key whose options this setter
		 * defines
		 * @param type the type of value that will be set
		 * @param setter a function that calls the appropriate setter function
		 * in a session
		 * @param options an alternating list of names and values; the first and
		 * every odd numbered index should be a string; the second and every
		 * even numbered index should be a value
		 */
		@SuppressWarnings("unchecked")
		public OptionSetter(String key, Class<T> type, Setter<T> setter, Object...options) {
			this.key = key;
			this.setter = setter;
			this.codes = new String[options.length / 2];
			this.values = (T[]) Array.newInstance(type, options.length / 2);
			for(int i=0; i<options.length; i+=2) {
				this.codes[i / 2] = (String) options[i];
				this.values[i / 2] = type.cast(options[i + 1]);
			}
		}
		
		/**
		 * Parses the name of the option and passes the corresponding value to
		 * the {@link #setter setter}.
		 * 
		 * @param session the session where the setter function will be called
		 * @param code the name of an option
		 * @throws Exception if an exception is thrown by the session while
		 * setting the value
		 */
		public void set(Session session, String code) throws Exception {
			for(int i=0; i<codes.length; i++) {
				if(codes[i].equalsIgnoreCase(code)) {
					setter.set(session, values[i]);
					return;
				}
			}
			throw Exceptions.failedToParseCommandLineArgument(key, code);
		}
	}
	
	/**
	 * The options for {@link ProgressionPlanner#getMethod() a heuristic
	 * progression tree planner's search method}
	 */
	private static final OptionSetter<Method> METHOD_OPTIONS = new OptionSetter<>(
		METHOD_KEY, Method.class,
		(s, v) -> s.setMethod(v),
		BEST_FIRST_OPTION, Method.BEST_FIRST,
		EXPLANATION_FIRST_OPTION, Method.EXPLANATION_FIRST,
		GOAL_FIRST_OPTION, Method.GOAL_FIRST
	);
	
	/**
	 * The options for {@link ProgressionPlanner#getCost() a heuristic
	 * progression tree planner's cost function}
	 */
	private static final OptionSetter<ProgressionCostFactory> COST_OPTIONS = new OptionSetter<>(
		COST_KEY, ProgressionCostFactory.class,
		(s, v) -> s.setCost(v),
		TEMPORAL_COST_OPTION, ProgressionCostFactory.TEMPORAL,
		EXPLANATION_COST_OPTION, ProgressionCostFactory.EXPLANATION,
		PLAN_SIZE_COST_OPTION, ProgressionCostFactory.PLAN_SIZE,
		ZERO_COST_OPTION, ProgressionCostFactory.ZERO
	);
	
	/**
	 * The options for {@link HeuristicProgressionTreePlanner#getHeuristic() a
	 * heuristic progression tree planner's heuristic function}
	 */
	private static final OptionSetter<ProgressionCostFactory> HEURISTIC_OPTIONS = new OptionSetter<>(
		HEURISTIC_KEY, ProgressionCostFactory.class,
		(s, v) -> s.setHeuristic(v),
		RELAXED_PLAN_HEURISTIC_OPTION, RelaxedPlanHeuristic.FACTORY,
		SUM_HEURISTIC_OPTION, GraphHeuristic.SUM,
		MAX_HEURISTIC_OPTION, GraphHeuristic.MAX,
		REACHABILITY_HEURISTIC_OPTION, ReachabilityHeuristic.FACTORY,
		ZERO_COST_OPTION, ProgressionCostFactory.ZERO
	);
	
	/**
	 * Configures a {@link Session session} according to command line arguments,
	 * runs a {@link Search search}, and prints the {@link Result result} to
	 * standard output.
	 * 
	 * @param args the command line arguments passed to the program
	 */
	public static void main(String[] args) {
		try {
			// Print help.
			CommandLineArguments arguments = new CommandLineArguments(args);
			if(args.length == 0 || arguments.contains(HELP_KEY)) {
				System.out.println(USAGE);
				return;
			}
			// Configure session according to command line arguments.
			boolean verbose = arguments.contains(VERBOSE_KEY);
			Session fakeSession = new Session();
			configure(fakeSession, arguments, false);
			if(verbose)
				System.out.println(Settings.CREDITS);
			
			
			// read in the actions from the file
			arguments.require(PLAN_KEY);
			File actionsFile = arguments.getFile(PLAN_KEY);
			arguments.checkUnused();
			Scanner scanner = new Scanner(actionsFile);
			ArrayList<CompiledAction> scannedActions = new ArrayList<>();
			while (scanner.hasNextLine()) {
			    String line = scanner.nextLine();
			    EventSet<CompiledAction> as = ((CompiledProblem) generatedCompiledProblem).actions;
			    for (CompiledAction a : as) {
			    	if (a.toString().equals(line)) {
			    		scannedActions.add(a);
			    	}
			    }
			}
			scanner.close();
			
			
			
			ArrayList<CompiledAction> actionsToApply = new ArrayList<>();
			ArrayList<ArrayList<Solution<?>>> explanations = new ArrayList<>();
			
			boolean authorGoalAchieved = false;
	
			// We'll now generate an explanation for each action
			for (CompiledAction ca : scannedActions) {
				explanations.add(new ArrayList<>());
				// We build up the partial plan that we'll start with
				actionsToApply.add(ca);
				
				// We need an explanation for every consenting character
				for (Character consenter : ca.consenting) {
					// we make a node for every action, then one more to get the branch
					searchBuffer = actionsToApply.size() + 1;
					temporalBuffer = actionsToApply.size();
					epistemicBuffer = 0;
					
					Session session = new Session();
					configure(session, arguments, verbose);
					
					ProgressionSearch progSearch = (ProgressionSearch) session.getSearch();
					
					// stuff for creating a search starting at the action we want to explain
					// doesn't really work
//					CompiledProblem comProb = (CompiledProblem) generatedCompiledProblem;
//					StateGraph graph = new StateGraph(generatedCompiledProblem, comProb.start);
//					StateNode current = graph.root;
//					for (CompiledAction ta : actionsToApply) {
//						current = current.getAfter(ta).getAfterTriggers();
//					}
//					current = current.getEpistemicChild(consenter).parent;
//					session.setState(current);
					
					// Set up our search with the actions and the consenter we're using
					progSearch.SetExplanationGoal(actionsToApply, consenter);
					
					// Get the solution, and print it if verbose
					Result<?> result;
					if(verbose)
						result = Worker.get(s -> session.getResult(), session.getStatus());
					else
						result = session.getResult();
					
					// Add the solution to our list of explanations
					explanations.get(explanations.size() - 1).add(result.solution);
					if (scannedActions.size() == actionsToApply.size()) {
						Number authorUtil = ((ProgressionSearch) session.getSearch()).authorUtility(actionsToApply);
						if (authorUtil.compareTo(session.goal) >= 0)
							authorGoalAchieved = true;
					}
				}
			}
			
			// Create the solution that we'll eventually build up
			Expression authorGoal = generatedCompiledProblem.utility;
			Expression util = authorGoalAchieved ? authorGoal : True.TRUE;
			Solution<CompiledAction> bigSolution = new SolutionGoal<>(null, util);
			
			// Go backwards, and add each action and its explanations
			for (int i = scannedActions.size() - 1; i >= 0; i--) {
				bigSolution = bigSolution.prepend(scannedActions.get(i));
				for (Solution<?> explanation : explanations.get(i)) {
					if (explanation == null) continue;
					bigSolution = bigSolution.setExplanation((Solution<CompiledAction>) explanation);
				}
			}
			// Print out the solutions
			System.out.println(bigSolution);
		}
		catch(Throwable t) {
			if(t instanceof RuntimeException && t.getCause() != null)
				t = t.getCause();
			System.err.println("Error: " + t.getMessage());
		}
	}
	
	// we only have one problem class that we continue to use for all sessions
	static Problem generatedProblem = null;
	static Problem generatedCompiledProblem = null;
	
	static int temporalBuffer = 0;
	static int epistemicBuffer = 0;
	static int searchBuffer = 0;
	
	/**
	 * Configures the given {@link Session session} according to the {@link
	 * CommandLineArguments command line arguments}.
	 * 
	 * @param session the session object whose settings will be configured
	 * @param arguments the command line arguments describing how to configure
	 * the session
	 * @param verbose if true, details of the problem and search will be printed
	 * to standard output while the session is configured
	 * @throws Exception if any required command line arguments are missing or
	 * formatted incorrectly, or if the session throws an exception while it is
	 * being configured (for example, if the parser fails to parse the problem)
	 */
	public static void configure(Session session, CommandLineArguments arguments, boolean verbose) throws Exception {
		if (generatedProblem == null) {
			// Problem
			arguments.require(PROBLEM_KEY);
			session.setProblem(arguments.getFile(PROBLEM_KEY));
			if(verbose)
				print("Problem", session.getProblem());
			// Compiled Problem
			if(verbose)
				Worker.run(s -> session.getCompiledProblem(), session.getStatus());
			else
				session.getCompiledProblem();
			if(verbose)
				print("Compiled Problem", session.getCompiledProblem());
			
			generatedProblem = session.getProblem();
			generatedCompiledProblem = session.getCompiledProblem();
		}
		else {
			arguments.require(PROBLEM_KEY);
			session.setProblem(generatedProblem);
			session.setCompiledProblem(generatedCompiledProblem);
		}
		
		// Search
		session.setGoal(arguments.getDouble(GOAL_KEY, session.getGoal().value));
		
		// A buffer is added for search/space since we expand nodes to get the node we want to explain
		long searchLimit = arguments.getLong(SEARCH_LIMIT_KEY, Planner.UNLIMITED_NODES);
		if (searchLimit != Planner.UNLIMITED_NODES) searchLimit += searchBuffer;
		session.setSearchLimit(searchLimit);
		long spaceLimit = arguments.getLong(SPACE_LIMIT_KEY, Planner.UNLIMITED_NODES);
		if (spaceLimit != Planner.UNLIMITED_NODES) spaceLimit += searchBuffer;
		session.setSpaceLimit(spaceLimit);
		
		session.setTimeLimit(arguments.getLong(TIME_LIMIT_KEY, Planner.UNLIMITED_TIME));
		session.setAuthorTemporalLimit(arguments.getInt(AUTHOR_TEMPORAL_LIMIT_KEY, Planner.UNLIMITED_DEPTH));
		
		// A buffer is added since we've already taken some actions before the node to be explained
		int charTempLimit = arguments.getInt(CHARACTER_TEMPORAL_LIMIT_KEY, Planner.UNLIMITED_DEPTH);
		if (charTempLimit != Planner.UNLIMITED_DEPTH) charTempLimit += temporalBuffer;
		session.setCharacterTemporalLimit(charTempLimit);
		
		// I don't believe this buffer is necessary but just in case
		int epistemicLimit = arguments.getInt(EPISTEMIC_LIMIT_KEY, Planner.UNLIMITED_DEPTH);
		if (epistemicLimit != Planner.UNLIMITED_DEPTH) epistemicLimit += epistemicBuffer;
		session.setEpistemicLimit(epistemicLimit);
		
		if(session.getPlanner() instanceof ProgressionPlanner) {
			METHOD_OPTIONS.set(session, arguments.getOption(METHOD_KEY, METHOD_OPTIONS.codes));
			COST_OPTIONS.set(session, arguments.getOption(COST_KEY, COST_OPTIONS.codes));
			HEURISTIC_OPTIONS.set(session, arguments.getOption(HEURISTIC_KEY, HEURISTIC_OPTIONS.codes));
			if(arguments.contains(COST_WEIGHT_KEY))
				session.setCost(new WeightedCost.Factory(session.getCost(), arguments.getDouble(COST_WEIGHT_KEY, 1)));
			if(arguments.contains(HEURISTIC_WEIGHT_KEY))
				session.setCost(new WeightedCost.Factory(session.getHeuristic(), arguments.getDouble(HEURISTIC_WEIGHT_KEY, 1)));
			session.setExplanationPruning(arguments.getBoolean(EXPLANATION_PRUNING_KEY, true));
		}
		
		if(verbose)
			Worker.run(s -> session.getSearch(), session.getStatus());
		else
			session.getSearch();
		if(verbose)
			System.out.println(session.getPrinter().toString(session.getSearch()));
	}
	
	/**
	 * Prints summary statistics of a {@link Problem problem} to standard
	 * output if running in verbose mode.
	 * 
	 * @param key the type of problem
	 * @param problem the problem
	 */
	private static final void print(String key, Problem problem) {
		System.out.println(key + ": " + problem.name);
		System.out.println("  characters: " + problem.universe.characters.size());
		System.out.println("  entities:   " + problem.universe.entities.size());
		System.out.println("  fluents:    " + problem.fluents.size());
		System.out.println("  actions:    " + problem.actions.size());
		System.out.println("  triggers:   " + problem.triggers.size());
	}
	
	private Main() {}
}