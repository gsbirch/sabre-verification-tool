package edu.uky.cs.nil.sabre.prog;

import edu.uky.cs.nil.sabre.Number;
import edu.uky.cs.nil.sabre.Problem;
import edu.uky.cs.nil.sabre.Settings;
import edu.uky.cs.nil.sabre.comp.CompiledAction;
import edu.uky.cs.nil.sabre.comp.CompiledProblem;
import edu.uky.cs.nil.sabre.etree.EventTree;
import edu.uky.cs.nil.sabre.logic.Unknown;
import edu.uky.cs.nil.sabre.logic.Value;
import edu.uky.cs.nil.sabre.prog.ExplanationFirstSearch;
import edu.uky.cs.nil.sabre.prog.GoalFirstSearch;
import edu.uky.cs.nil.sabre.prog.ProgressionCost;
import edu.uky.cs.nil.sabre.prog.ProgressionPlanner;
import edu.uky.cs.nil.sabre.prog.ProgressionSearch;
import edu.uky.cs.nil.sabre.prog.ProgressionSpace;
import edu.uky.cs.nil.sabre.ptree.ProgressionTreeSpace;
import edu.uky.cs.nil.sabre.util.Worker.Status;

// This class mimics the ProgressionPlanner class
// But it hijacks the getSearch method to instead generate a VerificationSearch object
public class VerificationPlanner extends ProgressionPlanner {
	
	/** Serial version ID */
	private static final long serialVersionUID = Settings.VERSION_UID;
	
	@Override
	public ProgressionSearch getSearch(Problem problem, Status status) {                           
		CompiledProblem compiled = problem instanceof CompiledProblem ? (CompiledProblem) problem : compile(problem, status);
		EventTree<CompiledAction> actions = compiled.actions.buildTree(status);
		compiled.triggers.buildTree(status);
		ProgressionSpace<?> space = new ProgressionTreeSpace(compiled, status);
		ProgressionCost cost = getCost().getCost(compiled, status);
		ProgressionCost heuristic = getHeuristic().getCost(compiled, status);
		ProgressionSearch search;
		search = new VerificationSearch(
			compiled,
			cost,
			heuristic,
			actions,
			space,
			getSearchLimit(),
			getSpaceLimit(),
			getTimeLimit(),
			getAuthorTemporalLimit(),
			getCharacterTemporalLimit(),
			getEpistemicLimit(),
			getExplanationPruning()
		);		
		search.setStart(compiled.start);
		Value goal = compiled.utility.evaluate(compiled.start);
		if(goal.equals(Unknown.UNKNOWN))
			goal = Number.NEGATIVE_INFINITY;
		search.setGoal((Number) goal);
		return search;
	}
}
