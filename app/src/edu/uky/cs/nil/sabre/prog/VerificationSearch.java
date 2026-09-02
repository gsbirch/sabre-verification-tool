package edu.uky.cs.nil.sabre.prog;

import java.lang.reflect.Field;
import java.util.ArrayList;
import java.util.List;

import edu.uky.cs.nil.sabre.Character;
import edu.uky.cs.nil.sabre.Number;
import edu.uky.cs.nil.sabre.Solution;
import edu.uky.cs.nil.sabre.SolutionGoal;
import edu.uky.cs.nil.sabre.comp.CompiledAction;
import edu.uky.cs.nil.sabre.comp.CompiledEvent;
import edu.uky.cs.nil.sabre.comp.CompiledProblem;
import edu.uky.cs.nil.sabre.etree.EventTree;
import edu.uky.cs.nil.sabre.logic.Value;
import edu.uky.cs.nil.sabre.prog.ProgressionCost;
import edu.uky.cs.nil.sabre.prog.ProgressionSearch;
import edu.uky.cs.nil.sabre.prog.ProgressionSpace;
import edu.uky.cs.nil.sabre.prog.SearchNode;
import edu.uky.cs.nil.sabre.ptree.ProgressionTree;
import edu.uky.cs.nil.sabre.ptree.ProgressionTreeSpace;
import edu.uky.cs.nil.sabre.search.Progress;
import edu.uky.cs.nil.sabre.util.ImmutableSet;
import edu.uky.cs.nil.sabre.util.Worker.Status;

public class VerificationSearch extends ProgressionSearch {

	public <N> VerificationSearch(CompiledProblem problem, ProgressionCost cost, ProgressionCost heuristic,
			EventTree<CompiledAction> actions, ProgressionSpace<N> space, long searchLimit, long spaceLimit,
			long timeLimit, int authorTemporalLimit, int characterTemporalLimit, int epistemicLimit,
			boolean explanationPruning) {
		super(problem, cost, heuristic, actions, space, searchLimit, spaceLimit, timeLimit, authorTemporalLimit,
				characterTemporalLimit, epistemicLimit, explanationPruning);
		
	}

	// additional parameters for verification
	private SearchNode<?> explainNode;
	
	// helper function for reflections to access the root
	private SearchNode<?> reflectionRoot() {
		Field field;
		try {
			field = ProgressionSearch.class.getDeclaredField("root");
			field.setAccessible(true);
			
			SearchNode<?> value = (SearchNode<?>) field.get(this);
			return value;
		} catch (Exception e) {
			e.printStackTrace();
			return null;
		}
	}
	
	// This function sets the explanation goal for our search
	// It starts at the root and applies each action, then changes
	// to the branch for the desired consenting character
	// The search will then try to find an explanation for the generated node
	public void SetExplanationGoal(List<CompiledAction> actionList, Character character) {
		// go down the list of actions to find our new node
		explainNode = reflectionRoot();
		
		for (CompiledAction ca : actionList) {
			explainNode = explainNode.getChild(ca);
		}
		// swap to the branch for the consenting character
		explainNode = explainNode.getBranch(character);
		
		// change the starting node to our new node to be explained
		queue.clear();
		push(explainNode);
	}
	
	// This is honestly just a sneaky way for me to test author utility
	public Number authorUtility(List<CompiledAction> actionList) {
		SearchNode<?> utilNode = reflectionRoot();
		for (CompiledAction ca : actionList) {
			utilNode = utilNode.getChild(ca);
		}
		return (Number) utilNode.getUtility(null);
	}
	
	private Solution<CompiledAction> findExplanation(ProgressionTree tree, long startID, long goalID, Character parentChar, int epiDepth) {
		Character consenting = tree.getCharacter(startID);
		
		Solution<CompiledAction> explanation = new SolutionGoal<>(consenting, tree.getGoal(startID));
		
		long rootID = tree.getRoot(startID);
		long stopID = tree.getBefore(goalID);
		long beforeID = -1;
		
		// We add this to our seen characters to not infinitely recurse
		//ImmutableSet<Character> checkChars = seenCharacters.add(consenting);
		
		long nodeID = startID;
		
		// We stop searching when:
		// 1: we reach the node before the one we're trying to explain (the explain node must be part of the explanation)
		// 2: a node loops back on itself (i think this is a root)
		// 3: we reach the root of a search
		List<CompiledAction> seenActions = new ArrayList<>();
		while (nodeID != stopID && nodeID != beforeID && nodeID != rootID) {
			
			// Skip any triggers along the way
			CompiledAction compAct = tree.getAction(nodeID);
			if (tree.getAction(nodeID) != null && tree.getEvent(nodeID) instanceof CompiledAction) {
				// Add the action to our explanation
				explanation = explanation.prepend(tree.getAction(nodeID));
				seenActions.add(compAct);
				
				// We need to skip the explain nodes action
				// a character does not care about the explanations for others
				// after achieving their goal
				
				if (explainNode.getAction() != compAct) {
					// Explain the action for any other consenting characters
					ImmutableSet<Character> consenters = tree.getAction(nodeID).consenting;
					for (Character c : consenters) {
						// we find a new character that we must explain
						if (c != parentChar && nodeID != goalID) {
							// our goal is to explain the action we're currently looking at
							long branchGoal = tree.getBranch(nodeID, c);
							
							// we need to go down to that goals explanation
							long branch = tree.getExplanation(branchGoal, c);
							// branch goal is intended to represent the most recent action
							while (!(tree.getEvent(branchGoal) instanceof CompiledAction)) {
								branchGoal = tree.getBefore(branchGoal);
							}
							
							// This should always return something because explainNode will always be fully explained
							if (epiDepth >= epistemicLimit) {
								System.out.println("This is a problem");
							}
							
							Solution<CompiledAction> charExplain = findExplanation(tree, branch, branchGoal, c, epiDepth + 1);
							//if (charExplain == null) return null; 
							explanation = explanation.setExplanation(charExplain);
						}
					}
				}
			}
			
			beforeID = nodeID;
			nodeID = tree.getBefore(nodeID);
		}
		
		return explanation;
	}
	
	// helper function to get the ProgressionTree
	// with reflections since it's private
	private ProgressionTree reflectionTree(ProgressionTreeSpace space) {
		Field field;
		try {
			field = ProgressionTreeSpace.class.getDeclaredField("tree");
			field.setAccessible(true);
			
			ProgressionTree value = (ProgressionTree) field.get(space);
			return value;
		} catch (Exception e) {
			e.printStackTrace();
			return null;
		}
	}
	
	private void reflectionIncrementVisited() {
		Field field;
		try {
			field = ProgressionSearch.class.getDeclaredField("visited");
			field.setAccessible(true);
			
			long value = (long) field.get(this);
			field.set(this, value + 1);
		} catch (Exception e) {
			e.printStackTrace();
		}
	}
	
	@Override
	protected void run(Progress<CompiledAction> progress, Status status) {
		setStatus(status, progress);
		while(!progress.isDone()) {
			// Grabbing stuff from our node to explain
			ProgressionTreeSpace explainSpace = (ProgressionTreeSpace) explainNode.getSpace();
			ProgressionTree tree = reflectionTree(explainSpace);
			Character consentingChar = explainNode.getCharacter();
			long explainNodeID = (long) tree.getExplanation((long) explainNode.getNode(), consentingChar);
			
			// We generate an explanation when the tree has been populated with one
			// For some reason, this isn't always the same as when explainNode.isExplained() is true
			if (explainNodeID != -1) {
				
				// This function builds the solution from the given explanation node
				long goalID = (long) explainNode.getNode();
				
				// Goal ID is intended to represent the most recent action
				while (!(tree.getEvent(goalID) instanceof CompiledAction)) {
					goalID = tree.getBefore(goalID);
				}
				
				Solution<CompiledAction> explanation = findExplanation(tree, explainNodeID, goalID, consentingChar, 0);
				if (explanation != null) {
					// We set the solution to halt this search
					progress.setSolution(explanation, getGoal());
				}
					
			}
			else if(!queue.isEmpty()) {
				SearchNode<?> node = queue.poll();
				if(!prune(node) && visit(node))
					reflectionIncrementVisited();
				updateStatus(status, progress);
			}
			else
				break;
		}
		updateStatus(status, progress);
	}
}
