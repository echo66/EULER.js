/**
  * Author: Guido J.M. Naudts Bouwel
  */
package com.ptb.sw.reasoner.bwr;

import com.ptb.sw.Model;
import com.ptb.sw.RuleSource;
import com.ptb.sw.elements.*;
import com.ptb.sw.mimpl.MemMultiIndexModelBuilder;
import com.ptb.sw.reasoner.*;
import com.ptb.sw.reasoner.owl.OWLSpecies;
import com.ptb.sw.reasoner.builtins.BuiltinException;
import com.ptb.sw.reasoner.builtins.BuiltinRegistry;
import com.ptb.sw.reasoner.builtins.DefaultBuiltinRegistry;
import com.ptb.sw.reasoner.builtins.SW;
import static com.ptb.sw.reasoner.bwr.BWRFlag.*;
import com.ptb.sw.parsers.ModelBuilder;
import com.ptb.sw.parsers.ParseException;

import java.util.*;
import java.util.logging.Level;
import java.util.logging.Logger;


/**
 * This class implements a backward reasoning engine.
 * The constructor BackwardReasoner(Model model) accepts a model.
 * This is the abstract representation of a RDF graph with added rules.
 * The model can be queried by the method:<br>
 * public InfOutput query( List<Triple> pQuery )<br>
 * A new model can be set with the method:<br>
 * public void setModel(Model model)<br>
 * The class implements the interface InferenceData
 * This interface permits the builtin classes to retrieve certain data from
 * the backward reasoner.
 * <p/>
 * <p/>
 * <p/>
 *
 *     Example of the use:<br>
 * <p/>
 * <i>         File app1 = new File(testDir + File.separator + "gedcom-reduced.n3");<br>
 *            File app2 = new File(testDir + File.separator + "gedcom-simple-query.n3");
 * <p/>
 *            ModelBuilder mb = new MemMultiIndexModelBuilder();<br>
 *            mb.setContainersAsTriples( false );
 * <p/>
 *            Model m = mb.newModel( Syntax.N3, new FileInputStream( app1 ) );<br>
 *            Model query = mb.newModel( Syntax.N3, new FileInputStream( app2 ) );<br>
 *            int i = 1;
 * <p/>
 *            BackwardReasoner bw = new BackwardReasoner(m);<br>
 *            bw.setLogger("SEVERE");
 * <p/>
 *            for (TripleSet ts : bw.findSolutionSets(query)){<br>
 *                System.out.println("Solution " + i + ":\n" +
 * <p/>
 *                 ts.getTriples() + "\n");<br>
 *                 i++;<br>
 *            }<br>
 *            bw.reset(m);<br>
 *            System.out.println("Second query");<br>
 *            for (Model m : bw.applySolutions(query)){<br>
 *                 System.out.println("Solution " + i + ":\n" +<br>
 *                 m.getFacts() + "\n");<br>
 *                 i++;<br>
 *            }</i>
 * <p/>
 * <p/>
 *  <b><u>Basics of backward reasoning</u></b>
 * <p/>
 *     Backward reasoning starts with a query. The query is matched against the data triples
 *     and the triples of the consequent of the rules.
 *     The matching of two triples goes as follows:
 *     the two triples are matched element by element: first the two subjects are matched,
 *     then the two predicates and then the two objects.
 *     Two elements match when: one is a variable, both are variables or
 *     both are the same URI.
 * <p/>
 *     When a query matches with a data triple a solution is found.
 *     When a query matches with a consequent triple of a rule, then
 *     the antecedent triples of the rule become new 'queries' ie
 *     new triples to be proven. Normally, we call those new queries <b>goals</b>
 *     Each of the new goals must be 'proven'. Therefore they are
 *     stacked on the <b>goallist</b> and proven one by one.
 *     A goal can match with several data triples as well with several consequent triples of a rule.
 *     Each of these matches constitutes what is called an <b>alternative</b>.
 *     Each alternative can lead to a <b>solution</b>.
 * <p/>
 *     It can also happen that a goal is not matching with any data triple
 *     or consequent triple of a rule. This is called a <b>failure</b>. Thus some
 *     alternatives can lead to a failure. When a failure happens, the program looks
 *     into the <b>stack of alternatives</b> to see whether any alternatives where left.
 *     When all goals of the goallist have been proven and the goallist is empty,
 *     then a solution has been found. The inferencing then continues by retrieving an alternative
 *     from the stack of alternatives. When no more alternatives are left,
 *     the process is finished and all solutions have been found.
 * <p/>
 *     <b><u>Implementation</u></b>
 * <p/>
 *     The inferencing process is organized as a <b>Finite State Machine</b>.
 *     The states are:<br>
 * <p/>
 *     <b>INFERENCE</b><br>
 *     <b>CHOOSE</b><br>
 *     <b>FAILURE</b><br>
 *     <b>BUILTIN</b><br>
 *     <b>SOLUTION</b><br>
 *     <b>DONE</b>
 * <p/>
 *     INFERENCE is the start state, but is regularly used after start.
 *     The end state is of course DONE.
 *     The states are part of the method:
 *     <i>private void find()</i>
 * <p/>
 *     I say something more about each state:
 * <p/>
 *     <b>INFERENCE</b>
 * <p/>
 *     The goallist is initialized with the query. The first triple
 *     of the goallist is taken (if this triple is marked as being on
 *     hold it is just skipped: see further). If the predicate of the
 *     triple is a <b>builtin</b> a jump to the state BUILTIN is done,
 *     else the triple is matched with
 *     all possible data triples and consequents of rules generating
 *     alternatives. If there are no alternatives the state of the
 *     FSM is set to failure.
 * <p/>
 *     If there are alternatives a goall node is created and the alternatives
 *     are entered into the goallist node (GoallistNode.java) with the function:
 *     <i> public void setAlternatives( List<Alternative> altList ) </i>
 *     If there is more than one alternative some more happens:
 *     this goallist node is pushed on the <b>alternatives stack</b>.
 *     Also a pointer to the last entry of the <b>mainSubstitutionList</b>
 *     is saved in the goallist node. A copy of the goallist is saved
 *     into the goallist node. (in fact the function of a stack is fulfilled by the goallistnodes).
 *     But we do not need all goallist nodes in the alternative stack,
 *      only those with more than one alternative.
 * <p/>
 *     The other goallist nodes are however used for other functions.
 *     The current goal is marked as 'on hold'. The goal is not eliminated
 *     because we still need it in the <b>anti-looping</b> mechanism.
 *     If the goallist is empty upon entering the INFERENCE state,
 *     a solution has been found and the state is set to SOLUTION.
 * <p/>
 *     <b>CHOOSE</b>
 * <p/>
 *     In the INFERENCE state we have generated alternatives. All these alternatives
 *     must be looked into. We start by choosing one. This is the selection process.
 *     In BacwardReasoner.java the selection process is very simple:
 *     the first alternative from the list of alternatives is choosen.
 *     The substitutions associated with this alternative are added to the
 *     <b>mainSubstitutionList</b>.
 *     A new goallist node is created containing the alternative. If the
 *     <b>historyFlag</b> is set, the matching and matched triples from the alternative are saved
 *     (after substitution). These will serve then later for generating a proof
 *     and eventually deducing a new rule (see explanations about the 'generic query mechanism').
 *     The next state after the CHOOSE state is the INFERENCE state (the choosen
 *     alternative is the new goal).
 * <p/>
 *     <b>FAILURE</b>
 * <p/>
 *     If there are no more alternatives on the alternative stack, the
 *     the stats is DONE and inferencing finishes.
 *     Else a goallist node is retrieved from the alternative stack. If
 *     it has no alternatives left, the goallist node is discarded and
 *     another one is taken from the stack. if it has at elast one
 *     alternative left it becomes the current goallist node. The mainSubstitutionList and
 *     the goallist are restored to the state they had when this goallist node
 *     was saved on the alternative stack.
 *     The next state is CHOOSE.
 * <p/>
 *     <b>BUILTIN</b>
 * <p/>
 *     Depending on wich builtin is represented by the predicate of the goal,
 *     the relevant module is called. A builtin module always responds with a boolean.
 *     If the boolean is 'true' then the goal is discarded (these goals do not have to be
 *     kept for the anti-looping mechanism). A jump to the state INFERENCE is done.
 *     If 'false' is returned, a jump to the state FAILURE is done.
 *     Many builtins add subtitutions to the mainSubstitutionList.
 * <p/>
 *     <b>SOLUTION</b>
 * <p/>
 *     The solution wich is represented by the mainSubstitutionList is saved
 *     in the result set.
 *     If there are no more alternatives on the alternative stack,
 *     the state is DONE and inferencing finishes.
 *     Else a goallist node is retrieved from the alternative stack. If
 *     it has no alternatives left, the goallist node is discarded and
 *     another one is taken from the stack. if it has at least one
 *     alternative left it becomes the current goallist node. The mainSubstitutionList and
 *     the goallist are restored to the state they had when this goallist node
 *     was saved on the alternative stack.
 *     The next state is CHOOSE.
 * <p/>
 *     <b>DONE</b>
 * <p/>
 *     The results(solutions) are saved to the InfOutput object.
 *     If the 'historyFlag' is set, the kept history is transformed
 *     to a set of <b>proofs</b>.
 * <p/>
 *      <u>Method of BackwardReasoner.java: <i> private boolean unifyR( Triple pGoal )</i></u>
 * <p/>
 *      This method matches a goal with all rules and adds the alternatives
 *      found to the variable alts (List<Alternative> alts).
 * <p/>
 *      <u>Method of BackwardReasoner.java: <i> private boolean unifyF( Triple pGoal )</i></u>
 * <p/>
 *      This method matches a goal with all data triples and adds the alternatives
 *      found to the variable alts (List<Alternative> alts).
 * <p/>
 *      <b><u>The anti-looping system</u></b>
 * <p/>
 *      The inferencing process will loop when a goal has been applied to
 *      a rule and then, later in the process, the same goal is again applied to the same rule.
 *      If the first time the goal is applied leads to a second application of the same
 *      goal, there will be a third application etc...
 * <p/>
 *      By introducing lists, there is another way looping can occur ie
 *      when a goal contains a list and the same goals reappears again applied
 *      to the same rule but this time with a bigger list and each time the
 *      rule makes the list bigger. This is the equivalen <of what in prolog is
 *      remediated by an 'occurs check'. This occurs check is also done in
 *      BackwardReasoner.java. However if the flag 'occursFlag' is set to
 *      false, this check is not done. The reason for introducing this flag is that
 *      the 'occurs check' is resource intensive and for the programmer it
 *      is relatively easy to avoid this kind of looping. In automated
 *      environments the policy perhaps might better be to give this flag the value 'true'.
 * <p/>
 *      Now back to the main anti-looping mechanism. In order to stop applying the same goal
 *      to the same rule again, two things are necessary:
 *      1) define when two goals are equal
 *      2) remember which goals have been applied to a certain rule.
 * <p/>
 *      1) when are two goals equal? This might seem a stupid question but
 *      are the two following goals equal:<br>
 *      <i>?a :b :c.</i> and <i>?x :b :c.</i><br>
 *      The answer is yes because the query:<br>
 *      <i>?a :b :c.</i> is equal to the query:<br>
 *      <i>?x :b :c.</i>.
 * <p/>
 *      2) There are several ways to remember the application of
 *      a goal. Eg we could make a hashtable where for each rule
 *      we enter the applied goals. This can be done, but it is
 *      not the most efficient way.
 *      Anyway, we need a goallist in inferencing and it is therefore
 *      not a bad idea to use this goallist for the anti-looping.
 *      Indeed the goallist is a list of goals that should be
 *      applied. It is not a list of goals, normally, that have been applied *      but we can make it into that. So when a goal has been applied,
 *      instead of deleting it, we keep it and mark it as already
 *      been applied ie we mark it as 'on hold'. But this is not enough.
 *      For the anti-looping we also need to know if this goal was applied to a rule
 *      and to which rule. Therefore I created an object I called GoalUse.java
 *      and instead of keeping a list of goals I keep a list of GoalUse objects.
 *      In these GoalUse objects then the rule is marked after
 *      application of the goal  as well as a flag indicating
 *      whether the goal is on hold or not.
 *      So when a goal is matched with a rule, a check is done comparing
 *      all goals on hold in the goallist to see whether this goal has
 *      already previously matched with a rule.
 *      When this is the case, the match is negative ie the goal is not
 *      again matching with the rule to prevent looping.
 * <p/>
 *      <b><u>The generation of a proof</u></b>
 * <p/>
 *      Giving a solution to a query is one thing; but a skeptic or
 *      an instance might ask for a proof of the solution.
 *      If the historyFlag was set, the engine can deliver a proof.
 *      Whenever a goal matches with a data triple, the two triples are kept.
 *      If a goal matches with a rule, the rule and the goal are kept.
 *      A sequence of these pairs constitute the proof.
 *      For better readability the proof is presented in the sequence
 *      that a forward reasoner will give.
 * <p/>
 *      In the same way when the researchFlag is set, the engine will keep data
 *      about the failures and can then afterwards show the history of
 *      all paths leading to a failure. A failure path is represented in reverse
 *      ie in the sequence that was followed in the engine.
 * <p/>
 *      See also:  <a>http://www.jdrew.org/jDREWebsite/tutorial/jDREWTutorial.ppt</a>
 *        or logic textbooks/tutorials (there are plenty on the internet).
 *
 *       For instance: <a>http://www.csupomona.edu/~jrfisher/www/prolog_tutorial/contents.html</a>
 *
 * @author Guido Naudts
 */
public class BackwardReasoner extends BWRAbstractReasoner implements InferenceData {

   private static Logger LOGGER = Logger.getLogger( "BackwardReasoner" );


   /**
    * integer for numbering rules
    */
   private int _ruleCnt = 1;

   /**
    * the list of accumulated substitutions during the inferencing process
    */
   private SubstitutionList _mainSubstitutionList;

   /**
    * the results are kept as a list of substitutionlists
    */
   private List<SubstitutionList> _results;

   /**
    * stack of nodes that have alternatives; for fast access
    */
   private Stack<GoallistNode> _alternativeStack;
    /**
     * stack to keep pointers to the _alternativeStack for implementation
     * of 'not' and 'cut' builtins
     */
    private Stack<Integer> _altPointerStack;

   /**
    * the list of all goals that have to be 'proved'
    */
   private List<GoalUse> _goallist;

   /**
    * the current node
    */
   private GoallistNode _currentNode;

   /**
    * alternatives after matching
    */
   private Stack<Alternative> _alts;

   /**
    * help variable
    */
   private SubstitutionList _coll;

   /**
    * maps all rules to an integer; for anti-looping
    */
   private HashMap<Rule, Integer> _ruleMap;

   /**
    * the rule level for renumbering variables
    */
   private int _ruleLevel = 1;

   /**
    * parameter for testing; limitation of the inferencing process
    * if the inference limit is greater than zero and greater than the loopCounter
    * then the inferencing process is stopped
    */
   private int _inferenceLimit = 0;

   /**
    * counter for inferenceloops
    */
   private int _loopCounter = 0;

   /**
    * solution counter: when _solution number of solutions have been found
    * inferencing stops.
    */
   private int _solutions = 0;

   /**
    * counts the solutions
    */
   private int _solutionCounter = 0;

   /**
    * the current goal as GoalUse object
    */
   private GoalUse _currentGoalUse;

   /**
    * the current goal as triple
    */
   private Triple _currentGoal;

   /**
    * This flag indicates that alternatives were added by a builtin
    */
   private boolean _alternateFlag = false;

   /**
    * the default registry of the builtins
    */
   private BuiltinRegistry _builtinRegistry = DefaultBuiltinRegistry.getUserRegistry();

    /**
     * flag that checks whether a query has happened already; in yes, a reset is done.
     */
   private boolean firstQueryDone = false;

   /**
    * object that contains the routine for comparing elements
    *
    */
   private IElementComparator elemComparator;

   /**
    * if true, the reasoner works in cached mode.
    */
   private boolean _cached = false;

   private Model _cache;

   private ModelBuilder _mb;

   private boolean _owlBuiltin;

   private List<Rule> _brulesSave;

   /////////////////////////////////////////////////////////////////////////////
   //
   // Constructors
   //

   /**
    * if instantiating like this, use setFacts() and setRuleSource() afterwards
    */
   public BackwardReasoner() {
      super();
   }


   /**
    * instantiate with a model that also contains rules.
    * If it does not contain rules, then use afterwards setRuleSource()
    *
    * @param pBase
    */
   public BackwardReasoner( Model pBase ) {
      super( pBase );
   }

   /**
    * create a reasoner with facts and rules
    *
    * @param pFacts
    * @param pRules
    */
   public BackwardReasoner( Model pFacts, RuleSource pRules ) {
      super( pFacts, pRules );
   }


   /**
    * create a reasoner with an OWLBox
    * @param pOWLData
    */
   public BackwardReasoner( OWLData pOWLData ) {
      super( pOWLData );
   }


   public BackwardReasoner( OWLData pOWLData, BWRFlagOwnerImpl pMap ) {
      super( pOWLData, pMap );
   }

   //
   // (Constructors)
   //
   /////////////////////////////////////////////////////////////////////////////

   /////////////////////////////////////////////////////////////////////////////
   //
   // 'InferenceData' methods
   //
   public BackwardReasoner cloneReasoner(){
      return cloneReasoner( false );
   }


   /**
    * Clone a reasoner with the same characteristics as this reasoner:
    * flags, facts and rules.
    * @return Reasoner
    */
   public BackwardReasoner cloneReasoner( boolean nofacts){
       BackwardReasoner br = new BackwardReasoner();
       for( Flag f: getValidFlags() ) {
          br.setFlag( f , getFlag( f ));
       }
       if ( ! nofacts ){
          br.setFacts( getFacts() );
       }else{
          ModelBuilder mb = new MemMultiIndexModelBuilder();
          mb.setContainersAsTriples(false);
          Model m = mb.newModel();
          // add dummy triple
          m.add( RDF.TYPE, OWL.CLASS, RDF.TYPE);
          br.setFacts( m );

       }
       br.setRuleSource( getRuleSource());
       // must we clone the rules and the facts
       br._brules = new ArrayList<Rule>(_brules);
       br._ruleMap = new HashMap<Rule, Integer>(_ruleMap);
       br.setOWLData( getOWLData());
       br._loopCounter = 0;
       br._results = new ArrayList<SubstitutionList>( 5 );
       br._alternativeStack = new Stack<GoallistNode>();
       br._altPointerStack = new Stack<Integer>();

       br.setFlag( INITIALIZED_FLAG, true );

       return br;
   }

   /**
    * Add new facts to the model that is used by this reasoner.
    *
    * @param pNewFacts
    */
   public void addNewFacts( Collection<Triple> pNewFacts ) {
      getFacts().add( pNewFacts );
   }

   /**
    * Remove facts from the model that is used by this reasoner.
    *
    * @param pFacts
    */
   public void removeFacts( Collection<Triple> pFacts ) {
      getFacts().remove( pFacts );
   }

    /**
     * Remove rules from the model that is used by this reasoner.
     *
     * @param pRules
     */
    public void removeRules( Collection<Rule> pRules ) {
       _brules.remove( pRules );
    }

   /**
    * Add new rules to the model that is used by this reasoner.
    *
    * @param pRules
    */
   public void addNewRules( Collection<Rule> pRules ) {
      for (Rule r : pRules){
         _ruleCnt++;
         _ruleMap.put(r, _ruleCnt);
         if ( ! _brules.contains(r)){
            _brules.add( r );
         }
      }
   }

   public void setCacheFlag( boolean pValue){
       _cached = pValue;
   }

   /**
    * Get the current goal.
    *
    * @return the goal
    */
   public Triple getCurrentGoal() {
      return _currentGoal;
   }

   /**
    * Add a triple to the goallist
    *
    * @param pPosition
    * @param pTriple
    * @return true if the triple is added; false if the triple could  not be added.
    */
   public boolean addTripleToGoallist( int pPosition, Triple pTriple ) {

      boolean result = false;
      if( pPosition <= _goallist.size() ) {
         _goallist.add( pPosition, new GoalUse( pTriple ) );
         result = true;
      }
      return result;
   }

   /**
    * Remove a triple from the goallist/
    *
    * @param pPosition
    * @return true if the triple could be removed; false if not.
    */
   public boolean removeTripleFromGoallist( int pPosition ) {

      boolean result = false;
      if( pPosition < _goallist.size() ) {
         _goallist.remove( pPosition );
         result = true;
      }
      return result;
   }

   /**
    * Gets a triple from the goallist.
    *
    * @param pPosition
    * @return a triple or null if it could not be retrieved.
    */
   public Triple getTripleFromGoallist( int pPosition ) {
      return pPosition < _goallist.size() ? _goallist.get( pPosition ).getGoal() : null;
   }

    /**
     * query using a rule and facts model and a query model.
     * The defined builtin registry is copied into a new reasoner.
     * @param m
     * @param ml
     * @return a list of answers. Each answer is a list of triples.
     */
   public List<List<Triple>> query(Model m, Model ml){
     AdvancedBWR bwr = new AdvancedBWR(m);
     bwr.setBuiltinRegistry(getBuiltinRegistry());
     InferenceOutput output = bwr.queryByTriples( ml.getTriples() );
     return output.getAnswerTriples();
   }

    /**
     * Make a query using the facts and rules of the current reasoner and
     * a query in the form of a list of triples.
     * Lists must be in the form of elementcontainers.
     * The sequence of triples in the query is conserved.
     * @param pT
     * @return a list of answers. Each answer is a list of triples.
     */
    public List<TripleSet> queryS(List<Triple> pT) {
       BackwardReasoner bwr = cloneReasoner();
       bwr.query( pT );
       List<SubstitutionList> answer = InfUtils.cleanSubstitutions( bwr._results, pT );
       List<TripleSet> out = new ArrayList<TripleSet>(answer.size());
       for( SubstitutionList substl : answer ) {
          out.add(new TripleSet( substl.applyToTripleset( pT )));
       }
       return out;
    }

   public List<TripleSet> queryS(List<Triple> pT, BackwardReasoner pBwr) {
      pBwr.query( pT );
      List<SubstitutionList> answer = InfUtils.cleanSubstitutions( pBwr._results, pT );
      List<TripleSet> out = new ArrayList<TripleSet>(answer.size());
      for( SubstitutionList substl : answer ) {
         out.add(new TripleSet( substl.applyToTripleset( pT )));
      }
      return out;
   }

   public List<TripleSet> queryS(Triple pTriple, BackwardReasoner pBwr) {
      List<Triple> list = new ArrayList<Triple>(1);
      list.add( pTriple );
      pBwr.query( list );
      List<SubstitutionList> answer = InfUtils.cleanSubstitutions( pBwr._results, list );
      List<TripleSet> out = new ArrayList<TripleSet>(answer.size());
      for( SubstitutionList substl : answer ) {
         out.add(new TripleSet( substl.applyToTripleset( list )));
      }
      return out;
   }

   /**
    * Make a query using the facts and rules of the current reasoner and
    * a query in the form of a list of triples.
    * Stops when finding one solution.
    * Lists must be in the form of elementcontainers.
    * The sequence of triples in the query is conserved.
    * @param pT
    * @return a list of answers. Each answer is a list of triples.
    */
   public List<TripleSet> querySingle(List<Triple> pT) {
      BackwardReasoner bwr = cloneReasoner();
      bwr.setFlag( ONE_SOLUTION, true );
      bwr.query( pT );
      List<SubstitutionList> answer = InfUtils.cleanSubstitutions( bwr._results, pT );
      List<TripleSet> out = new ArrayList<TripleSet>(answer.size());
      for( SubstitutionList substl : answer ) {
         out.add(new TripleSet( substl.applyToTripleset( pT )));
      }
      return out;
   }

   //
   // ('InferenceData' methods)
   //
   /////////////////////////////////////////////////////////////////////////////

   /////////////////////////////////////////////////////////////////////////////
   //
   // 'Reasoner' methods
   //

   /**
    * Find all solutions to a query of the current model of the reasoner
    * in the form of a set of Solution objects.
    * Attention: redundant solutions are given too.
    * If no redundant solutions are wanted see method findSolutionSets()
    * and applySolutions()
    * Attention: this does not respect the sequence of triples in the query!!!
    *
    * @param pQuery
    * @return all solutions.
    */
   public Set<Solution> findSolutions( Model pQuery ) {

      Collection<Triple> queryT = checkQueryTriples( pQuery.getTriples());
      query( queryT );
      queryT = clearLogSequence( queryT );
      //List<SubstitutionList> answer = InfUtils.cleanSubstitutions( _results, queryT );
      Set<Solution> sols = new HashSet<Solution>( 2 );
      if (_mb == null){
          _mb = new MemMultiIndexModelBuilder();
          _mb.setContainersAsTriples( false );
      }
      pQuery = _mb.newModel();
      pQuery.add( queryT );
      for( SubstitutionList substl : _results) { //answer ) {
         sols.add( new Solution( substl, pQuery ) );
      }

      return sols;
   }

   /**
    * Find all solutions to a query of the current model of the reasoner
    * in the form of a list of TripleSet objects.
    * Redundant solutions are eliminated.
    *
    * @param pQuery
    * @return all solutions.
    */
   public List<TripleSet> findSolutionSets( Model pQuery ) {
      Set<Solution> sols = findSolutions( pQuery );
      List<List<Triple>> setsOut = new ArrayList<List<Triple>>( 3 );

      for( Solution sol : sols ) {
         setsOut.add( sol.getSolutionTriples() );
      }
      setsOut = InfUtils.eliminateDoubleTriplesets( setsOut );
      List<TripleSet> solsOut = new ArrayList<TripleSet>( setsOut.size() );
      for( List<Triple> lt : setsOut ) {
         solsOut.add( new TripleSet( lt ) );
      }
      return solsOut;
   }

   /**
    * Find all solutions to a query of the current model of the reasoner
    * in the form of a set of models.
    * Redundant solutions are eliminated.
    *
    * @param pQuery
    * @return all solutions.
    */
   public Set<Model> applySolutions( Model pQuery ) {
      Model m;
      ModelBuilder mb = new MemMultiIndexModelBuilder();
      mb.setContainersAsTriples(false);
      Set<Solution> sols = findSolutions( pQuery );
      List<List<Triple>> setsOut = new ArrayList<List<Triple>>( 3 );

      for( Solution sol : sols ) {
         setsOut.add( sol.getSolutionTriples() );
      }
      setsOut = InfUtils.eliminateDoubleTriplesets( setsOut );
      Set<Model> models = new HashSet<Model>( setsOut.size() );
      for( List<Triple> triples : setsOut ) {
         m = mb.newModel();
         m.add( triples );
         models.add( m );
      }
      return models;
   }

   //
   // ('Reasoner' methods)
   //
   /////////////////////////////////////////////////////////////////////////////

   /////////////////////////////////////////////////////////////////////////////
   //
   // 'FlagOwner' methods
   //

   /**
    * Certain aspects of the reasoner are manipulated using flags.
    * This method returns a list of the flag values.
    *
    * @return a list of the flags
    */
   public BWRFlag[] getValidFlags() {
      return BWRFlag.values();
   }

   //
   // ('FlagOwner' methods)
   //
   /////////////////////////////////////////////////////////////////////////////

   /////////////////////////////////////////////////////////////////////////////
   //
   // Other public methods
   //

   /**
    * The builtin registry contains all builtins that can be used.
    *
    * @return the current builtin registry
    */
   public BuiltinRegistry getBuiltinRegistry() {
      return _builtinRegistry;
   }

   /**
    * The given builtin registry will be used for handling builtins.
    *
    * @param pBuiltinRegistry
    */
   public void setBuiltinRegistry( BuiltinRegistry pBuiltinRegistry ) {
      _builtinRegistry = pBuiltinRegistry;
   }

   /**
    * The inference limit limits the number of loops that the engine executes.
    * This is a testing feature that is useful if a testcase presents
    * combinatorial explosion. When the number of loops is finished,
    * the process stops and the logging can be examined.
    *
    * @param pInferenceLimit
    */
   public void setInferenceLimit( int pInferenceLimit ) {
      _inferenceLimit = pInferenceLimit;
   }

   /**
    * The GoallistNode contains all data that are necessary for
    * returning to the current state.
    *
    * @return the current GoallistNode
    */
   public GoallistNode getCurrentNode() {
      return _currentNode;
   }

   /**
    * @return the main substitutionlist
    */
   public SubstitutionList getMainSubstitutionList() {
      return _mainSubstitutionList;
   }

   /**
    * determines the number of solutions that is searched for
    * @param pCounter
    */
   public void setSolutionCounter( int pCounter ){
      _solutions = pCounter;
   }

   /**
    * This method return the list of rules that are needed for a given query.
    *
    * @param pQuery
    * @return a list of rules
    */
   public List<Rule> getNeededRules( Set<Triple> pQuery ) {
         // calculate the list of necessary rules
         List<Rule> selected = new ArrayList<Rule>( 5 );
         RuleSelector selector = new RuleSelector( _brules );
         List<Iterator<Rule>> iteratorList;
         for( Triple t : pQuery ) {
            if ( t.getPredicate().equals( SW.SEQUENCE )){
               if ( ! t.getObject().isTripleSet()){
                  throw new IllegalArgumentException( "The object of log:sequence must be a tripleset:\n" + t + "\n");
               }
               for ( Triple t1: t.getObject().asTripleSet().getTriples()){
                  iteratorList = selector.getRuleIterator( t1 );
                  for( Iterator iterator : iteratorList ) {
                     while( iterator.hasNext() ) {
                        selected.add( ( Rule ) iterator.next() );
                     }
                  }

               }
            }else if( isCurrentGoalBuiltin (t)){
               // do nothing
            }else{

               iteratorList = selector.getRuleIterator( t );
               for( Iterator iterator : iteratorList ) {
                  while( iterator.hasNext() ) {
                     selected.add( ( Rule ) iterator.next() );
                  }
               }
            }
         }


      // selected = InfUtils.eliminateDoubleRules( selected );
      if (selected.isEmpty()){
         return _brules;
      }
      return selected;
   }



   //
   // (Other public methods)
   //
   /////////////////////////////////////////////////////////////////////////////

   /////////////////////////////////////////////////////////////////////////////
   //
   // Private methods
   //

    /**
     * Initializes the reasoner after initialization.
     */
   protected void initializeReasoner() {
      checkDB();

      _loopCounter = 0;
      _results = new ArrayList<SubstitutionList>( 5 );
      _alternativeStack = new Stack<GoallistNode>();
      _altPointerStack = new Stack<Integer>();

      _ruleMap = new HashMap<Rule, Integer>( 3 );
      if (_brules == null){
         _brules = new ArrayList<Rule>( getRules() );
      }
      _ruleCnt = 1;
      //numberRules();
      if (_cached){
         _mb = new MemMultiIndexModelBuilder();
         _mb.setContainersAsTriples(false);
         _cache = _mb.newModel();
      }
      setFlag( INITIALIZED_FLAG, true );
   }

    /**
     * Initializes the reasoner for a new query.
     */
   protected void initializeReasonerForQuery() {

      _loopCounter = 0;
      _results = new ArrayList<SubstitutionList>( 5 );
      _alternativeStack = new Stack<GoallistNode>();
      if( getFlag( SELECT_RULES_FLAG ) ) {
         _brules = _brulesSave;
      }

        if (_cached){
           _cache = _mb.newModel();
        }

      setFlag( INITIALIZED_FLAG, true );
   }

    /**
     *
     * Gets the results of a query.
     * @param pQuery
     */
   protected void query( Collection<Triple> pQuery ) {

      boolean grounded = true;

      if (! getFlag( INITIALIZED_FLAG)){
         initializeReasoner();
      }
      if( LOGGER.isLoggable( Level.FINE ) ) {
         LOGGER.fine( "\n##### START OF QUERY #####\n" );
      }

      if( LOGGER.isLoggable( Level.FINER ) ) {
         LOGGER.finer( "Model triples: " + InfUtils.tripleListToN3( new ArrayList<Triple>( getTriples() ), "", false ) );
         LOGGER.finer( "Model rules: " + InfUtils.ruleListToN3( _brules, " ", false ) );
         LOGGER.finer( "Model query: " + InfUtils.tripleListToN3( new ArrayList<Triple>( pQuery ), "", false ) );
      }

      checkRuleSelection( pQuery );
      pQuery = checkQueryTriples( pQuery );
      List<Triple> querySet = new ArrayList<Triple>( pQuery.size() );
      querySet.addAll( pQuery );
      if (getOWLSpecies() != OWLSpecies.NONE){
         querySet = super.getOWLData().replaceInQuery(querySet);
      }
        for (Triple t: querySet){
            if (! InfUtils.testGrounded( t )){
                grounded = false;
            }
        }
        if ( grounded ){
            setSolutionCounter( 1 );
        }

      infOutputQuerySetJoinPoint(  checkQueryTriples( pQuery ));
      initGoals( querySet );
      _mainSubstitutionList = new SubstitutionList( 6 );

      // The initial step consists of the triples making up the query

      _currentNode.setRuleLevel( _ruleLevel );

      genericQueryCheckJoinPoint( querySet );
      historyFlagSettingJoinPoint();

      find();
      infOutputResultsJoinPoint();

      proofsJoinPoint();
      failuresJoinPoint();
      ruleGenerationJoinPoint( pQuery, querySet );
   }

   protected void infOutputResultsJoinPoint() {
   }

   protected void infOutputQuerySetJoinPoint( List<Triple> pQuerySet ) {
   }

   protected int getLoopCounter() {
      return _loopCounter;
   }

   protected List<SubstitutionList> getResults() {
      return _results;
   }

   protected SubstitutionList getColl() {
      return _coll;
   }

   protected void setColl( SubstitutionList pColl ) {
      _coll = pColl;
   }

   protected int getRuleLevel() {
      return _ruleLevel;
   }

   protected int getRuleCnt() {
      return _ruleCnt;
   }

   protected void setRuleCnt( int pRuleCnt ) {
      _ruleCnt = pRuleCnt;
   }

   protected void setRules( List<Rule> pRules ) {
      _brules = pRules;
   }

    /**
     * Advanced method: from the obtained proofs new rules are derived,
     * that can later be used to optimize queries.
     * @param pQuery
     * @param pQuerySet
     */
   protected void ruleGenerationJoinPoint(
         Collection<Triple> pQuery, List<Triple> pQuerySet ) {
   }

   protected void failuresJoinPoint() {
   }

   protected void proofsJoinPoint() {
   }

    /**
     * Look whether the ruleset can be replaced by a more simplified ruleset
     * @param pQuerySet
     */
   protected void genericQueryCheckJoinPoint( List<Triple> pQuerySet ) {
   }

   protected void historyFlagSettingJoinPoint() {
   }

    /**
     * Creates the initial GoalUse objects from the query.
     * @param pQuerySet
     */
   protected void initGoals( List<Triple> pQuerySet ) {

      // the next goal will be the highest on the goal list
      _goallist = new ArrayList<GoalUse>( pQuerySet.size() + 2 );
      _currentNode = new GoallistNode();
      GoalUse gUse;
      for( Triple t : pQuerySet ) {
         gUse = new GoalUse( t );
         _goallist.add( gUse );
      }
   }

    /**
     * Eliminates the list declarations from the query.
     * Also blank nodes are replaced by AnonVariables.
     * @param pQuery
     * @return a list of triples
     */
   private List<Triple> checkQueryTriples( Collection<Triple> pQuery ) {

      List<Triple> querySet = new ArrayList<Triple>( pQuery.size() );
      MutablePattern pattern;
      Map<Element, Element> bNodes = new HashMap<Element, Element>(2);
      for( Triple t : pQuery ) {
         if( InfUtils.testListDeclaration( t ) ) {
            continue;
         }
         if (t.getPredicate().equals(SW.SEQUENCE)){
            if ( ! t.getObject().isTripleSet()){
               throw new IllegalArgumentException(" Invalid swlog:sequence builtin :\n " + t + "\n" );
            }
            for (Triple t1 : t.getObject().asTripleSet().getTriples()){
                pattern = getPattern(t1, bNodes);
                querySet.add( pattern.freeze() );

            }
         }else{
            pattern = getPattern(t, bNodes);
            querySet.add( pattern.freeze() );
         }
      }

      return querySet;
   }

   private MutablePattern getPattern(Triple t, Map<Element, Element> pBNodes ) {
      MutablePattern pattern;
      Element elem;
      Variable v;

      pattern = new MutablePattern();
      for ( TriplePos pos : TriplePos.values() ){
         elem = t.getElementAt( pos );
         if ( ! elem.isVariable() && ! elem.isElementContainer()
                     && ! elem.isTripleSet() && elem.isBlankNode() ){
            if (! pBNodes.containsKey( elem )){
                v = new AnonVariable();
                pattern.setCombination( pos, v);
                pBNodes.put(elem, v);

            }else{
                pattern.setCombination( pos, pBNodes.get( elem ));
            }
         }else{
            pattern.setCombination( pos, t.getElementAt( pos ) );
         }
      }
      return pattern;
   }

   /**
    * If the flag SELECT_RULES_FLAG is set, then make a preliminary selection
    * of the rules before executing the query.
    * @param pQuery
    */
  private void checkRuleSelection( Collection<Triple> pQuery ) {

     if( getFlag( SELECT_RULES_FLAG ) ) {

        // calculate the list of necessary rules
        List<Rule> selected = new ArrayList<Rule>( 5 );
        RuleSelector selector = new RuleSelector( _brules );
        List<Iterator<Rule>> iteratorList;
        for( Triple t : pQuery ) {
           if ( t.getPredicate().equals( SW.SEQUENCE )){
              if ( ! t.getObject().isTripleSet()){
                 throw new IllegalArgumentException( "The object of log:sequence must be a tripleset:\n" + t + "\n");
              }
              for ( Triple t1: t.getObject().asTripleSet().getTriples()){
                 iteratorList = selector.getRuleIterator( t1 );
                 for( Iterator iterator : iteratorList ) {
                    while( iterator.hasNext() ) {
                       selected.add( ( Rule ) iterator.next() );
                    }
                 }

              }
           }else if( isCurrentGoalBuiltin (t)){
              // do nothing
           }else{

              iteratorList = selector.getRuleIterator( t );
              for( Iterator iterator : iteratorList ) {
                 while( iterator.hasNext() ) {
                    selected.add( ( Rule ) iterator.next() );
                 }
              }
           }
        }
        _brulesSave = _brules;
        _brules = selected;
        _ruleMap = new HashMap<Rule, Integer>( 3 );
        _ruleCnt = 1;

     }
       _brules = InfUtils.eliminateDoubleRules( _brules );
        numberRules();
  }

    /**
     * The main loop of the inference engine.
     */
   private void find() {

      if ( firstQueryDone ){
          reset();
      }else{
         firstQueryDone = true;
      }

      findStartJoinPoint();

      _currentGoal = null;

      States status = States.INFERENCE;

      while( status != States.DONE ) {

         if( LOGGER.isLoggable( Level.FINER ) ) {
            LOGGER.finer( "Status = " + status );
         }

         if( getFlag( PERFORMANCE_FLAG ) || _inferenceLimit > 0 ) {
            _loopCounter++;
         }

         if( _inferenceLimit > 0 && _loopCounter > _inferenceLimit ) {
            status = States.DONE;
         }

         switch( status ) {



            case INFERENCE:
               status = onInference();
               break;

            case CHOOSE:
               status = onChoose();
               break;

            case FAILURE:
               status = onFailure();
               break;

            case BUILTIN:
               status = onBuiltin();
               break;

            case SOLUTION:
               status = onSolution();
               break;

            case DONE:
               break;
         }

      }

      findEndJoinPoint();
      OWLData pOWL= getOWLData();
      if ( pOWL != null ){
          if ( pOWL.getSameAsIndex() != null &&  ! pOWL.getSameAsIndex().isEmpty()){
             _results = InfUtils.addSameAs(_results, pOWL.getSameAsIndex());
          }
      }
   }

    /**
     * State gone to when a solution has been found.
     * @return the next state
     */
   private States onSolution() {

      States status;
      if( LOGGER.isLoggable( Level.FINE ) ) {
         LOGGER.fine( "Solution: " + _mainSubstitutionList.toN3() );
      }

      saveResults();
      _solutionCounter++;

      if( !searchAlternative() ) {

         status = States.DONE;

      } else {

         saveHistoryJoinpoint();

         int substitutionListPointer = _currentNode.getSubstitutionListPointer();
         _mainSubstitutionList = new SubstitutionList( _mainSubstitutionList.subList( 0, substitutionListPointer ) );
         _goallist = _currentNode.getGoallist();
         _currentGoalUse = _goallist.get( 0 );
         setFlag( LOGICS_FLAG, _currentNode.getLogicsFlag() );
         status = States.CHOOSE;
      }

      if( (getFlag( ONE_SOLUTION ) && _solutionCounter == 1) || (_solutions > 0 && _solutionCounter == _solutions )) {
         status = States.DONE;
      }

      return status;
   }

   protected void saveHistoryJoinpoint() {
   }

    /**
     * State gone to when a builtin is encountered.
     * @return the next state.
     */
   private States onBuiltin() {

      if( LOGGER.isLoggable( Level.FINE ) ) {
         LOGGER.fine( "Builtin: " + InfUtils.tripleToN3( _currentGoal, " ", false ) );
      }

      States status;
      URIRef current =  getCurrentGoal().getPredicate().asURIRef();
      // intercept 'not' and 'cut' builtins to push current alt-entry on stack
      if ( current.equals( SW.NOT ) || current.equals( SW.CUT )) {
          _altPointerStack.push( _alternativeStack.size());
      }
      try {

         status = handleBuiltin( current ) ? States.INFERENCE : States.FAILURE;

      } catch( BuiltinException bex ) {

         LOGGER.log( Level.SEVERE, bex.getMessage(), bex );
         throw new IllegalStateException("Builtin error : " + bex);
      }


      _goallist.remove( 0 );
      _currentNode.addMatchingTriple( _currentGoal );
      _currentNode.addMatchedTriple( _currentGoal );

      if( LOGGER.isLoggable( Level.FINER ) ) {
         LOGGER.finer( "Substitutions: " + _mainSubstitutionList.toN3() );
      }
      if (_alternateFlag){
         _alternateFlag = false;
         status = States.CHOOSE;
      }
      return status;
   }

    /**
     * Jump to the correct builtin instance.
     * @return boolean
     * @throws BuiltinException
     */
   private boolean handleBuiltin( URIRef current   ) throws BuiltinException {
      if ( _owlBuiltin ){
         return getOWLData().getOWLCache().getBuiltin( current ).process( this );
      }
      return _builtinRegistry.getBuiltinInstance( current ).process( this );
   }

   public void unstackAltStack(){
      Integer size = _altPointerStack.pop();
      while ( _alternativeStack.size() > size ){
         _alternativeStack.pop();
      }
   }

    /**
     * Tests whether the current goal is a builtin.
     * @return boolean
     */
   private boolean isCurrentGoalBuiltin( Triple pGoal) {
      _owlBuiltin = false;
      Element candidate = pGoal.getPredicate();
      if (candidate.isURIRef()){
         if ( getOWLData() != null && getOWLData().getOWLCache().checkBuiltin( candidate.asURIRef() )){
            _owlBuiltin = true;
            return true;
         }
         return _builtinRegistry.isRegistered( candidate.asURIRef() );
      }else{
         return false;
      }
   }

    /**
     * State gone to when a failure happens during the reasoning process.
     * @return the next state.
     */
   private States onFailure() {

       if( LOGGER.isLoggable( Level.FINE ) ) {
          LOGGER.fine( "Failure !!" );
       }

      if( getFlag( LOGICS_FLAG ) ) {
         // take measures for 'not', 'or' and 'eor' builtins.
         return handleLogicBuiltins();
      }

      onFailureJoinPoint();

      States status;
      // this alternative was a failure

      if( !searchAlternative() ) {

         status = States.DONE;

      } else {

         saveHistoryJoinpoint();

         int substitutionListPointer = _currentNode.getSubstitutionListPointer();

         _mainSubstitutionList = new SubstitutionList
               ( _mainSubstitutionList.subList( 0, substitutionListPointer ) );

         _goallist = _currentNode.getGoallist();

         setFlag( LOGICS_FLAG, _currentNode.getLogicsFlag() );

         _currentGoalUse = _goallist.get( 0 );

         status = States.CHOOSE;
      }

      return status;
   }

   protected void onFailureJoinPoint() {
   }

    /**
     * State gone to when a new alternative must be choosen.
     * @return the next state.
     */
   private States onChoose() {

      Alternative alt = _currentNode.getAlternative();
      if( alt.getFromRule() ) {
         _currentGoalUse.setRuleNumber( _ruleMap.get( alt.getMatchedTriple() ) );
         _currentGoalUse.setFromRuleFlag();
      } else {
         _currentGoalUse.setRuleNumber( 0 );
         _currentGoalUse.resetFromRuleFlag();
      }

      // following sets the goallist, the substitutionmaps
      // and the history triples
      // the substitutions of the alternative are added to _mainSubstitutionList
      GoallistNode childNode = new GoallistNode( alt, _mainSubstitutionList );
      setGoallist( alt );
      _currentNode.addChild( childNode );
      childNode.setParent( _currentNode );
      if( getFlag( HISTORY_FLAG ) ) {
         childNode.setHistory( _currentNode.getMatchingTriples(),
               _currentNode.getMatchedTriples() );
         childNode.addMatchingTriple( alt.getMatchingTriple() );
         childNode.addMatchedTriple( alt.getMatchedTriple() );
      }
      _currentNode = childNode;
      return States.INFERENCE;
   }

   /**
    * Adds the triples of an alternative to the goallist.
    * @param pAlt
    */
  private void setGoallist( Alternative pAlt ) {
     List<Triple> alts = pAlt.getTriples();
     for( int i = alts.size() - 1; i >= 0; i-- ) {
        GoalUse gUse = new GoalUse( alts.get( i ) );
        _goallist.add( 0, gUse );
        if( Rule.isARule( pAlt.getMatchedTriple() ) ) {
           gUse.setFromRuleFlag();
        }
     }
  }



    /**
     * State for checking the truth value of a goal.
     * @return the next state.
     */
   private States onInference() {

      Triple tc;

      if( _goallist.size() == 0 ) {

         // there are no more goals in the goallist
         // all goals are resolved
         return States.SOLUTION;

      } else {

         _currentGoalUse = _goallist.get( 0 );
         if( _currentGoalUse.testOnHold() ) {
            if( LOGGER.isLoggable( Level.FINER ) ) {
               LOGGER.finer( "Goal on hold: " + InfUtils.tripleToN3( _currentGoalUse.getGoal(), " ", false ) );
            }
            if ( _cached ){
               tc = _currentGoalUse.getGoal();
               if (InfUtils.testGrounded( tc )){
                  _cache.add( tc );
                  getFacts().add( tc );
               }
            }
            _goallist.remove( 0 );
            return States.INFERENCE;
         }

         if( _currentGoalUse.testListDeclaration() ) {
            _goallist.remove( 0 );
            return States.INFERENCE;
         }

         _currentGoal = _currentGoalUse.getGoal();
         _currentGoal = _mainSubstitutionList.applyToTriple( _currentGoal );

          if( LOGGER.isLoggable( Level.FINER ) ) {
             LOGGER.finer( "Goallist: " + _goallist );
             LOGGER.finer( "Substitutions are: " + _mainSubstitutionList.toN3() );
          }

         if( LOGGER.isLoggable( Level.FINE ) ) {
            LOGGER.fine( "Selected goal: " + InfUtils.tripleToN3( _currentGoal, " ", false ) );
         }

         // check of builtins

         if( isCurrentGoalBuiltin( _currentGoal ) ) {
            return States.BUILTIN;
         }

         _alts = new Stack<Alternative>();

         // Unification with facts
         boolean factMatched = unifyF( _currentGoal );

         // Unification with rules
          boolean ruleMatched = false;
          if (!( factMatched && InfUtils.testGrounded(_currentGoal))){
                 // if the goal is grounded and has been confirmed by data
                 // no purpose of matching with rules
                 ruleMatched = _brules != null && unifyR( _currentGoal );
          }
         if( LOGGER.isLoggable( Level.FINER ) ) {
            LOGGER.finer( "Alts are: " + Alternative.altListToN3( _alts ) );
         }

         if( !factMatched && !ruleMatched ) {

            return States.FAILURE;

         } else {

            _currentNode.setAlternatives( _alts );
            _currentGoalUse.setOnHold();
            _currentGoalUse.setGoal( _currentGoal );

            if( _alts.size() > 1 ) {
               _alternativeStack.push( _currentNode );
               _currentNode.setSubstitutionListPointer( _mainSubstitutionList.size() );
               _currentNode.setGoallist( _goallist );
               _currentNode.setLogicsFlag( getFlag( LOGICS_FLAG ) );
            }

            _ruleLevel++;

            // set substituted goal here?
            //currentGoalUse.setGoal(currentGoal);
            return States.CHOOSE;
         }
      }
   }

   /**
    * procedure used by builtins to add alternatives to the alternative stack
    * @param pAlts
    */
   public void setAlternatives( Stack<Alternative> pAlts){
      _currentNode.setAlternatives( pAlts );
      _currentGoalUse.setOnHold();
      _currentGoalUse.setGoal( _currentGoal );

      if( pAlts.size() > 0 ) {
         _alternativeStack.push( _currentNode );
         _currentNode.setSubstitutionListPointer( _mainSubstitutionList.size() );
         _currentNode.setGoallist( _goallist );
         _currentNode.setLogicsFlag( getFlag( LOGICS_FLAG ) );
      }
      _alternateFlag = true;
   }

   protected void findStartJoinPoint() {
   }

   protected void findEndJoinPoint() {
   }

    /**
     * Searches for an alternative search path.
     * @return true if an alternative is found, false otherwise.
     */
   private boolean searchAlternative() {

      if( _alternativeStack.isEmpty() ) {
         return false;

      } else {

         _currentNode = _alternativeStack.peek();
         while( !_currentNode.hasMoreAlternatives() ) {

            if( getFlag( CLEAN_FLAG ) ) {
               // destroy this node
               _currentNode.setParent( null );
               _currentNode.clearChildren();
               _currentNode = null;
            }

            _alternativeStack.pop();

            if( _alternativeStack.isEmpty() ) {
               return false;
            }

            _currentNode = _alternativeStack.peek();
         }

         return true;
      }
   }

   private void saveResults() {
      _results.add( _mainSubstitutionList );

      saveResultsJoinPoint();
   }

   protected void saveResultsJoinPoint() {
   }

    /**
     * Checks whether the goal can match with rules from the 'generic' queries.
     * @param pGoal

     * @return boolean
     */
   protected boolean unifyRJoinPoint( Triple pGoal ) {
      return false;
   }

    /**
     * Tries to match a goal with all rules of the N3/OWL ruleset.
     * @param pGoal
     * @return true if new goals have been found, false otherwise.
     */
   private boolean unifyR( Triple pGoal ) {

      // The provided goal is matched against all available rules

      boolean result = false;

      if( !unifyRJoinPoint( pGoal ) ) {
         for( Rule rule : _brules ) {
            if( matchRule( rule, pGoal ) ) {
               result = true;
            }
         }

         return result;

      } else {

         return true;
      }
   }

    /**
     * Tries to match a goal with all rules of the N3/OWL ruleset.
     * Helper function.
     * @param pRule
     * @param pGoal
     * @return true is a match is found, false otherwise.
     */
   protected boolean matchRule( Rule pRule, Triple pGoal ) {

      if ( _cached){
         if ( InfUtils.testGrounded( pGoal ) ){
            Collection<Triple> set =  _cache.find( pGoal );
            if ( set != null && ! set.isEmpty()){
               return false;
            }
         }
      }

      if( getFlag( ANTILOOP_FLAG ) && hasBeenAppliedBefore( pRule, pGoal ) ) {
         return false;
      }
      List<Triple> lt = new ArrayList<Triple>( pRule.getConsequent().getTriples() );
      changeVariableLevel(lt);
      boolean result = false;
      for( Triple c : lt ) {

         _coll = new SubstitutionList( 5 );
         ruleUnificationJoinPoint();

         // If the goal matches the rule and it's not been applied before,
         // new goals may be derived
         SubstitutionResult res = Substitution.
               determineSubstitutions1( pGoal, c, _coll, _ruleLevel, true, getFlag( OCCURS_FLAG ) );

         if( res._result ) {

            if( LOGGER.isLoggable( Level.FINE ) ) {
               StringBuilder sb = new StringBuilder();
               sb.append( "Goal " );
               sb.append( InfUtils.tripleToN3( pGoal, " ", false ) );
               sb.append( " matches consequent in rule: " );
               sb.append( InfUtils.tripleToN3( pRule, " ", false ) );
               LOGGER.fine( sb.toString() );
            }

            // New goals are derived by applying substitutions to the
            // antecedents of the matched rule; the obtained goals constitute
            // a new inference step

            Alternative alt = new Alternative();

            List<Triple> tlist = new ArrayList<Triple>( pRule.getAntecedent().getTriples() );
            // need to change the level of some variables in the antecedents
            //  copy the triples
            changeVariableLevel( tlist );
            alt.setTriples( tlist );
            alt.setSubstitutions( res._substList );
            alt.setMatchingTriple( pGoal );
            alt.setMatchedTriple( pRule );
            alt.setFromRule();

            _alts.add( alt );

            result = true;
         }
      }
      return result;
   }

   protected void ruleUnificationJoinPoint() {
   }

    /**
     * tests whether a goal has been matched with a rule before.
     * When it is, a looping in the inferencing process is detected.
     * @param pRule
     * @param pGoal
     * @return true, if the goals had already been matched with this rule,
     *         false otherwise.
     */
   private boolean hasBeenAppliedBefore( Rule pRule, Triple pGoal ) {

      for( GoalUse gUse : _goallist.subList( 1, _goallist.size() ) ) {
         int num = gUse.getRuleNumber();
         if( gUse.testOnHold() && num != 0 && InfUtils.isEquivalentGoal( gUse.getGoal(), pGoal )
               && num == _ruleMap.get( pRule ) ) {
            if( LOGGER.isLoggable( Level.FINE )){
               LOGGER.fine(" Looping!!!");
            }
            if( LOGGER.isLoggable( Level.FINER ) ) {
               LOGGER.finer( "Looping!!! Rule " + InfUtils.tripleToN3( pRule, " ", false )
                     + " had previously been applied to " + InfUtils.tripleToN3( pGoal, " ", false ) );
            }
            return true;
         }

      }
      return false;
   }

    /**
     * Changes the variable level in a list of triples (and thus creating a
     * new set of variables).
     * @param pTriples
     * @return a list of triples.
     */
   private List<Triple> changeVariableLevel( List<Triple> pTriples ) {

      // set the level attribute of all variables to the current level
      //  copy the antecedents and substitute
      Element elem;
      MutablePattern pattern;
      Triple nt;
      for( int i = 0; i < pTriples.size(); i++ ) {

         nt = pTriples.get( i );
         pattern = new MutablePattern();

         for( TriplePos pos : TriplePos.values() ) {
            elem = nt.getElementAt( pos );
            elem = changeVariableLevel( elem );
            pattern.setCombination( pos, elem );
         }

         nt = pattern.freeze();
         pTriples.set( i, nt );
      }

      return pTriples;
   }

    /**
     * Changes the level of the variables contained in an element.
     * @param pElem
     *   @return the eventually changed element.
     */
   private Element changeVariableLevel( Element pElem ) {

      // set the level attribute of all variables to the current level
      //  copy the antecedents and substitute
      // the flag indicates a change in variables
      if( pElem.isElementContainer() ) {

         pElem = changeVariableLevel( pElem.asElementContainer() );

      } else if( pElem.isTripleSet() ) {

         pElem = new TripleSet( changeVariableLevel( pElem.asTripleSet().getTriples() ) );

      } else if( pElem.isVariable() ) {
         pElem = pElem.asVariable().copy( _ruleLevel );
      }

      return pElem;
   }

    /**
     * Changes the level of the variables in an element container.
     * @param pElem
     * @return the eventually changed container.
     */
   private Element changeVariableLevel( ElementContainer pElem ) {

      List<Element> l = pElem.asElementContainer().getElements();
      boolean vars = false;
      for( Element el : l ) {
         if( InfUtils.hasVariables( el ) ) {
            vars = true;
            break;
         }
      }

      if( vars ) {
         pElem = new AnonElementContainer( l, ContainerType.LIST );
      }

      Element el;
      Variable vari;
      for( int i1 = 0; i1 < l.size(); i1++ ) {

         el = l.get( i1 );

         if( el.isVariable() ) {

            vari = el.asVariable().copy( _ruleLevel );
            pElem = InfUtils.replaceInContainer( pElem.asElementContainer(), i1, vari );

         } else {
            el = changeVariableLevel( el );
            pElem = InfUtils.replaceInContainer( pElem.asElementContainer(), i1, el );
         }
      }
      return pElem;
   }

    /**
     * Matches a goal against all data triples of the RDF/N3/OWL database.
     * @param pGoal
     * @return true if a match is (matches are) found, false otherwise.
     */
   private boolean unifyF( Triple pGoal ) {
      // first search among newTriples if the goal is grounded
      // and set the noRulesFlag
      Collection<Triple> matches;
      TriplePattern pattern;

      if( InfUtils.hasAList( pGoal ) ) {
         pattern = InfUtils.getPattern( pGoal );
         matches = getFacts().find( pattern );

      } else {
         matches = getFacts().find( pGoal );
      }
      batchFactUnificationJoinPoint( matches );
      SubstitutionResult hasMatched;
      int nrOfMatches = 0;
      if( LOGGER.isLoggable( Level.FINE ) ) {
          LOGGER.fine( "Matched with data triple(s)" );
      }

      for( Triple match : matches ) {

         _coll = new SubstitutionList( 3 );
         hasMatched = Substitution.determineSubstitutions1( pGoal, match, _coll, 0, false, getFlag( OCCURS_FLAG ) );
         if( !hasMatched._result ) {
            continue;
         }
         nrOfMatches++;

         Alternative alt = new Alternative();
         alt.setSubstitutions( hasMatched._substList );
         if( getFlag( HISTORY_FLAG ) ) {
            alt.setMatchingTriple( pGoal );
            alt.setMatchedTriple( match );
         }
         _alts.add( alt );
      }

      return nrOfMatches != 0;
   }

   protected void batchFactUnificationJoinPoint( Collection<Triple> pMatches ) {
   }

    /**
     * Handles the special logic builtins: NOT, OR, EOR.
     * @return the enxts tate.
     */
   private States handleLogicBuiltins() {

      // search the special triple in the goallist
      boolean found = false;
      GoalUse gu = null;
      while( !found && _goallist.size() > 0 ) {
         gu = _goallist.remove( 0 );
         found = SWLog.isInstruction( gu.getGoal() );
      }

      States result;
      if( !found ) {

         setFlag( LOGICS_FLAG, false );
         result = States.FAILURE;

      } else {
         result = evaluateLOption(
               gu.getGoal().getObject().asElementContainer().getElements(), // Object list
               gu );
      }

      return result;
   }

    /**
     * Interpretes certain special builtin triples that were inserted in the
     * goallist to handle the special logic builtins: NOT, OR and EOR.
     * @param pElems
     * @param pGu
     * @return the next state.
     */
   private States evaluateLOption( List<Element> pElems, GoalUse pGu ) {

      States result = States.INFERENCE;
      switch( LOption.match( pElems.get( 0 ) ) ) {
         case END_EOR:
            // an endEor failure; we should check whether one tripleset has succeeded
            if( LOGGER.isLoggable( Level.FINE ) ) {
               LOGGER.fine( "Logic failure endEor - goal = " + pGu );
            }

            if( LOption.match( pElems.get( 2 ) ) == LOption.FALSE ) {
               setFlag( LOGICS_FLAG, false );
            }

            if( LOption.match( pElems.get( 3 ) ) != LOption.ONE ) {
               result = States.FAILURE;
            }
            break;

         case END_OR:
            // this is a failure of the or;
            // none of the triplesets is confirmed
            if( LOGGER.isLoggable( Level.FINE ) ) {
               LOGGER.fine( "Logic failure endOr - goal = " + pGu );
            }
            if( LOption.match( pElems.get( 1 ) ) == LOption.FALSE ) {
               setFlag( LOGICS_FLAG, false );
            }
            result = States.FAILURE;
            break;

         case EOR:
            // an eor failure should just be skipped
            if( LOGGER.isLoggable( Level.FINE ) ) {
               LOGGER.fine( "Logic failure eor - goal = " + pGu );
            }
            break;

         case NOT:

            if( LOGGER.isLoggable( Level.FINE ) ) {
               LOGGER.fine( "Logic failure not - goal = " + pGu );
            }

            int p = _altPointerStack.peek() ;
            int sp = _alternativeStack.size() ;
            GoallistNode gl;
            boolean done = false;
            while ( p < sp && sp > 0 ){
               gl = _alternativeStack.get( sp - 1 );
               if ( gl.hasMoreAlternatives()){
                  result = States.FAILURE;
                  done = true;
                  break;
               }
               sp--;
            }

            if ( ! done){
               if( LOption.match( pElems.get( 1 ) ) == LOption.FALSE ) {
                  setFlag( LOGICS_FLAG, false );
               }
               _altPointerStack.pop();
            }

            break;

         case CUT:

            if( LOGGER.isLoggable( Level.FINE ) ) {
               LOGGER.fine( "Logic failure cut - goal = " + pGu );
            }

            p = _altPointerStack.peek() ;
            sp = _alternativeStack.size() ;

            done = false;
            while ( p < sp && sp > 0 ){
               gl = _alternativeStack.get( sp - 1 );
               if ( gl.hasMoreAlternatives()){
                  done = true;
                  break;
               }
               sp--;
            }

            if ( ! done){

               if( LOption.match( pElems.get( 1 ) ) == LOption.FALSE ) {
                  setFlag( LOGICS_FLAG, false );
               }
               _altPointerStack.pop();
            }
            result = States.FAILURE;

            break;

         case OR:
            if( LOGGER.isLoggable( Level.FINE ) ) {
               LOGGER.fine( "Logic failure or - goal = " + pGu );
            }

            break;
      }

      return result;
   }

    /**
     * Throws an IllegalStateException if the model contains no
     * data triples.
     */
   private void checkDB(){
      if (getRuleSource() == null){
         if (getFacts() == null){
            throw new IllegalStateException("I cannot reason without facts!");
         }else{
            _brules = new ArrayList<Rule>();
         }
      }
   }

   private List<Triple> clearLogSequence(Collection<Triple> pQuery){
       List<Triple> queryOut = new ArrayList<Triple>(pQuery.size());
       for (Triple t: pQuery){
           if (t.getPredicate().equals(SW.SEQUENCE)){
               if (! t.getObject().isTripleSet()){
                   throw new IllegalArgumentException("The object of " + SW.SEQUENCE +
                   " must be a tripleset:\n" +t + "\n");
               }
               for (Triple t1: t.getObject().asTripleSet().getTriples()){
                   queryOut.add(t1);
               }
           }else{
               queryOut.add(t);
           }
       }
       return queryOut;
   }

    /**
     * Gives all rules of the model a number.
     */
   protected void numberRules() {

      for( Rule r : _brules ) {
         _ruleMap.put( r, _ruleCnt );
         _ruleCnt++;
      }
   }


   //
   // (Private methods)
   //
   /////////////////////////////////////////////////////////////////////////////
}
