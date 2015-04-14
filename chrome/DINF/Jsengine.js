/* inference engine lightInf
 * finite state machine
 * as described in: www.agfa.com/w3c/2002/02/thesis/thesis.pdf: p.77 - 85
 * Author: Guido J.M. Naudts Bouwel
 */
/**
 * This class implements a backward reasoning engine.
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

//var notEqualTo = "log:notEqualTo";

function inference(inf){
        var sols;
        var list;
        var state;
        // create an engine manager
        // serves for managing different modalities for the engine
        // manager = new EngineManager();
        // generally the infData object contains all data necessary for
        // inferencing like the RDF Graph, inferencing parameters, tracing data etc...
        //
        var state = "inf"; // state = inferencing; the start state
        var triple;
        var uri;
        var counter = 0;
       // handle the inferencing parameters
       // these are parameters directing the engine
       // for the moment not necessary?
       // handleParamTriples(inf)
        // eventually start the timer
        var time1 = myClock();
    //writeln("db: " + inf.dslist[0].ts);
    //writeln("Stack:::: "); printArray(inf.stack);
        testVerbose("GOALLIST: " + arrayToString( inf.goallist) + "\n");
    if (inf.triples == undefined || inf.triples == []){    // get all triples now
           inf.triples = [];
           for (var i1 = 0; i1 < inf.graphs.length; i1++){
              graph = inf.graphs[i1].ts;
              for (var i2 = 0; i2 < graph.length; i2 ++){
                   triple = graph[i2];
                   if (triple.getType() != "r")
                        inf.triples.push(triple);
              }
          }
     }
     // temporary array for storing new grounded triples
     inf.cache = [];
     if (! inf.nobuiltins){
         checkContradictionsB(inf);
     }
     inf.maxSteps = 0;
     inf.unSteps = 0;
     //inf.nooutput = false;
     //inf.verbose = true;
     makePropertyDictI(inf);
     //writeln("Backward.inference triples from propertyDictM: " + getAllTriplesM(inf));
     //writeln(propertyDictMToString(inf));
        // finite state loop
        while (inf.state != "endinf"){

            counter++;
            if (inf.maxSteps > 0 && counter > inf.maxSteps){
                writeln(inf, "Stopped at maxSteps: " + inf.maxSteps);
                testVerbose(inf, "Stopped at maxSteps: " + inf.maxSteps);
                inf.state = "endinf";
                break;
            }
            // if the verbose flag is set give output
            testVerbose(inf,  " state ===== " + inf.state + "\n");
            // a solution has been found
            state = inf.state;
            if (state == "solution"){
                // show the solution
                testVerbose(inf, showsol( inf.sols[inf.sols.length-1], inf));
                // only one solution? Then stop.
                if (inf.onesol == 1)
                     inf.state = "endinf";
               else
                     // try to find other solutions
                     backtrack(inf);
            }
            else if (state == "backtracked"){
                // a backtrack was done

                testVerbose(inf, "A backtrack has been done.\n");
                // print("matchlist after backtrack: " +inf.matchlist);
                //  go and choose new goals
                choose(inf);
            }
            else if (state == "failure"){
                // this was a dead path; backtrack and try again
                testVerbose(inf, "Failure path done.\n");
                backtrack(inf);
            }
            // main state
            else{
               var ret;
                //testVerbose(inf,"Stack: ");
                //testVerbose(inf,  arrayToString(inf.stack));
               if (inf.goallist.length != 0){
                  // check whether the next predicate is a builtin
                  // testVerbose(inf,"Substitutionlist: " + inf.subst);

                  triple = inf.goallist[0];
                   //writeln("Jsengine.inference triple == " + triple + " ");


                  var triple1 = applySubstitutionListToTriple(inf.subst, copyTriple(triple));
                 //print("triple1 Jsengine " + triple1);
                   //writeln("INF.TRIPLES " + inf.triples);
                  var ret = 0;
                  if (! inf.nobuiltins){
                     ret = checkBuiltins(inf, triple1);
                  // print("builtins ret = " + ret + "\n");
                  }
                }
                if (ret == 0){
                      // display the list of goals
                      testVerbose(inf, "Goallist:\n" + triplesetToString(inf.goallist) + "\n");
                      // display the current substitution
                      testVerbose(inf, "Current Substitutions:\n"
                          + inf.subst + "\n");
                      //print("inf.sols    "+inf.sols + "\n");
                      solve(inf);
                      state = inf.state;
                }
            }
        }
        if (inf.state == "endinf"){
             var time2 = myClock();
            // inf.infTime = time2 - time1;
            sols = inf.sols;
            showsols(sols,inf);
            if(inf.abort){
                 s = "Reasoning was aborted because a contradiction happened:\n" +
                     inf.contradiction + "\n";
                 testNooutput(inf, s);
            }else{

	           if (sols == []){
                  testNooutput(inf,  "There were no solutions found.\n");
               }else {
                  //testNooutput(inf, showsols(sols, inf));
               }
            }
        }

              testNooutput(inf, "Starting time BW: "  + time1 + "\n");
              testNooutput(inf, "Ending time BW: "  + time2 + "\n");
              testNooutput( inf, "Unifications steps: " + inf.unSteps);
              testNooutput(inf, "Unifications: " + inf.unifs);
//            print "Unifications/sec : ",inf.unifs/inf.infTime;
              testNooutput(inf, "Number of solutions: "
                              + inf.solnr + "\n");
}

function testVerbose(inf, s){
   if (inf.verbose > 0)
         print( s + "\n");
}

function testNooutput(inf, s){
   if (inf.nooutput == 0)
         print( s + "\n");
}


function getsol(sol, inf){
    //writeln("Jsengine.getsol query = " + inf.query);
    //writeln("Jsengine.getsol sol = " + sol);
    // inf.subst is a list of substitutions;
        // each substitution represents a solution when
        // applied to the query
        // print("sol: " + sol + "\n");
        if (sol == null){
          return;
        }
        var q = [];
        var tr;
        for (var i = 0; i < inf.query.length; i++){
            tr = inf.query[i];

            if (tr.getProperty().getUri() != prefixPredicate.getUri()){
                 q.push(copyTriple(inf.query[i]));
            }
        }
        //writeln("Jsengine.getsol solution = " + applySubstitutionListToTripleSet(sol, q));
        return applySubstitutionListToTripleSet(sol, q);
}

function showsol(sol, inf){
    return triplesetToString(getsol(sol,inf)) + "\n";
}

function showsols(sols, inf){
    //writeln("Jsengine.showsols sols = " + sols);
    var s = "\nSolutions:\n\n";
    var solbuf = []; 
    var solbuf1;
    for (var i = 0; i < sols.length; i++)
       solbuf.push(getsol(sols[i], inf));
    solbuf = elimDoubleTriplesets(solbuf);
    inf.solbuf = solbuf;
    for (var i = 0; i < solbuf.length; i++) 
       s = s + triplesetToString(solbuf[i])+ "\n";
    inf.solnr = solbuf.length;
    return s; 
}

