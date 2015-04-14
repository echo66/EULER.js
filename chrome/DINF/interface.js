/** simulated interface functions
  * Author: Guido J.M. Naudts Bouwel
  */

var log = "http://www.w3.org/2000/10/swap/log#";
var variables = "proctest#variables";

// a global prefix dictionary who collects all prefixes
// of an application
var globalPrefixes = [];

function triple(subject, property, object){
   this.subject = new resource(subject);
   this.property = new resource(property);
   this.object = new resource(object);
   this.toString = function(){
     return this.subject.toString() + " " +  this.property.toString()
             + " " + this.object.toString() + ". ";
   };
    this.prettyOut = function(){
      return this.subject.prettyOut() + " " +  this.property.prettyOut()
              + " " + this.object.prettyOut() + ". ";
    };

   this.getType = function(){

     return "t";
   };
   this.getSubject = function(){
       return this.subject;
   };
   this.getProperty = function(){
       return this.property;
   };
   this.getObject = function(){
       return this.object;
   };
   this.setSubject = function(subject){
       this.subject = subject;;
   };
   this.setProperty = function(property){
       this.property = property;
   };
   this.setObject = function(object){
        this.object = object;
   };
    var s = checkResource(this.subject, this.property, this.object);
    if (s != undefined){
        writeln("Triple --- error --- : " + this.toString() + "\n" + s);
    }

}

function cTriple(subject, property, object){
   /* complex triple: subject, property and object are resources or cResources */
   this.subject = subject;
   this.property = property;
   this.object = object;

   this.toString = function(){
     return this.subject.toString() + " " +  this.property.toString()
             + " " + this.object.toString() + ". ";
   };
   this.prettyOut = function(){
     return this.subject.prettyOut() + " " +  this.property.prettyOut()
             + " " + this.object.prettyOut() + ". ";
   };

   this.getType = function(){
     return "ct";
   };
   this.getSubject = function(){
       return this.subject;
   };
   this.getProperty = function(){
       return this.property;
   };
   this.getObject = function(){
       return this.object;
   };
   this.setSubject = function(subject){
       this.subject = subject;;
   };
   this.setProperty = function(property){
       this.property = property;
   };
   this.setObject = function(object){
        this.object = object;
   };
    var s = checkResource(this.subject, this.property, this.object);
    if (s != undefined){
                writeln("Triple --- error --- : " + this.toString() + "\n" + s);
    }

}

function triplesetPrettyOut(tripleset){
    var s = "";
    for (var i = 0; i < tripleset.length; i++){
        if ( tripleset[i] instanceof triple || tripleset[i] instanceof cTriple){
            s = s +  tripleset[i].prettyOut();
        }else{
            s = s + tripleset[i];
        }
    }
    return s;
}

function rule(ants, cons){
   this.ants = ants;
   this.cons = cons;
   this.toString = function(){
        return  "{" + triplesetToString(this.ants) + "} => {" + triplesetToString(this.cons) + "}.";
   };
   this.getType = function(){
     return "r";
   };
   this.getAntecedents = function(){
      return this.ants;
   };
   this.setAntecedents = function(ants){
      this.ants = ants;
   };
   this.getConsequents = function(){
      return this.cons;
   }
   this.setConsequents = function(cons){
      this.cons = cons;
   };
   this.getProperty = function(){
      return this.cons[0].getProperty();
   };
}

function makeLiteral(sin){
   var res = new resource(sin);
   res.constant = 1;
   return res;
}


function resource(res){
   this.res = res;
   this.uri = res;
   this.simple = 1;
   this.RDFList = [];
   this.list = false;
   this.constant = 0;
   this.testVar = function(){

       if (this.nr < 0){
           //writeMessage("testVar res = " + this.uri + "\n");
           return true;
       }
       if (this.uri == undefined || this.uri.toString() == "" )
           return false;
       if (this.uri.toString().substring(0,1) == "?")
           return true;
       if (this.uri.length > 2 && this.uri.toString().substring(0,2) == "_:")
           return true;
       // print("testVar nr = " + this.nr + "\n");
       return 0;
   };
   this.toString = function(){
       // toString gives the standard full notation <http://....>
       if (this.list){
          var s = "(";
          for (var i = 0; i < this.RDFList.length; i++)
              s = s + this.RDFList[i].toString() + " ";
          s = s.substring(0, s.length -1) + ")";
          return s;
       }
       if (this.simple == 0){
          var s = "{";
          for (var i = 0; i < this.set.length; i++)
               s = s + this.set[i].toString();
          return s + "}\n";
       }
       if (this.level == null ){
          if (this.constant > 0){
              return this.getUri();
          }else{
              if (this.testVar()){
                  return this.getUri();
              }
              return "<" + this.getUri() + ">";
          }

       }
       return this.getUri() + "_" + this.level;
   };

   this.prettyOut = function(){
       if (this.list){
          var s = "(";
          for (var i = 0; i < this.RDFList.length; i++)
              s = s + this.RDFList[i].toString() + " ";
          s = s.substring(0, s.length -1) + ")";
          return s;
       }
       if (this.simple == 0){
          var s = "{";
          for (var i = 0; i < this.set.length; i++)
               s = s + this.set[i].toString();
          return s + "}\n";
       }
       if (this.constant > 0){
            return this.getUri();
       }

       if (this.level == null){
          // get the part before # with the #
          var s = this.getUri();
          var s1, s2;
          var i = s.indexOf("#");
          if ( i >= 0){
              s1 = s.substring(0, i+1);
              s2 = s.substring(i+1);
              if (globalPrefixes[s1] != undefined){
                  s = globalPrefixes[s1] + s2;
                  return s;
              }
          }
           if (this.testVar()){
               return this.getUri();
           }

          return "<" + this.getUri() + ">";

       }

       return this.getUri() + "_" + this.level;

   }
   this.getUri = function(){
       if (this.uri == undefined || this.uri.toString() == "")
          return this.label;
       return  this.uri;
   };
   this.getType = function() {
       if ( this.list ){
           return "lr";
       }
       if (this.constant == 1)
          return "lt";
       return "sr";   // "r" is used for rules; sr = simple resource
   }
}


function cResource(set){
   // a complex resource contains a tripleset
   // cannot be a variable
   this.set = set;
   this.toString = function(){
       var s = "{";
       for (var i = 0; i < this.set.length; i++)
          s = s + this.set[i].toString();
       s = s + "}";
       return s;
   };
   this.getSet = function(){
       return this.set;
   };
   this.getType = function(){
       return "cr";
   }
    this.testVar = function(){
        return 0;
    }

}

function print (str) {
      document.getElementById("resultsText").value += str;
}


function db(ts){
   this.ts = ts;
   this.dict = [];
   this.getPropertyExtension = function(prop){
       var t;
       var list = [];
       for (var i = 0; i <  this.ts.length; i++){
          t = this.ts[i];
          if (t.getType() == "r"){
             for (var i1 = 0; i1 < t.cons.length; i1++){
                if (prop.uri == t.cons[i1].getProperty().uri){
                    list.push(t);
                    break;
                }
             }
          }else{
             prop1 = t.getProperty();
             if (prop1.uri == prop.uri)
                list.push(t);
          }
       }
       return list;
   };
   this.makePropertyDict = function(){
      var prop;
      var t;
       for (var i = 0; i <  this.ts.length; i++){
          t = this.ts[i];
          if (t.getType() == "r"){
             //print("rule = " + t + "\n");
             for (var i1 = 0; i1 < t.cons.length; i1++){
                prop = t.cons[i1].getProperty().uri;
                //print("prop = " + prop + "\n");
                if (this.dict[prop] == undefined)
                   this.dict[prop] = [t];
                else
                   this.dict[prop].push(t);
             }
          }else{
             prop = t.getProperty().uri;
                if (this.dict[prop] == undefined)
                   this.dict[prop] = [t];
                else
                   this.dict[prop].push(t);
          }
       }
    };
    this.toString = function(){
        return this.ts.toString();
    };
}

function infData(dslist){
    /* define an infData object */
    // dslist is the list of the RDF datasources;
    // the last entry is the query
    this.nr = 0;
    this.dslist = dslist;
    if (this.dslist.length > 0){
        this.graphs = subArray(this.dslist, 0, this.dslist.length-1);
        this.goallist = this.dslist[this.dslist.length-1].ts;
    }
    this.query = [];

    this.initinf = function(){
       // give all triples a number and initialize
       // the level in variables
       var nr = 1;
        var nr1;
        var sub;
        var prop;
        var obj;
        this.dict = [];
        var t;
        var flag = 0;
        for (var i = 0; i <  this.dslist.length; i++) {
           var g = this.dslist[i];
           for (var i1 = 0; i1 < g.ts.length; i1++){
              t = g.ts[i1];
              // print("triple " + t.toString() + "\n");
              t.nr = nr++;
              // renameTriple(t, 0, 1);
              /* all uris recieve a unique number.
                A dictionary is kept for keeping numbers unique
              */
              if (t.getType() == "r"){
                 var a = 1;
                 /* var ants = t.getAntecedents();
                  for (var i2 =0; i2 < ants.length; i2++){
                        this.numberTriple(this.dict, ants[i2]);
                  }
                  var seqs = t.getConsequents();
                  for (var i2 =0; i2< seqs.length; i2++){
                        this.numberTriple(this.dict, seqs[i2]);
                  }*/
              }else{
                 this.proclist = [];
                 uri = t.getProperty().uri;
                 if (uri == variables){
                    //print("!!!!!!!!!!!!!!!!!variables\n");
                    // this defines the list of variables for a procedure call
                    // check whether the proc has already been defined
                    var procName = t.getSubject().uri;
                    var procparams;
                    try{
                        procparams = this.proclist[procName];
                        procparams[0] = t.getObject().RDFList;
                    }catch(e){
                        this.proclist[procName] = [t.getObject().RDFList, [], []];
                    }
                  }
                  else if (uri == proc){
                    //print("!!!!!!!!!!!!!!!!!proc\n");
                     // this is the tripleset belonging to a procedure
                     var procName = t.getSubject().uri;
                     var procparams;
                     try{
                        procparams = this.proclist[procName];
                        procparams[1] = t.getObject().set;
                     }catch(e){
                        this.proclist[procName] = [[], t.getObject().set, []];
                     }
                  }
                  else if (uri == query){
                    //print("!!!!!!!!!!!!!!!!!query\n");
                     // this is the query belonging to a procedure
                     var procName = t.getSubject().uri;
                     var procparams;
                     try{
                        procparams = this.proclist[procName];
                        procparams[2] = t.getObject().set;
                     }catch(e){
                        this.proclist[procName] = [[], [], t.getObject().set];
                     }
                  }//else{
                   //  this.numberTriple(this.dict, t);
                  //}
              }
           }
        }
       for (var i = 0; i <  this.goallist.length; i++) {
           this.query.push(copyTriple(this.goallist[i]));
       }
       //makePropertyDictI(this);
     };

    this.initinf1 = function(nr){
       // give all triples a number
        var t;
        this.proclist = [];
        /*if ( this.nodict != true){
            if (this.propertyDictD == undefined || this.propertyDictM == undefined){
                writeln("nodict: " + this.nodict);
                makePropertyDictI(this);
            }
        } */
        for (var i = 0; i <  this.dslist.length; i++) {
           var g = this.dslist[i];
           for (var i1 = 0; i1 < g.ts.length; i1++){
              t = g.ts[i1];
              // print("triple " + t.toString() + "\n");
                uri = t.getProperty().uri;
                 if (uri == variables){
                    //print("!!!!!!!!!!!!!!!!!variables\n");
                    // this defines the list of variables for a procedure call
                    // check whether the proc has already been defined
                    var procName = t.getSubject().uri;
                    var procparams;
                    try{
                        procparams = this.proclist[procName];
                        procparams[0] = t.getObject().RDFList;
                    }catch(e){
                        this.proclist[procName] = [t.getObject().RDFList, [], []];
                    }
                  }
                  else if (uri == proc){
                    //print("!!!!!!!!!!!!!!!!!proc\n");
                     // this is the tripleset belonging to a procedure
                     var procName = t.getSubject().uri;
                     var procparams;
                     try{
                        procparams = this.proclist[procName];
                        procparams[1] = t.getObject().set;
                     }catch(e){
                        this.proclist[procName] = [[], t.getObject().set, []];
                     }
                  }
                  else if (uri == query){
                    //print("!!!!!!!!!!!!!!!!!query\n");
                     // this is the query belonging to a procedure
                     // special query operations by parser are not done yet!!
                     var procName = t.getSubject().uri;
                     var procparams;
                     var set = t.getObject().set;
                     //checkForQueryVariables(set);
                     try{
                        procparams = this.proclist[procName];
                        procparams[2] = set;
                     }catch(e){
                        this.proclist[procName] = [[], [], set];
                     }
                  }else{
                      t.nr = nr++;
                  }
           }
        }
     return nr;
     };


     this.graphsToString = function(){
         s = "";
         for (var i = 0; i < this.graphs.length; i++)
            s = s + "Graph: " + i + "\n" +
                        triplesetToString(this.graphs[i].ts);
         return s + "\n";
     };
     this.propertyDictR;
     this.propertyDictM;
     this.path = [];
     this.subst = [];
     this.unifs = 0;
     this.unSteps = 0;
     this.verbose = 0;
     this.nooutput = 0;
     this.maxSteps = -1;
     this.state = "inf";
     this.matchlist = [];
     this.level = 0;
     this.oneSol = 0;
     this.interactive = 0;
     this.stack = [];
     this.sols = [];
     this.resdic = [];
     this.currRes = 0;
     this.anonCounter = 0;
     this.locCounter = 0;
     this.existCounter = 0;
     this.listCounter = 0;
     this.ruleNr = 0;
     this.dict = [];
     this.goallistSav = [];
     this.querySav = [];

     this.abort = false;
     this.newTriples = [];

     this.reinit = function(){
         this.propertyDictR;
         this.propertyDictM;
         this.path = [];
         this.subst = [];
         this.unifs = 0;
         this.unSteps = 0;
         this.verbose = 0;
         this.nooutput = 0;
         this.maxSteps = 100;
         this.state = "inf";
         this.matchlist = [];
         this.level = 0;
         this.oneSol = 0;
         this.interactive = 0;
         this.stack = [];
         this.sols = [];
         this.resdic = [];
         this.currRes = 0;
         this.anonCounter = 0;
         this.locCounter = 0;
         this.existCounter = 0;
         this.listCounter = 0;
         this.ruleNr = 0;
         this.dict = [];
         this.goallist = this.goallistSav;
         this.query = this.querySav;

         this.newTriples = [];
         this.abort = false;
     };
}


var ruleprefix = "urn:clerk:anon#Rule";
var forall = "http://www.w3.org/2000/10/swap/log#forAll";
var first = "http://www.w3.org/1999/02/22-rdf-syntax-ns#first";
var restLi = "http://www.w3.org/1999/02/22-rdf-syntax-ns#rest";
var nilst = "http://www.w3.org/1999/02/22-rdf-syntax-ns#nil";
var subjectRDF = "http://www.w3.org/1999/02/22-rdf-syntax-ns#subject";
var predicateRDF = "http://www.w3.org/1999/02/22-rdf-syntax-ns#predicate";
var objectRDF = "http://www.w3.org/1999/02/22-rdf-syntax-ns#object";
var implies = "http://www.w3.org/2000/10/swap/log#implies";

function infData1(path, files){
   /** Returns an infData object from a list of filenames
     * Path is the native path for the files
     */
     //print("files = " + files + "\n");
     //print("path = " + path + "\n");
     var dslist = [];
     var queryFlag = 0;
     var n3Parser = new N3EParser();
     var objects = [];
     var ret;
     var dbi = null;
     var inf = new infData([]);
     for (var i = 0; i < files.length; i++){
        n3Parser.init();
        if (i == files.length - 1){
              queryFlag = 1;
              n3Parser.queryFlag = 1;
        }
        ret = getRDFDB(path, files[i], inf, n3Parser);
        inf = ret[1];
        //print("ret = " + ret + "\n");
        dbi = new db(ret[0]);
        dbi.makePropertyDict();
        //print("dbi dict = " + dbi + "\n");
        inf.dslist.push(dbi);
    }
    if (inf.dslist.length > 0){
        inf.graphs = subArray(inf.dslist, 0, inf.dslist.length-1);
        inf.goallist = inf.dslist[inf.dslist.length-1].ts;
    }
    for (var i = 0; i <  inf.goallist.length; i++) {
           inf.query.push(copyTriple(inf.goallist[i]));
           inf.goallistSav.push(copyTriple(inf.goallist[i]));
           inf.querySav.push(copyTriple(inf.goallist[i]));
    }
    inf.initinf1(0);

    return inf;

}

/**
  * if reasoner = "b" (backward) rules must be returned;
  * if reasoner = "f" (forward) no rules must be returned
  */
function getMatching( goal, inf, reasoner){
    if ( inf.matchingMechanism == "D"){
        return getMatchingD( goal, inf, reasoner );
    }else{
        return getMatchingM( goal, inf, reasoner );
    }

}

function getMatchingD( goal, inf, reasoner){
       /* getmatching gets all statements with a property
           matching with the goal
           graphs contains the RDF datastores
        */

        // initialize the list
        var mli = [];
        //writeln("interface.getMatchingR goal:  " + goal)
        // get the property
        var pr = goal.getProperty();
        //writeln("interface.getMatchingR predicate = "  + pr +
        //        " matching: " + inf.predicateDict[pr]);
         // for each db add the relevant triples
        if( inf.predicateDict[pr] != undefined){
            mli = mli.concat(inf.predicateDict[pr]);
        }
        if ( reasoner == "f"){
            var mlc = [];

            for (var k = 0; k < mli.length; k++){
                if (mli[k] != undefined && mli[k].getType() != "r"){
                    mlc.push(mli[k]);
                }
            }
            return mlc;
        }
        return mli;
}

function propertyDictMToString(inf){
    s = "";
    s = nodeToString(inf.propertyDictM, s);
    return s;
}


function getAllTriplesM(inf){
    ml = [];
    getAllTriplesMH(inf.propertyDictM, ml);
    return ml;
}

function getAllTriplesMH(node, ml){
    if (! node.isLeaf()){
        for ( var ch in node.children){
           getAllTriplesMH(node.children[ch], ml);
        }
    }else{
        ml.push(node.triple);
    }
}


function nodeToString(node, s){
    s = node.toString() + "/" ;
    for ( var ch in node.children){
       s = s + nodeToString(node.children[ch], s);
    }
    return s;
}

  /**
    * get matching triples with multiple hashes
    * first hash of property, second of subject, third of object
    * Rules: all variables are considered equal .
    */
function getMatchingM(goal, inf, reasoner){
    // initialize the list
    var mli = [];
    //writeln("\ninterface.getMatchingM goal: " + goal + "\n");
    var property = goal.getProperty();
    var subject = goal.getSubject();
    var object = goal.getObject();
    var root = inf.propertyDictM;
    // if property is variable get all children
    if (property.testVar()){
        for (var child in root.children){
            getLeafsP(root.children[child], subject, object, mli);
        }
    }else{
        getLeafsP(root.children[property.toString()], subject, object, mli);
        getLeafsP(root.children["var"], subject, object, mli);
    }
    if ( reasoner == "f"){
        var mlc = [];

        for (var k = 0; k < mli.length; k++){
            if (mli[k] != undefined &&  mli[k].getType() != "r"){
                mlc.push(mli[k]);
            }
        }
        return mlc;
    }

    return mli;
}

function getLeafsP( pnode, subject, object, mli ){
    if (pnode != undefined){
        //writeln("pnode: " + pnode + " children: " + mapToString(pnode.children));
        if (subject.testVar()){
            for (var child in pnode.children){
                getLeafsS(pnode.children[child], object, mli);
            }
        }else{
            if( subject.getType() == "lr" ){
                // handle lists
                for (var child in pnode.children){
                    if (pnode.children[child] == "L$$$" ){
                          //if (matchResources(subject, pnode.children[child])){
                              getLeafsS(pnode.children[child], object, mli);
                          //}
                    }
                }
            }else if( subject.getType() == "cr" ){
                    // handle sets a
                    for (var child in pnode.children){
                        if (pnode.children[child] == "S$$$" ){
                              //if (matchResources(subject, pnode.children[child])){
                                  getLeafsS(pnode.children[child], object, mli);
                              //}
                        }
                    }

            }else{
                getLeafsS(pnode.children[subject.toString()], object, mli);
            }
            getLeafsS(pnode.children["var"], object, mli);
        }
    }
}

function getLeafsS( snode,  object, mli ){
    if (snode != undefined){
        //writeln("snode: " + snode + " children: " + mapToString(snode.children) );
        if (object.testVar()){
            for (var child in snode.children){
                getLeafsO(snode.children[child], mli);
            }
        }else{
            if( object.getType() == "lr" ){
                // handle lists

                for (var child in snode.children){
                    if (snode.children[child] == "L$$$" ){
                          //if (matchResources(object, pnode.children[child].RDFList)){
                              getLeafsO(snode.children[child],  mli);
                          //}
                    }
                }
            }else if( object.getType() == "cr"){
                    // handle sets
                    for (var child in snode.children){
                        if (snode.children[child] == "L$$$" ){
                              //if (matchResources(object, pnode.children[child].set)){
                                  getLeafsO(snode.children[child],  mli);
                              //}
                        }
                    }

            }else{

                getLeafsO(snode.children[object.toString()], mli);
            }
            getLeafsO(snode.children["var"],  mli);
        }
    }
}

function getLeafsO( onode,  mli ){
    if (onode != undefined){
        //writeln("onode: " + onode.resource.toString());
        for (var key in onode.children){
            //writeln("onode children: " + onode.children[key].triple)
            mli.push(onode.children[key].triple);
         }
    }
}

function matchResources(res1, res2){
    if (res1.testVar()){
        return true;
    }
    if (res2.testVar()){
        return true;
    };
    if (res1.getType() == "lr"){
        if ( ! res2.getType() == "lr"){
            return false;
        }
        for (var i = 0; i <res1.RDFList.length; i++){
            if (res1.RDFList[i] != res2.RDFList[i]){
                return false;
            }
        }
        return true;
    }
    if (res1.getType() == "cr"){
        if ( ! res2.getType() == "cr"){
            return false;
        }
        if (res1.set.length != res2.set.length){
            return false;
        }
        for (var i = 0; i <res1.set.length; i++){
            if (! tripleInList(res1.set[i], res2.set)){
                return false;
            }
        }
        return true;
    }
    if (res1.toString() != res2.toString()){
        return false;
    }
    return true;

}

function makePropertyDictI(inf){
    if ( inf.matchingMechanism == "D"){
        if (inf.predicateDict == undefined){
            makePropertyDictD( inf );
        }
    }else{
        if (inf.propertyDictM == undefined){
            makePropertyDictM(  inf );
        }
    }

}

/** make a dictionary with as key the predicate and as value the triples
  * store variable triples under key "variable"
  * during execution got to add the new triples
  */

function makePropertyDictD( inf){
        var ts;
        inf.predicateDict = [];
        var predicateDict = inf.predicateDict;
         // for each db add the relevant triples
        for (var n = 0; n < inf.graphs.length; n++){
            ts = inf.graphs[n].ts;
            for (var i = 0; i < ts.length; i++){
               addTripleToPropertyDictD( ts[i], inf);
            }
        }
         //for( var key in predicateDict){
         //   writeln("interface.makePropertyDict Key: " + key + " triples " + predicateDict[key]);
         //}


}

/**
  * Tree for fast finding of triples and rules matching with a goal
  */
function TNode ( resourceIn ){
    this.resource = resourceIn;
    this.children = [];
    this.previousNode;
    this.triple; // triples are in leafNodes

    this.addNode = function( resourceIn ){
        if (resourceIn == undefined){
            resourceIn = "null";
        }

        if (this.children[resourceIn.toString()] != undefined){
            return this.children[resourceIn.toString()];
        }
        var newNode = new TNode(resourceIn);
        newNode.previousNode = this;
        //writeln("resourceIn: " + resourceIn);
        this.children[resourceIn.toString()] = newNode;
        return newNode;
    };

    this.isLeaf = function(){
        return this.triple != undefined;
    };

    this.toString = function(){
        if (this.triple != undefined){
            return this.triple.toString();
        }else if (this.resource != undefined){
            return this.resource.toString();
        }else{
            return "null";
        }
    };
}


/**
  * PropertyDictM is not really a dictionary (the name is historical) but a tree made of TNodes
  */

function makePropertyDictM( inf ){
    // create the root node with a resource null
    inf.propertyDictM = new TNode("root");
    var tripleO;
    for (var n = 0; n < inf.graphs.length; n++){
        ts = inf.graphs[n].ts;
        for (var i = 0; i < ts.length; i++){
            if (ts[i].getType() == "r"){
                for (var k = 0; k < ts[i].getConsequents().length; k++){
                    tripleO = ts[i].getConsequents()[k];
                    addTripleToPropertyDictM(tripleO, inf.propertyDictM, ts[i]);
                }

            }else{
                addTripleToPropertyDictM(ts[i], inf.propertyDictM, null);
            }

        }
     }
//printPropertyDictM(inf);
}

function addTripleToPropertyDictM(triple, root, rule){

        //writeln("interface.addTripleToPropertyDictM adding triple to propertydict: " + triple);
        if (triple == undefined){
           // return;
        }
        var property = triple.getProperty();
        var subject = triple.getSubject();
        var object = triple.getObject();
        if (property.testVar()){
             node1 = root.addNode("var");
        }else{
             node1 = root.addNode(property.toString());
        }
    if (subject.testVar()){
         node2 = node1.addNode("var");
    }else if(subject.getType() == "cr"){
        // S stands for set
        node2 = node1.addNode("S$$$");
        node2.set = subject.set;
    }else if(subject.getType() == "lr"){
        // L stands for list
        node2 = node1.addNode("L$$$");
        node2.RDFList = subject.RDFList;

    }else{
         node2 = node1.addNode(subject.toString());
    }
    if (object.testVar()){
         node3 = node2.addNode("var");
    }else if(object.getType() == "cr"){
        // S stands for set
        node3 = node2.addNode("S$$$");
        node3.set = object.set;
    }else if(object.getType() == "lr"){
        // L stands for list
        node3 = node2.addNode("L$$$");
        node3.RDFList = object.RDFList;
    }else{
         node3 = node2.addNode(object.toString());
    }
    node4 = node3.addNode(triple.toString());
    if ( rule == null){
        node4 = node3.addNode(triple.toString());
        node4.triple = triple;
    }else{
        node4 = node3.addNode(rule.toString());
        node4.triple = rule;
    }

}

function addTripleToPropertyDictD( triple, inf ){
    if ( triple.getType() == "r"){
         // a rule must be entered with the properties of the consequent
         for ( var k = 0; k < triple.getConsequents().length; k++ ){
             var tr = triple.getConsequents()[k];
             if (inf.predicateDict[tr.getProperty()] == undefined){
                 inf.predicateDict[tr.getProperty()] = [triple];
             }else{
                  inf.predicateDict[tr.getProperty()].push(triple);
             }

         }
    }else{
        if (inf.predicateDict[triple.getProperty()] == undefined){
            inf.predicateDict[triple.getProperty()] = [triple];
        }else{
         inf.predicateDict[triple.getProperty()].push(triple);
        }
    }

}

function addTripleToPropertyDict( triple, inf ){
    if ( inf.matchingMechanism == "D"){
        addTripleToPropertyDictD( triple, inf );
    }else{
        if (triple.getType() == "r"){
            var tr;
            for (var k = 0; k < triple.getConsequents().length; k++){
                tr = triple.getConsequents()[k];
                addTripleToPropertyDictM(tr, inf.propertyDictM, triple);
            }

        }else{
            addTripleToPropertyDictM(triple, inf.propertyDictM, null);
        }
    }
}


function getRDFDB(path, fileName, infData, n3Parser){
      /** getRDFDB return an tripleset and an infData object that
        * contains global inferencing data that is needed
        * this function is necessary for integrating several files
        */
        var ts = [];
        n3Parser.resdic = infData.resdic;
        // this.originList = infData.originList
        // a counter for assigning  anonymous subjects
        n3Parser.anonCounter = infData.anonCounter;
        // a counter for tranforming local variables into global variables
        n3Parser.locCounter = infData.locCounter;
        // a counter for instantiating existential variables
        n3Parser.existCounter = infData.existCounter;
        // a counter for naming lists format: (res1 ...resn)
        n3Parser.listCounter = infData.listCounter;
        n3Parser.ruleNr = infData.ruleNr;
        n3Parser.tripleset = [];
        //writeln("getRDFDB before parsing!!!! ");
        n3Parser.parseAFile(path, fileName);
        if (n3Parser.errorFlag)
           n3Parser.writeOutput1();
        //writeln("getRDFDB after parsing!!!!");
        numberResources( n3Parser.tripleset, infData.dict);
        //writeln("getRDFDB resources numbered");
        //print("n3Parser.tripleset: " + n3Parser.tripleset + "\n");
        ts = checkLogical(n3Parser, n3Parser.tripleset);
        //writeln("getRDFDB checkLogical done.");
        //print("ts = " + ts + "\n");
        ts = checkAnonInRule(n3Parser, ts);
        //writeln("getRDFDB checkAnonInRule done");
        //print("ts = " + ts + "\n");
        infData.resdic = n3Parser.resdic;
        // infData.originList = n3Parser.originList
        // a counter for assigning  anonymous subjects
        infData.anonCounter = n3Parser.anonCounter;
        // a counter for tranforming local variables into global variables
        infData.locCounter = n3Parser.locCounter;
        // a counter for instantiating existential variables
        infData.existCounter = n3Parser.existCounter;
        // a counter for naming lists format: (res1 ...resn)
        infData.listCounter = n3Parser.listCounter;
        infData.ruleNr = n3Parser.ruleNr;
        return [ts, infData];
}

function getRDFDB1(setAsString, infData, n3Parser){
    var ts = [];
    n3Parser.resdic = infData.resdic;
    // this.originList = infData.originList
    // a counter for assigning  anonymous subjects
    n3Parser.anonCounter = infData.anonCounter;
    // a counter for tranforming local variables into global variables
    n3Parser.locCounter = infData.locCounter;
    // a counter for instantiating existential variables
    n3Parser.existCounter = infData.existCounter;
    // a counter for naming lists format: (res1 ...resn)
    n3Parser.listCounter = infData.listCounter;
    n3Parser.ruleNr = infData.ruleNr;
    n3Parser.tripleset = [];
    n3Parser.parseN3(setAsString);
    if (n3Parser.errorFlag)
       n3Parser.writeOutput1();
    numberResources( n3Parser.tripleset, infData.dict);
    //print("n3Parser.tripleset: " + n3Parser.tripleset + "\n");
    ts = checkLogical(n3Parser, n3Parser.tripleset);
    //print("ts = " + ts + "\n");
    ts = checkAnonInRule(n3Parser, ts);
    //print("ts = " + ts + "\n");
    infData.resdic = n3Parser.resdic;
    // infData.originList = n3Parser.originList
    // a counter for assigning  anonymous subjects
    infData.anonCounter = n3Parser.anonCounter;
    // a counter for tranforming local variables into global variables
    infData.locCounter = n3Parser.locCounter;
    // a counter for instantiating existential variables
    infData.existCounter = n3Parser.existCounter;
    // a counter for naming lists format: (res1 ...resn)
    infData.listCounter = n3Parser.listCounter;
    infData.ruleNr = n3Parser.ruleNr;
    //writeln("interface.getRDFDB1 ts = " + ts);
    return [ts, infData];

}

function getRDFDB2(setAsString, infData, n3Parser){
      /** getRDFDB1 return an tripleset and an infData object that
        * contains global inferencing data that is needed
        * this function is necessary for integrating several files
        */
        var ts = [];
        n3Parser.resdic = infData.resdic;
        // this.originList = infData.originList
        // a counter for assigning  anonymous subjects
        n3Parser.anonCounter = infData.anonCounter;
        // a counter for tranforming local variables into global variables
        n3Parser.locCounter = infData.locCounter;
        // a counter for instantiating existential variables
        n3Parser.existCounter = infData.existCounter;
        // a counter for naming lists format: (res1 ...resn)
        n3Parser.listCounter = infData.listCounter;
        n3Parser.ruleNr = infData.ruleNr;
        n3Parser.tripleset = [];

        n3Parser.parseN3(setAsString);
        //print("interface.getRDFDB1 n3Parser.tripleset\n");
        if (n3Parser.errorFlag > 0)
           n3Parser.writeOutput1();
        numberResources( n3Parser.tripleset, infData.dict);
        //print("n3Parser.tripleset: " + n3Parser.tripleset + "\n");
        ts = checkLogical(n3Parser, n3Parser.tripleset);
        //print("ts = " + ts + "\n");
        ts = checkAnonInRule(n3Parser, ts);
        //print("ts = " + ts + "\n");
        infData.resdic = n3Parser.resdic;
        // infData.originList = n3Parser.originList
        // a counter for assigning  anonymous subjects
        infData.anonCounter = n3Parser.anonCounter;
        // a counter for tranforming local variables into global variables
        infData.locCounter = n3Parser.locCounter;
        // a counter for instantiating existential variables
        infData.existCounter = n3Parser.existCounter;
        // a counter for naming lists format: (res1 ...resn)
        infData.listCounter = n3Parser.listCounter;
        infData.ruleNr = n3Parser.ruleNr;
        return [ts, infData];
}



function numberResources( tl, dict){
    for (var i =0; i < tl.length; i++)
          numberTriple( tl[i], dict );
}

function numberTriple(t, dict ){
              var nr1;
              var sub = t.getSubject();
              //print("subject = " + sub + " type = " + sub.getType() + "\n");
              numberResource( sub, dict );
              var prop = t.getProperty();
              numberResource( prop, dict );
              var obj = t.getObject();
              //print("object = " + obj + " type = " + obj.getType() + "\n");
              numberResource( obj, dict );
}

function numberResource( res, dict ){

   if (res.getType() == "cr")
       numberCResource( res, dict );
   else if (res.RDFList.length != 0)
       numberList( res.RDFList, dict );
   else{
       var nr1 = dict[res.uri];
       if (nr1 == undefined) {
           nr1 = resNrsInst.nextNumber();
           dict[res.uri] = nr1;
           res.nr = nr1;
       }else
           res.nr = nr1;
   }
}

function numberCResource( res, dict ){
   for (var i = 0; i < res.set.length; i++){
     //print("triple = " + res.set[i] + "\n");
     numberTriple( res.set[i], dict );
   }
}

function numberList( list, dict ){
   for (var i = 0; i < list.length; i++)
      numberResource( list[i], dict );
}


function checkAnonInRule(n3Parser, tl){
   /* Anonymous subjects in rules must be variables */
   var t;
   var ret;
   var flag;
   for (var i = 0; i < tl.length; i++){
      flag = 0;
      //print("t === \n");
      //printArray(t);
      t = tl[i];
      if (t.property.uri == log + "implies")
          flag = 1;
      ret = addGlobalVariables(n3Parser, t, [], flag);
      t = ret[0];
   }
   for (var i = 0; i < tl.length; i++){
       t = tl[i];
       try{
       if (t.getProperty().uri == log + "implies")
            tl[i] = new rule(t.subject.set, t.object.set);
       }catch(e){print("Exception: " + e + "\n");}
    }
   //print ("tl = " + tl + "\n");
   return elimDoubles(tl);
}

function addGlobalVariables(n3Parser,t, list, flag){
   /* add and change the global variables in a triple
    * call with empty list
    * flag indicates a rule
    */
    var ret;
    ret = addGlobalVariablesToRes(n3Parser, t.subject, list, flag);
    list = ret[0];
    n3Parser = ret[2];
    t.subject = ret[1];
    ret = addGlobalVariablesToRes(n3Parser, t.property, list, 0);
    list = ret[0];
    n3Parser = ret[2];
    t.property = ret[1];
    ret = addGlobalVariablesToRes(n3Parser, t.object, list, 0);
    list = ret[0];
    n3Parser = ret[2];
    t.object = ret[1];
    return [t, list, n3Parser];
}

function addGlobalVariablesToRes(n3Parser, r, list, flag){
    /* flag indicates a rule or a query
   /* add and change the global variables in a resource */
   var ret;
   var i;
   var e;
   if (r.simple == 0){
       for (i = 0; i < r.set.length; i++){
           ret = addGlobalVariables(n3Parser, r.set[i], list, flag);
           r.set[i] = ret[0];
           n3Parser = ret[2];
           list = ret[1];
       }
   }
   if (r.RDFList != undefined && r.RDFList.length != 0){
      //print("addGlobalVariablesToRes RDFList = " + r.RDFList + "\n");
      for (i = 0; i < r.RDFList.length; i++){
         ret = addGlobalVariablesToRes(n3Parser, r.RDFList[i], list, flag);
         r.RDFList[i] = ret[1];
         list = ret[0];
         n3Parser = ret[2];
      }
      //print("addGlobalVariablesToRes after RDFList = " + r.RDFList + "\n");
   }

    if (r.uri == undefined || r.uri == ""){
       return [list, r, n3Parser];
    }
    if (r.uri.substring(0, 5) == ":T$$$") {
        //print("uri::::: " + r.uri.substring(0, 7) + " flag " + flag);
        if (flag &&  r.nr > 0 && r.cr == true) {
            r.nr = - r.nr;
        } else {
            if (re.nr >= 0) {
                r.cr = false;
            }
        }
    }
    if ( r.uri.substring(0, 1) != "?"){
        return [list, r, n3Parser];
    }


   i = 0;
   try{
       var i2 = 0;
       for (var i1 = 0; i1 < list.length; i1++){
           ret = list[i1];
           if (ret[0] == r.uri){
              i2 = i1;
              break;
           }
       }
       ret = list[i2];
       var lab = ret[0];
       var n = ret[1];
       var name = ":G$$$" + n + lab;
       ret = n3Parser.resdic[name];
       var r = ret[1];
       return [list, r, n3Parser];
   }catch(e){
       list =concat( [r.uri, n3Parser.locCounter], list);
   }
   if (r.uri.substring(0, 5) == ":G$$$"){
        r.uri = ":G$$$" + n3Parser.locCounter + r.label;
        n3Parser.locCounter += 1;
        if (n3Parser.resdic[r.uri] == undefined){
           r.nr = -n3Parser.currRes;
           n3Parser.resdic[r.uri] = [n3Parser.currRes, r];
           n3Parser.currRes += 1;
        }
   }
   return [list, r, n3Parser];
}

function checkLogical(n3Parser, tripleList){
   /* react to log: instructions: log:forSome, log:forAll; log:Truth
    *
    *  variable handling:
    *    variables recieve a negative number for the 'number' property of Resource
    *    the entry in revres uses the corresponding positive number
    *    local universal variables are transformed to global universal variables by
    *    giving them a unique name starting with ":G$$$"
    *    local existential variables are instantiated with a unique name;
    *    global existential variables are instantiated with a unique name;
    *    the name of existential variables starts with ":E$$$"
    *    Handles also the "... is ... of ..." construct.
    */
    var tlout = [];     // triple list out
    var t;
    var ofullname;
    var nfullname;
    var nr;
    for (var i = 0; i < tripleList.length; i++){
        t = tripleList[i];

        //print("t = " + t + "\n");
        if (t.property.uri == log + "forAll"){
           if (t.subject.uri == n3Parser.getFromDictionary(":")){
               // this is a global universal variable
               // mark the object as such
               // do not return the triple
               // variables have a negative number
               if (t.object.nr > 0)
                   t.object.nr = -t.object.nr;
               t.object.varType = "gul";
            }else{
               // this defines a local universal variable
               // transform into a global variable
               // the subject should be a tripleset
               if (t.subject.getType() == "sr"){
                   n3Parser.errorList.push("!!! error in log:forAll instruction !!!");
                   n3Parser.errorFlag = 1;
               }else{
                   ofullname = t.object.uri;

                   if (t.object.varType != "gu"){
                      nr = t.object.nr;
                      t.object.varType = "gu";
                      if (nr > 0)
                          t.object.nr = -nr;
                      else
                          nr = -nr;
                      if (nr < 0)
                          nr = -nr;
                   }
                   tlout = concat(tlout, t.subject.set);
                }
            }
         }else if (t.property.uri == log + "forSome"){
            if (t.subject.uri == n3Parser.getFromDictionary(":")){
                // this is a global existential variable
                // mark the object as such
                // do not return the triple
                nr = t.object.nr;
                t.object.varType = "gel";
                if (n3Parser.queryFlag && t.object.nr > 0)
                   t.object.nr = -nr;
            }else{
                 // this defines a local existential variable
                 // the subject should be a tripleset
                 ofullname = t.object.fullname;
                 if (t.object.varType != "ge"){
                    nr = t.object.nr;
                    t.object.varType = "ge";
                    if (nr > 0)
                        if (n3Parser.queryFlag && t.object.nr > 0)
                             t.object.nr = -nr;
                    else{
                       nr = -nr;
                       if (nr < 0)
                          nr = -nr;
                  }
                  if (t.subject.getType() == "sr"){
                     n3Parser.errorList.push("!!! error in log:forSome instruction !!!");
                     n3Parser.errorFlag = 1;
                  }else
                     tlout = concat(tlout, t.subject.set);
                 }
             }
         }else if (t.object.uri == log + "Truth"){
             // this defines a truth; just add the subject

             // the subject should be a tripleset
             if (t.subject.getType() == "sr")
                 n3Parser.errorList.push("!!! error in log:Truth instruction !!!");
             else
                 tlout = concat(tlout, t.subject.set);
         }else{
             tlout.push(t);
         }
     }
   //print("tlout = " + tlout + "\n");
    // transform the rules in tlout
    //print("tlout = " + tlout + "\n");
    // now eliminate doubles in tlout
    return tlout;
}

function elimDoubles(tl){
   // eliminate double triples in a list
   if (tl.length < 2)
      return tl;
   else if (tripleInList(tl[0], subArray(tl, 1, tl.length))){
        //print("\ntripleInList = " + tl[0] + " : " +  tripleInList(tl[0], subArray(tl, 1, tl.length + "\n")));
        return elimDoubles(subArray(tl, 1, tl.length));
   }else{
          var out = elimDoubles(subArray(tl, 1, tl.length));
          out.unshift(tl[0]);
          return out;
   }
}

function testParser(){
    var myUrl = document.location.href;
    var li = myUrl.lastIndexOf("/");
    var myUrlDoc = myUrl.substring(8, li+1);
    myUrlDoc = replaceChars(myUrlDoc, '/', '\\');
    print("url of document = " + myUrlDoc + "\n");
    n3Parser = new N3Parser();
    n3Parser.init();
    n3Parser.parseAFile(myUrlDoc, "authen.axiom.n3");
    print("Parsed triples = \n" + n3Parser.tripleset);
}

function readAFile(path, fileName){
   netscape.security.PrivilegeManager.enablePrivilege("UniversalXPConnect");

   var s = path + fileName;
   s = replaceChars(s, '/', '\\');

   var data = "";
   var file = Components.classes["@mozilla.org/file/local;1"].
      createInstance(Components.interfaces.nsILocalFile);
   //writeln("readAFile filename = "  + s);
   file.initWithPath(s);
   return readAFileFi(file);
}

function readAFileF(fileName){
   //writeln("readAFileF fileName: " + fileName);
   netscape.security.PrivilegeManager.enablePrivilege("UniversalXPConnect");
   fileName = replaceChars(fileName, '/', '\\');

   var file;
   try{
      file = Components.classes["@mozilla.org/file/local;1"].
      createInstance(Components.interfaces.nsILocalFile);
      file.initWithPath(fileName);
   }catch(exception){print("readAFileF exception: " + exception + "\n" +
      " filename = " + fileName + "\n");}
   return readAFileFi(file);
}

function readAFileFi(file){
    netscape.security.PrivilegeManager.enablePrivilege("UniversalXPConnect");

   var data = "";
   try{

      var fstream = Components.classes["@mozilla.org/network/file-input-stream;1"].
          createInstance(Components.interfaces.nsIFileInputStream);
      var sstream = Components.classes["@mozilla.org/scriptableinputstream;1"].
          createInstance(Components.interfaces.nsIScriptableInputStream);
      fstream.init(file, 1, 0, false);
      sstream.init(fstream);
      data += sstream.read(-1);
      sstream.close();
      fstream.close();
   }catch(ex){print("readAFileFi exception: " + ex + "\n" +
      " filename = " + file.persistentDescriptor + "\n");}
   return data;
}



function saveAFile(savefile, s) {
        /* saves the content 's' to the file 'savefile'*/
	try {
		netscape.security.PrivilegeManager.enablePrivilege("UniversalXPConnect");
	} catch (e) {
		alert("Permission to save file was denied.");
	}
	var file = Components.classes["@mozilla.org/file/local;1"]
		.createInstance(Components.interfaces.nsILocalFile);
	file.initWithPath( savefile );
	if ( file.exists() == false ) {
		file.create( Components.interfaces.nsIFile.NORMAL_FILE_TYPE, 420 );
	}
	var outputStream = Components.classes["@mozilla.org/network/file-output-stream;1"]
		.createInstance( Components.interfaces.nsIFileOutputStream );
	/* Open flags
	#define PR_RDONLY       0x01
	#define PR_WRONLY       0x02
	#define PR_RDWR         0x04
	#define PR_CREATE_FILE  0x08
	#define PR_APPEND      0x10
	#define PR_TRUNCATE     0x20
	#define PR_SYNC         0x40
	#define PR_EXCL         0x80
        */
	outputStream.init( file, 0x04 | 0x08 | 0x20, 420, 0 );
	var result = outputStream.write(s, s.length);
	outputStream.close();
}

function triplesetToString(ts){
   if (ts.length == 0)
     return "";
   var s = "";
   for (var  i = 0; i<ts.length; i++){
      s = s + ts[i] + "\n";
   }
   return s;
}

function subArray(array, ind1, ind2){
 var nArr = [];
 for (var i = ind1; i < ind2; i++)
    nArr[i-ind1] = array[i];
 return nArr;
}

function testEqualResources(res1, res2){
   // test equality of resources
   //writeln("res1 type = " + res1.constructor + " res2 type " + res2.constructor);

/*   if (! (res1 instanceof resource)){
       writeln("TestEqualResources!! res1 is not a res: " + res1 + " res2: " + res2);
   }
    if (! (res2 instanceof resource)){
        writeln("TestEqualResources!! res2 is not a res: " + res2 + " res1: " + res2);
    }*/

   if (res1 == undefined)
      if (res2 == undefined)
         return true;
      else
         return false;
    if (res2 == undefined)
       if (res1 == undefined)
          return true;
       else
          return false;

    //writeln("interface.testEqualResources res1.nr = " + res1.nr + " res1 = " + res1.toString()
    //        + " res2.nr = " + res2.nr
    //           + " res2 = " + res2.toString() + "\n");

   if (res1.simple == 0 && res2.simple == 0){
      // complex resources
      for (var i = 0; i < res1.set.length; i++)
         if (tripleInList(res1.set[i], res2.set) == 0)
            return false;
      return true;
   }
   // for javascript substitutions; maybe must create special substitution procs??
   if ( res1.testVar() && res2.testVar() && res1.toString() == res2.toString()){
       if (res1.level == null || res2.level == null)
          return true;
       if (res1.level == res2.level)
          return true;
   }
    //
    if (res1.nr == undefined && res2.nr == undefined ){
        if (res1.toString() == res2.toString()){
            if (res1.level == null && res2.level == null)
               return true;
            if (res1.level == res2.level)
               return true;
        }else{
            return false;
        }

    }

   if (res1.nr == res2.nr){
      if (res1.level == null && res2.level == null)
         return true;
      if (res1.level == res2.level)
         return true;
   }

   return false;
}

function tripleInList(t, list){
   // test whether t is in list
   for (var i = 0; i < list.length; i++){
      //print("t = " + t + " list[i] : " + list[i] + " equality  " + testEqualTriples(t, list[i]) + "\n");
      if (testEqualTriples(t, list[i]))
         return 1;
   }
   return 0;
}

function testEqualTriples(t1, t2){
   /*print("t1 = ");
   printArray(t1);
   print(" t2 = ");
   printArray(t2);
   print("\n");*/
   // test equality of triples
   if (t1 == null && t2 == null)
       return 1;
   if (t1 == null || t2 == null)
       return 0;
   if (t1.getType() == "r" && t2.getType() == "r"){
       //print("t1 = " + t1 + " t2 = " + t2 + "\n");
       if (testEqualTriplesets(t1.getAntecedents(), t2.getAntecedents()))
          if (testEqualTriplesets(t1.getConsequents(), t2.getConsequents())){
              //print("bool =  1\n");
              return 1;
          }
       return 0;
   }
   if (t1.getType() == "r" && t2.getType() != "r")
       return 0;
   if (t1.getType() != "r" && t2.getType() == "r")
       return 0;
   if (testEqualResources(t1.getSubject(),  t2.getSubject()) &&
        testEqualResources(t1.getProperty(),  t2.getProperty()) &&
        testEqualResources(t1.getObject(),  t2.getObject()))
       return 1;
   return 0;
}

function testEqualTriplesets(ts1, ts2){
   if (ts1.length != ts2.length)
      return 0;
   for (var i = 0; i < ts1.length; i++)
       if (tripleInList(ts1[i], ts2) == 0)
          return 0;
   return 1;
}

function elimDoubleTriplesets(ts){
  /* elim double triplesets in a list of triplesets */

  if (ts == undefined || ts.length < 2  )
       return ts;
  for (var i = 1; i < ts.length; i++)
     if (testEqualTriplesets(ts[0], ts[i]))
        return elimDoubleTriplesets(subArray(ts, 1, ts.length));
  return concat([ts[0]], elimDoubleTriplesets(subArray(ts, 1, ts.length)));
}

function copyTriple(triplein){
   // quick copy of a triple
  var t;
  if (triplein == undefined)
      return triplein;
  if (triplein.getType() == "r"){
       var ants = copyTripleset(triplein.getAntecedents());
       var cons = copyTripleset(triplein.getConsequents());
       t = new rule(ants, cons);
       t.nr = triplein.nr;
       return t;
  }
  var sub = triplein.getSubject();
  var prop = triplein.getProperty();
  var obj = triplein.getObject();
  var sub1 = copyResource(sub);
  var prop1 = copyResource(prop);
  var obj1 = copyResource(obj);
  t = new cTriple(sub1, prop1, obj1);
  t.nr = triplein.nr;
  t.pending = triplein.pending;
  t.fromRule = triplein.fromRule;
  t.fromFact = triplein.fromFact;
  return t;
}

function testResource(res, res1){
    //print("res = " + res + "\n");
    if (res == undefined)
       return res1;
    if (res.getType() == "cr"){
       // complex resource
       res1.set = copyTripleset(res.set);
       return res1;
    }
    if (res.RDFList.length != 0){
       // print("testResource RDFList = " + res.RDFList + "\n");
       res1.RDFList = copyResourceList(res.RDFList);
       return res1;
    }
    return res1;
}


function copyTripleset(ts){
   var tsout = [];
   for (var i = 0; i < ts.length; i++)
      tsout.push(copyTriple(ts[i]));
   return tsout;
}

function copyResource(resin){
  // copy of a resource
  r = resin.uri;
  //print("resin = " + resin + "\n");
  if (resin.getType() == "cr")
     resout = new cResource();
  else
     resout = new resource(r);
  resout.level = resin.level;
  resout.nr = resin.nr;
  resout.list = resin.list;
  resout.RDFList = resin.RDFList;
  resout.constant = resin.constant;
  resout = testResource(resin, resout);
  resout.cr = resin.cr;
  return resout;
}

function copyResourceList(lin){
   var lout = [];
   for (var i = 0; i < lin.length; i++)
      lout.push(copyResource(lin[i]));
   return lout;
}

function myClock(){
   var today=new Date();
   var theHours=today.getHours();
   var theMinutes=today.getMinutes();
   if (theMinutes<10)
      var theMinutes="0"+theMinutes;
   var theSeconds=today.getSeconds()
   if (theSeconds<10)
      var theSeconds="0"+theSeconds;
   var theMillis = today.getMilliseconds();
   var theTimeNow=theHours+":"+theMinutes+":"+theSeconds + ":" + theMillis;
   return theTimeNow;
}

function concat(array1, array2){
    if (array1 == undefined){
        return array2;
    }
    if (array2 == undefined){
        return array1;
    }
    if (array1.length == 0)
       return array2;
    if (array2.length == 0)
       return array1;
    out = [];
    for (var i = 0; i < array1.length; i++)
        out.push(array1[i]);
    for (var i = 0; i < array2.length; i++)
        out.push(array2[i]);
    return out;
}

function arrayToString(arr){

    var s = "";
    if (arr == undefined){
        s = "UNDEFINED";
        return s;
    }
    if (arr instanceof Array){
        s = s + "[";
        for(var i = 0; i < arr.length; i++){
            s = s + arrayToString(arr[i]) + " ";
        }
        s = s + "]";
    }else
        s = s + arr ;
    return s;
}

var resNrsInst = new function resNrs(){
    this.nr = 0;
    this.nextNumber = function(){
        this.nr++;
        if (this.nr > 30000){
            this.nr = 0;
        }
        return this.nr;
    }
}

function checkTriple(tripleIn){
    var s = "Triple: " + tripleIn + "\n";
    if (! (tripleIn instanceof triple) || ! (tripleIn instanceof cTriple)){
        s = s + ("This input is not a triple!!!!");
        return s;
    }
    if (! (tripleIn.getSubject() instanceof resource)){
        s = s + "Subject is not a resource.\n";
    }
    if (! (tripleIn.getPredicate() instanceof resource)){
        s = s + "Predicate is not a resource.\n";
    }
    if (! (tripleIn.getObject() instanceof resource)){
        s = s + "Object is not a resource.\n";
    }
    return s;
}

function checkTripleset(tripleset){
    var s;
    if (! (tripleset instanceof Array)){
        s = s + ("Tripleset: " + tripleset + "\nis not an array!!");
    }
    for (var i= 0; i < tripleset.length; i++){
        s = s + checkTriple(tripleset[i]);
    }
}

function checkRes(subject, predicate, object){
    var  s;
    s = checkResource(subject);
    s = s + checkResource(predicate);
    s = s + checkResource(object);
    return s;
}

function checkResource(resourceIn){
    var s;
    if (! (resourceIn instanceof resource) && ! (resourceIn instanceof cResource)){
        s =  "The input: " + resourceIn + " is not a resource object!!!";
    }
    return s;
}