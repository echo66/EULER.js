/*
 * Interface for a dynamic XUL Window based on N3 inferencing
 * ============================================================
 * Example:
 * var interface = new XULInterface();
 * interface.addSetByFilename("params", "a", filePath + fileName );
 * interface.addSetByString("q1", "q", t);
 * interface.makeInfDB("pdb", ["params"] );
 * var sols1 = interface.queryInfDB("pdb", "q1", "forward" );
 * Author: Guido J.M. Naudts Bouwel
 */

function XULInterface(){

    // dictopnary of N3 sets
    // format of entries:
    // [type_of_the_set, filename, set]
    //  type: the type of file:
    //         "d" = data
    //         "r" = rules
    //         "a" = axioms (data + rules)
    //         "q" = query 
    // filename can also be a URI; filename = "" when
    // originating from an array
    // set = the triples as a (long) string
    this.N3setBuffer = [];


    // the dictionary of infData objects
    this.infList = [];

    // list of positions of sets in the infData object
    this.setNameList = [];

    this.verbose = false;

    this.limit = -1;

    this.matchingMechanism="M";

    this.addSetByFilename = function(name, type, filename){
        /*
         *	name: name by which this set of triples is known in the program
         *  type: the type of file:
         *         "d" = data
         *         "r" = rules
         *         "a" = axioms (data + rules)
         *         "q" = query
         *  filename: the name of the N3 file
         *   Return: null
         * Example: addFileByName("authen", "a", "authen.axiom.n3");
         */
         // get the triples
         var i = filename.lastIndexOf("\\");
         var filepath = filename.substring(0, i+1);
         var filename1 = filename.substring(i+1, filename.length);
         //writeln("addSetByFilename filePath: " + filepath + " filename1: " + filename1);
         var data = readAFile(filepath, filename1);
         //writeln("addSetByFilename data:: " + data);
         this.N3setBuffer[name] = [type, filename, data];
    }

    // this.addFileByURIForInf

    this.addSetByStringArray = function(name, type, array){
       /*
	*    name: name by which this set of triples is known in the program
        * type: the type of file:
        *      "d" = data
        *      "r" = rules
        *      "a" = axioms (data + rules)
        *      "q" = query
        * array: an array of strings in N3 format
        *  Return: null
        *   Example: addFileByStringArray("query", "q",
        *       ["@prefix : <authen#>", "?who :authenticated ?what."]);
        */
        // make one big string
        var s = "";
        for (var i = 0; i < array.length; i++)
          s = s + array[i] + "\n";
        this.N3setBuffer[name] = [type, "", s];
     }

    this.addSetByString = function(name, type, str){
       /*
	*    name: name by which this set of triples is known in the program
        * type: the type of file:
        *      "d" = data
        *      "r" = rules
        *      "a" = axioms (data + rules)
        *      "q" = query
        * str: an N3 file as string
        *  Return: null
        *   Example: addSetByString("query", "q",
        *       "@prefix : <authen#>\n?who :authenticated ?what.");
        */
        // make one big string
        this.N3setBuffer[name] = [type, "", str];
     }

     this.addSetByTripleset = function(name, type, tripleset){

     }


 /* Note: executing addFileByName and addFileByStringArray
  *    a second time with the same name will overwrite the
  *    previous entered file.
  */


    this.makeInfDB = function(dbName, setList){
       /*  dbName: name of the db
        *  setList: list of names of sets. The name is the 'name' parameter in
        *  addFileByNameForInf,addFileByURIForInf and  addFileByArrayForInf.

        *  Return: null
        *  Example: makeInfDB("myDB", ["authen", "data"]);
        *   Note: a default db is constituted by all entered files by the
        *     commands addFileByNameForInf and addFileByArrayForInf
        *     with the exception of query files
        */
        // get the list of strings
        var set;
        var n3Parser;
        var ret;
        var inf = new infData([]);
        var dbi;
        //writeln("XULInterface.makeInfDB setList.length = " + setList.length);
        for (var i = 0; i < setList.length; i++){
            set = this.N3setBuffer[setList[i]];
            if (set[1] == "q"){
                continue;
            }
            if (set == undefined){
                writeMessage("Undefined set name!!!: " + setList[i]);
                continue;
            }
            // for each string parse and enter in infData object
            n3Parser = new N3EParser();
            ret = getRDFDB1(set[2], inf, n3Parser);
            // do some infData manipulations
            inf = ret[1];
            //writeln("set = " + ret[0]);
            dbi = new db(ret[0]);
            dbi.makePropertyDict();
            this.setNameList[setList[i]] = i;
            inf.dslist.push(dbi);
        }

        inf.graphs = inf.dslist;
        //writeln("XULInterface.makeInfDB inf.graphs[0]: " + inf.graphs[0].ts);
        inf.tripleNr = inf.initinf1(0);
        this.infList[dbName] = inf;

        //writeln("inf added to infList[dbName]: " + dbName);
     }

     this.queryInfDB = function(dbName, queryName, inferenceType){
         /* dbName: name of a db
          * queryName: name of a queryfile
          * inferenceType: actually two choices: "forward" and "backward"
          * Return: an array of arrays.
          *   The second order arrays are arrays of strings
          *   in N3 format; each string array represents a solution
          *   i.e. the query with all variables substituted
          *   by resources.
          *     Example: queryInfDB("myDB", "query", "backward");
          */
          // the state of the infData variables must be saved in vector inf.stateSave
          // so the state can be restored for a new query
          //writeln("XULInterface.queryInfDB dbName: " + dbName);
          var inf = this.infList[dbName];
          if (inf.stateSave == undefined)
             inf.stateSave = [inf.resdic, inf.currRes, inf.anonCounter, inf.locCounter,
                 inf.existCounter, inf.listCounter, inf.ruleNr, inf.tripleNr];
          else{
             inf.resdic = inf.stateSave[0];
             inf.currRes = inf.stateSave[1];
             inf.anonCounter = inf.stateSave[2];
             inf.locCounter = inf.stateSave[3];
             inf.existCounter = inf.stateSave[4];
             inf.listCounter = inf.stateSave[5];
             inf.tripleNr = inf.stateSave[6];
          }
          var n3Parser  = new N3EParser();
          n3Parser.queryFlag = 1;
          var set = this.N3setBuffer[queryName];
          //print("setBuffer query "+ arrayToString(this.N3setBuffer[queryName][2]) + "\n");
          var ret = getRDFDB1(set[2], inf, n3Parser);
          //writeln("XULInterface.queryInfDB ret = " + ret);
          // do some infData manipulations
          inf = ret[1];
          dbi = new db(ret[0]);

          dbi.makePropertyDict();
          //print("dbi " + dbi.ts + "\n");
          inf.dslist.push(dbi);
          if (inf.dslist.length > 0){
            inf.graphs = subArray(inf.dslist, 0, inf.dslist.length-1);
            inf.goallist = inf.dslist[inf.dslist.length-1].ts;
          }
          inf.query = [];
          inf.goallistSav = [];
          inf.querySav = [];
          //print("XULInterface inf.goallist = " + inf.goallist)

          for (var i = 0; i <  inf.goallist.length; i++) {
              inf.query.push(copyTriple(inf.goallist[i]));
              inf.goallistSav.push(copyTriple(inf.goallist[i]));
              inf.querySav.push(copyTriple(inf.goallist[i]));
          }
          //print("XULInterface inf.query = " + inf.query)
          inf.tripleNr = inf.initinf1(inf.tripleNr);
          inf.nooutput = 1;
          inf.verbose = this.verbose;
          inf.maxSteps = this.limit;
          inf.matchingMechanism = this.matchingMechanism;
          //inf.verbose=true;
          //inf.maxSteps = 50;
          if (inferenceType == "backward")
             inference(inf);
          if (inferenceType == "forward")
             reason(inf);
          inf.dslist.pop();
          return inf.solbuf;
     }

     this.getSet = function( DBName, setName ){
         /* getDB(dbName):
          *        dbName: name of a db
          *  Return: a tripleset.
          *  Example: getDB("gedcom", "myFamily");
          */
          var pos = this.setNameList[setName];
          return  this.infList[DBName].dslist[pos].ts;
     }

     this.getSource = function( setName ){
         return this.N3setBuffer[setName];
     }
}