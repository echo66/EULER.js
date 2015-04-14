/**
 * Example parameter definition:
 * [ a :parameter; :hasName "myName"; :hasValue "myValue"].
 * Author: Guido J.M. Naudts Bouwel
 */
function Parameter(){

    this.parameters = [];
    this.file;
    this.path = "http://eulermoz/parameter#";

    this.prefixes =
            "@prefix rdf: <http://www.w3.org/1999/02/22-rdf-syntax-ns#>.\n" +
            "@prefix rdfs: <http://www.w3.org/2000/01/rdf-schema#>.\n" +
            "@prefix owl: <http://www.w3.org/2002/07/owl#>.\n" +
            "@prefix : <http://eulermoz/parameter#>.\n";

    this.owlDefinition =
            this.prefixes +
            ":parameter a owl:Class.\n" +
            ":hasName a owl:DatatypeProperty;\n" +
            "rdfs:domain :parameter;\n" +
            "rdfs:range rdfs:Literal.\n" +
            ":hasValue a owl:DatatypeProperty;\n" +
            "rdfs:domain :parameter;\n" +
            "rdfs:range rdfs:Literal.\n";

    this.getAll = function(){
        return this.parameters;
    }

    this.setAll = function( map ){
         this.parameters = map;
    }

    this.addAll = function( map){
         this.parameters = this.parameters.concat(map);
    }

    this.addParameter = function( name, value ){
        this.parameters[name] = value;
    }

    this.getParameter = function( name ){
        if ( this.parameters == undefined ){
            return "";
        }
        if (  this.parameters[name] != undefined){
            return this.parameters[name];
        }else{
            return "";
        }
    }

    this.readParameterFile1 = function(){
        if ( this.fileO != undefined){
           return this.readParameterFile2( this.fileO );
        }else{
            return false;
        }
    }

    this.readParameterFile2 = function( fileIn ){

        var i = fileIn.lastIndexOf("/");
        if ( i < 0){
            //i = fileIn.lastIndexOf("\\");
        }
        //writeln("Parameter.readParameterFile2 path: " + fileIn.substring(0,i+1) + " name: " + fileIn.substring(i+1));
        this.readParameterFile3(fileIn.substring(0,i+1), fileIn.substring(i+1));
    }

    this.getBasePath = function(){
        var myUrl = document.location.href;
        var li = myUrl.lastIndexOf("/");
        var myUrlDoc = myUrl.substring(8, li+1);
        myUrlDoc = replaceChars(myUrlDoc, '/', '\\');
        return myUrlDoc;
    }


    this.readParameterFile3 = function( filePath, fileName ){

        var t = "?a <" + this.path + "hasName> ?p.";
        var t1;


        interface = new XULInterface();
        //writeln("file == " + filePath + fileName);
        interface.addSetByFilename("params", "a", filePath + fileName);
        interface.addSetByString("q1", "q", t);
        //writeln("interface.N3setBuffer " + interface.N3setBuffer["params"]);
        interface.makeInfDB("pdb", ["params"] );
        //writeln("Params: " + interface.getSet("pdb", "params") + "Query: " + interface.getSource("q1"));
        var sols1 = interface.queryInfDB("pdb", "q1", "forward" );
        //writeMessage("sols1 = " + sols1);


        var sols2;
        this.parameters = [];
        var tr;

        for (var i = 0; i < sols1.length; i++){
            tr = sols1[i];
            t1 = tr[0].getSubject().toString() + " <" +
                    this.path + "hasValue> ?p.";
//            writeln("t1 ============= " + t1);
            interface.addSetByString("q" + i + 2, "q", t1);
            sols2 = interface.queryInfDB("pdb", "q" + i + 2, "forward");
            //writeMessage("sols2::: " + sols2[0][0].getObject().toString());
            //writeMessage("name ::: " + tr[0].getObject().toString());
            this.parameters[tr[0].getObject().toString()] = sols2[0][0].getObject().toString();
        }
        //writeMessage("Parameter.readPArameterFile3 parameters: " + mapToString(this.parameters) + "\n");
        return true;

    }

    this.saveParameterFile = function(){
        if ( this.fileO != null){
           this.saveParameterFile( this.fileO );
           return true;
        }else{
            return false;
        }
    }


    this.saveParameterFileP = function( fileIn ){
        // prepare the output string
        var s = this.prefixes;
        for ( var key in this.parameters ){
            if (this.parameters[key] != undefined){
                s = s +  "[ a :parameter; :hasName \"" + key +
                  "\"; :hasValue \"" +
                  this.parameters[key].replace("\"", "\\\"") +
                  "\" ].";
            }
        }
        //writeln("file = " + fileIn + "\ns = " + s)
        // now write file
        try{
            saveAFile( fileIn, s);
        }catch( e){
            alert("Error saving parameter file:\n" + fileIn + "\nException: " + e + "\n");
        }
    }

}
