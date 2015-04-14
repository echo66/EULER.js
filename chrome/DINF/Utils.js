/** module utils
  * Author: Guido J.M. Naudts Bouwel
  */
var prefixPredicate = resMan("prefix:abbrev","prefix:abbrev", "<prefix:abbrev>");

//# delimiter list
var delimNode = " .;]}{[=\n\r,\t})(^";

var scheduleTimeout = 100;


function resMan( fullnameIn, abbrevIn, labelIn){
   var resourceOut = new resource("");
   resourceOut.simple = 1;
   resourceOut.uri = fullnameIn;
   resourceOut.abbrev = abbrevIn;
   resourceOut.label = labelIn;
   return resourceOut;
}

// see if a character is present in a string
function checkCharacter(ch, string){
   var i = string.length;
   var i1 = 0;
   var done = 0;
   while (i1 < i && done == 0){
       if (ch == string[i1]){
          done = 1;
          break;
       }  
       i1 = i1 + 1;
   }
   return done;
}


function takec(ch, s){
/*
 takec a b will parse character a from string b
 and returns (True, b-a) or (False, b)
*/
   if (s.length == 0)
       return [0, ""];
   else{
     if (ch == s.substring(0, 1))
         return [1, s.substring(1, s.length)];
     else
         return [0, s];
   }
}

function parseUntil(ch, inString){
   /* parseUntil( a, b) will take from string b until char a is met
      and returns (True, c, b-c)   where c is the part of b before a with
      a not included or it returns (False, "", b)
   */    
   if (inString.length == 0)
      return [0, "", ""];
   else{
      var list; 
      list = parseUntilHelp(0, ch, "", inString);
      if (list[0] == 0)
         return [0, list[2], list[3]];
      else
         return [1, list[2], list[3]];
   }
}

// help function for parseUntil
function parseUntilHelp(bool, ch, string1, string2){
   while (string2.length > 0){
       if (string2.substring(0, 1) == ch)
          return [1, ch, string1, string2.substring(1, string2.length)];
       else{
          if (string2.length > 1){
               string1 = string1 + string2.substring(0, 1);
               string2 = string2.substring(1, string2.length);
          }
          else
               return [0, ch, string1, ""];
       }
  }
  return [0, ch, string1, ""];
}

function parseUntilString(s1, s2){
   /* parseUntilString (s1, s2) will parse string s1 until string s2 is met.
    * True or False is returned; the parsed string and the rest string with
    *  s2 still included
    */
    var ret;
    var bool;
    var first;
    var rest;
    if (s1 == "" || s2 == "")
        return [0, s1, s2];
    ret = parseUntil(s2[0], s1);
    bool = ret[0];
    first = ret[1];
    rest = ret[2];
    if (bool && rest.substring(0, s2.length-1) == s2.substring(1, s2.length))
       return [1, first, s2.substring(0,1) + rest];
    else if (bool == 0)
       return [0, s1, s2];
    else{
       var first1;
       ret = parseUntilString(rest, s2);
       bool = ret[0];
       first1 = ret[1];
       rest = ret[2];
       return [bool, first + s2.substring(0,1) + first1, rest];
    }
}  
            
function parseUntilDelim(delimString, s){
   /* parseUntilDelim delim input will take a list with delimiters and parse the
      input string till one of the delimiters is found .
      It returns (True c input-c) where c is the parsed string without the
      delimiter or it returns (False "" input) if no result
    */
    //writeln("parseUntilDelim = " + s);

    if (s == "")
        return (0, "", "")
    else
        return parseUntilDelimHelp(delimString, "", s);
}

function parseUntilDelimHelp(delimString, s, input){
    /* This is a help function .
       must be called with s = ""
     */
     //writeln("parseUntilDelimHelp entered = " + input);
     if (input == "")
        return (0, s, "");
     else{
        if ( elemS(input.substring(0, 1), delimString))
            return [1, s, input];
        else
            return parseUntilDelimHelp(delimString, s + input.substring(0, 1),
                                                input.substring(1, input.length));
     }
}

// see if a character occurs (at least one time) in a string.
function elemS(ch, string){
    //writeln("Utils.elemS entered.")
    if (string.length == 0)
        return 0;
    else{
      //writeln("Utils.elemS ch = " + ch) ;
      if (ch == string.substring(0, 1)){
        //writeln("Utils.elemS ch after = " + ch);
        return 1;
      }
      else
        return elemS(ch, string.substring(1, string.length));
    }
}        

// skipTillCharacter skip the input string till the character is met .
// The rest of the string is returned without the character.
function skipTillCharacter(c, input){
   if (input.length == 0)
       return "";
   else{
       if (input[0] == c)
          return input.substring(1, input.length);
       else
          return skipTillCharacter(c, input.substring(1, input.length));
   }
}

// test if the following character is a blanc.
function testBlancs(ch){
   if (ch == " " || ch == "\n" || ch == "\r" || ch == "\t")
       return 1;
   else
       return 0;
}

// skips the blancs in a string and returns the stripped string.
function skipBlancs(s){
    if (s == "")
       return "";
    else{
       var x;
       while (s.length > 0){
          x = s.substring(0, 1);
          if (x == "#")
             s = parseComment(s);    
          else if (x == " " || x == "\n" || x == "\r" || x == "\t")
             s = s.substring(1, s.length);
          else
             return s;
       } 
    }
    return "";
}

function skipBlancs1(s){
    /*
     * skips the blancs but no comment in a string and returns
     * the stripped string.
     */ 
     if (s.length == 0)
        return "";
     else{
        var x;
        while (s != ""){
           x = s[0];
           if (x == " " || x == "\n" || x == "\r"){
              s = s.substring(1, s.length);
           }else
              return s;
         }
      }
      return "";
}   

function parseComment(s){
/* function for parsing comment.
   input is the string to be parsed.
   the comment goes till "\n" is encountered.
   returns a string with the comment striped off.
*/
   if (s == "")
      return "";
   else{
      var l1 = takec("#", s); // format (Bool,String)
      var l2 = parseUntil ("\n", l1[1]); // format (Bool, String, String)
      var l3 = parseUntil ("\n", l1[1]); // format (Bool, String, String)
      if (l1[0] && l2[0])
         return skipBlancs(l2[2]);
      else if (l1[0] && l3[0])
         return skipBlancs(l3[2]);
      else
         return "Error parsing comment" + s;
   }
} 


// containsString test whether the first string is contained in the
// second string.
function containsString(s1, s2){
   if (s1.length == 0)
       return 1;
   else if (s2.length == 0)
       return 0;
   else if (s1[0] == s2[0])
       return containsString(s1.substring(1, s1.length), s2.substring(1, s2.length));
   else
       return containsString(s1, s2.substring(1, s2.length));
}
        
// parseString a b will parse string a from string b
// and returns  (1, b-a) or (0,b).
function parseString(a, b){
    var a1 = a.length;
    var s = b.substring(0, a1);
    var c = b.substring(a1, b.length);
    if (s == a)
       return [1, c];
    else
       return [0, b];
}

function replaceChars(s, ch1, ch2){
   // replace every occurence of ch1 with ch2
  //print("s[0] = " + s[0] + " ch2 = " + ch2 + "\n");
  if (s.length == 0)
     return "";
  if (s.length == 1)
    if (s[0] == ch1)
       return ch2;
    else
       return s[0];
  if (s[0] == ch1)
     return ch2 + replaceChars(s.substring(1, s.length), ch1, ch2);
  else
    return s[0] + replaceChars(s.substring(1, s.length), ch1, ch2);
}

function stopProgram(time){
     setTimeout(throwException, time);
}

function throwException( message){
    throw message;
}

function checkFileExistence(fileIn){
    netscape.security.PrivilegeManager.enablePrivilege("UniversalXPConnect");

   try{
        var file = Components.classes["@mozilla.org/file/local;1"].
            createInstance(Components.interfaces.nsILocalFile);
        file.initWithPath(fileIn);
        if ( !file.exists){
            return false;
        }
   }catch(exception){
       return false;
   }
   return true;
}

function fileChooser(path, explanation, filter, mode ){
  //writeMessage("path: " + path + "\n");
  var fileString;
  var fileName;
  netscape.security.PrivilegeManager.enablePrivilege("UniversalXPConnect");
  try{
      var nsIFilePicker = Components.interfaces.nsIFilePicker;
      var myFilePicker  = Components.classes["@mozilla.org/filepicker;1"].createInstance(nsIFilePicker);
      var file = Components.classes["@mozilla.org/file/local;1"].
          createInstance(Components.interfaces.nsILocalFile);

      file.initWithPath(path);

      myFilePicker.displayDirectory =  file;
      myFilePicker.init(window,"Select a file", mode);
      myFilePicker.appendFilter( explanation, filter); // eg.( "n3 files", "*.n3")
      var fileOk = myFilePicker.show();
      if (fileOk == nsIFilePicker.returnOK) {
          fileName = myFilePicker.file.path;
          //writeMessage("File selected = " + fileName + "\n");
      }else{
          fileName = myFilePicker.file.path;
          //writeMessage("File selected = " + fileName + "\n");

      }
  }catch(exception){
      alert("error with fileChooser: " + exception );
  }

  return fileName;
}

function saveTextFile(text){
      var fileN = fileChooser(getBasePath() + "output", ".txt", "*.txt", 1);
      saveAFile(fileN.toString(), text);
      return fileN.toString();
}

function getBasePath(){
    if (document.location == undefined){
        return "/";
    }
    var myUrl = document.location.href;
    var li = myUrl.lastIndexOf("/");
    var myUrlDoc = myUrl.substring(8, li+1);
    myUrlDoc = replaceChars(myUrlDoc, '/', '\\');
    myUrlDoc = myUrlDoc.replace( "%20", " ");
    //writeMessage("Utils.getBasePath basePath = " + myUrlDoc + "\n");
    if( myUrlDoc == "\\dinf\\content\\"){
        myUrlDoc = chromeToPath("chrome://dinf/content/");
        //writeMessage("Utils.getBasePath path: " + myUrlDoc + "\n");
        li = myUrlDoc.lastIndexOf("\\");
        myUrlDoc = myUrlDoc.substring(0, li +1);
        myUrlDoc = replaceChars(myUrlDoc, '/', '\\');
        myUrlDoc = myUrlDoc.replace( "%20", " ");

        //writeMessage("Utils.getBasePath path: " + myUrlDoc + "\n");
    }
    return myUrlDoc;
}

function chromeToPath (aPath) {

   if (!aPath || !(/^chrome:/.test(aPath))){
       print("Utils.chromeToPath Not a chrome url: " + aPath);
       //return; //not a chrome url
   }

   var rv;
      netscape.security.PrivilegeManager.enablePrivilege("UniversalXPConnect");
      var ios = Components.classes['@mozilla.org/network/io-service;1'].getService(Components.interfaces["nsIIOService"]);
        var uri = ios.newURI(aPath, "UTF-8", null);
        var cr = Components.classes['@mozilla.org/chrome/chrome-registry;1'].getService(Components.interfaces["nsIChromeRegistry"]);
        rv = cr.convertChromeURL(uri).spec;

        if (/^file:/.test(rv))
          rv = this.urlToPath(rv);
        else
          rv = this.urlToPath("file://"+rv);

      return rv;
}

function urlToPath (aPath) {
    netscape.security.PrivilegeManager.enablePrivilege("UniversalXPConnect");
    if (!aPath || !/^file:/.test(aPath)) {
      print("Utils.urlToPath Not a file path: " + aPath);
      return ;
    }    
    var rv;
   var ph = Components.classes["@mozilla.org/network/protocol;1?name=file"]
        .createInstance(Components.interfaces.nsIFileProtocolHandler);
    rv = ph.getFileFromURLSpec(aPath).path;
    return rv;
}

function HashTable(){
    this.size = 0;
    this.dict = [];

    /**
      * return true if the (key, value) pair can be created;
      * if an element with such a key already exists return false
      */
    this.add = function(key, value){
        if (this.dict[key] != undefined){
            return false;
        }

        this.dict[key] = value;
        this.size++;
        return true;
    }

    this.remove = function(key){
        if (this.dict[key] == undefined ){
            return false;
        }
        this.dict[key] = undefined;
        this.size--;
        return true;

    }

    this.get  = function(key){
        if (this.dict[key] != undefined)
            return this.dict[key];
    }

    this.getKeys = function(){
        var keys = [];
        for (key in this.dict){
            keys.push(key);
        }
        return keys;
    }

    this.getValues = function(){
        var valuesOut = [];
        var val;
        for (key in this.dict){
            val = this.dict[key];
            //writeMessage("Value = " + val);
            if(val != undefined){
                valuesOut.push(val);
            }
        }
        return valuesOut;

    }

    this.getSize = function(){
        return this.size;
    }


}

    function schedule(threadManager) {
        if (! threadManager.stop)
            threadManager.schedule();

        setTimeout("schedule(threadManager);", scheduleTimeout);
    }

    function mapToString(mapIn){
        s = "";
        for (var key in mapIn){
            s = s + key + " : " + mapIn[key] + " || ";
        }
        return s;
    }

function readObject(transport) {
        this.transport = transport;
        this.stream;
        this.instream;


        this.init = function() {
            try {
                netscape.security.PrivilegeManager.enablePrivilege("UniversalXPConnect");

                this.stream = this.transport.openInputStream(1, 0, 0);
                this.instream = Components.classes["@mozilla.org/scriptableinputstream;1"]
                        .createInstance(Components.interfaces.nsIScriptableInputStream);
                this.instream.init(this.stream);
            } catch (ex) {
                writeln("readObject.init() exception: " + ex);
            }

        };
        this.read = function() {
            var data = "";
            try {
               // while ((data.indexOf("EOT") == -1) && (data.indexOf("EOM") == -1)) {
                   netscape.security.PrivilegeManager.enablePrivilege("UniversalXPConnect");

                    data += this.instream.read(this.instream.available());
               // }
            } catch(ex) {
                writeln("readObject.read() exception: " + ex + "\n");
                return undefined;
            }

            return data;
        };

        this.close = function() {
            try {
                this.instream.close();
            } catch(ex) {
                writeln("readObject.close() exception: " + ex + "\n");
            }

        }
}


function isEquivalentGoal(  triple1,  triple2 ) {

   if( triple1 == undefined || triple2 == undefined) {
      writeln("Utils.isEquivalentGoal: Cannot tell from a null triple: " + triple1 + ", " + triple2 );
      return false;
   }

   equivalent = false;
   var here, there;
   here = triple1.getSubject();
   there = triple2.getSubject();
   equivalent = isEquivalentElement(here, there);
   if( !equivalent ) {
         return false;
   }
    here = triple1.getProperty();
    there = triple2.getProperty();
    equivalent = isEquivalentElement(here, there);
    if( !equivalent ) {
          return false;
    }

    here = triple1.getObject();
    there = triple2.getObject();
    equivalent = isEquivalentElement(here, there);
    if( !equivalent ) {
          return false;
    }

   return true;
}

function isEquivalentElement( here, there) {
   var equivalent = false;
       if (( here.getType() == "sr" && there.getType() == "sr") ||
                ( here.getType() == "lt" && there.getType() == "lt")){
             if (here.testVar() && there.testVar() ){
                 equivalent = true;
             }else{
                 equivalent = here.toString() == there.toString();
             }
      }else if( here.getType() == "lr" && there.getType() == "lr" ) {

         equivalent = isEquivalentContainer( here, there);

      } else if( here.getType() == "cr" && there.getType() == "cr" ) {

         equivalent = isEquivalentTripleSet( here, there );
      }

   return equivalent;
}

function isEquivalentContainer( ec1, ec2 ){
   if ( ec1.RDFList.length != ec2.RDFList.length){
      return false;
   }
   for (var k = 0; k < ec1.RDFList.length; k++){
       if ( ! isEquivalentElement(ec1.RDFList[k], ec2.RDFList[k])){
         return false;
      }

   }
   return true;
}

function isEquivalentTripleSet(  set1,  set2 ){
   if ( set1.set.length != set2.set.length ){
      return  false;
   }
    for (var k = 0; k < set1.set.length; k++){
        if ( ! isEquivalentGoal(set1.set[k], set2.set[k])){
          return false;
       }

    }
   return true;

}

function encodeHTML(s)
{
    var sout = "";
    var c;
    //writeMessage("Utils.encodeHTML s: " + s + " length: " + s.length);
    for(var i=0; i<s.length; i++)
    {
        c = s.charAt(i);
        if(c > 127 || c=='"' || c=='<' || c=='>')
        {
           sout = sout + "&#" + s.charCodeAt(i) + ";";
        }
        else if ( c=='&' ){
           sout = sout + "&amp;";
        }else
        {
            sout = sout + c;
        }
    }
    return sout;
}


function decodeHTML( s ){
    var sout = "";
    var c;
    var index;
    var group;
    var i = 0;

    while ( i < s.length ){
        c = s.charAt(i);
        if ( c == '&'){
            index = s.indexOf(";", i);
            // retrieve group
            group = s.substring(i + 1, index);
            if ( group == "amp"){
                sout = sout + "&";
            }else if( group == "quot"){
                sout = sout + "\"";
            }else if( group == "lt"){
                sout = sout + "<";
            }else if( group == "gt"){
                sout = sout + ">";

            }else{
                c = String.fromCharCode(parseInt(group.substring(1)));
                sout = sout + c ;
            }
            i = index + 1;
        }else{
            sout = sout + c;
            i++;
        }
    }
    return sout;
}


function post_to_url(path, params, method) {
    method = method || "post"; // Set method to post by default, if not specified.

    // The rest of this code assumes you are not using a library.
    // It can be made less wordy if you use one.
    var form = document.createElement("form");
    form.setAttribute("method", method);
    form.setAttribute("action", path);

    for(var key in params) {
        //writeln("key: " + key + " value: " + params[key]);
        var hiddenField = document.createElement("input");
        hiddenField.setAttribute("type", "hidden");
        hiddenField.setAttribute("name", key);
        hiddenField.setAttribute("value", params[key]);

        form.appendChild(hiddenField);
    }

    document.body.appendChild(form);    // Not entirely sure if this is necessary
    form.submit();
}

function writeln(text){
       if (document.getElementById('resultsText') == undefined){
           document.writeln(text);
       }else{
           document.getElementById('resultsText').value =
               document.getElementById('resultsText').value + text + "\n";
       }

}
