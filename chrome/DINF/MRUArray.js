function MRUArray( mruSize, initialData){
    /**
      * Principles: the last selected item becomes the last element of the array; others go one backwards
      * The number of elements is limited to size.
      * An added element becomes the last ( it is a stack; the most recently used
      * element is the last ).
      * Author: Guido J.M. Naudts Bouwel
      */

    this.mruArray = initialData;

    this.mruSize = mruSize;

    this.getElement = function(name){

        var outs = "";
        var newArray = [];
        var s;
        //writeln("name = " + name);
        for( var i = 0 ; i <   this.mruArray.length; i++ ){
            s = this.mruArray[i];

            if ( s == name){
                //writeln("s= " + s);
                outs = s;
            }else if (s != undefined && s != ""){
                newArray.push(s);
            }

        }
        //writeln("***MRUArray.getElement mruArray: " + this.mruArray + "outs: " + outs);
        //writeln("MRUArray.getElement mruArray length: " + this.mruArray.length + " mruSize: " + this.mruSize);
        if ( outs == "" && this.mruArray.length < this.mruSize ){
            newArray.push (name);
        }else if (this.mruArray.length < this.mruSize){
            newArray.push( outs );
        }else{
            newArray.shift();
            newArray.push( outs );
        }

        this.mruArray = newArray;
        //writeln("***MRUArray.getElement mruArray: " + this.mruArray);
        return outs;
    };

    this.deleteElement = function(name){
        var newArray = [];
        for( var i = 0 ; i <   this.mruArray.length; i++ ){
            s = this.mruArray[i];
            if ( s != name){
                newArray.push(s);
            }

        }
        this.mruArray = newArray;
    };


    this.addElement = function(name){
        this.getElement(name);
    };

    this.saveArray = function(fileName){
        // got to save the MRU (most recently used) list
        var params = new Parameter();
        for(var k = 0; k < this.mruArray.length; k++ ){
            params.addParameter("MRU" + k, this.mruArray[k] );
        }
        //writeMessage("MRUArray.saveArray mruArray: " + this.mruArray + "\n")
        //writeMessage("MRUArray.saveArray Parameters: " + params.parameters + "\n");
        params.saveParameterFileP(fileName);
    };

    this.restoreArray = function(fileName){
        var params = new Parameter();
        params.readParameterFile2(fileName);
        //writeln("filename::: " + fileName);
        //writeMessage("MRUArray.restoreArray params read: " +
        //             mapToString(params.parameters) + "\n");
        var mrus = params.getAll();

        this.mruArray = [];
        for (var key in mrus){
            this.getElement(mrus[key]);
        }
    };


    this.test = function(){
        this.getElement("elem1");
        this.getElement("elem2");
        this.getElement("test");
        this.getElement("elem2");
        this.writeln("Array: " + this.mruArray);
    };

    this.writeln = function(text){
       document.getElementById('resultsText').value =
           document.getElementById('resultsText').value + text + "\n";

    };
}
