function WSclient(){
    /**
      * Author: Guido J.M. Naudts Bouwel
      */


    this.soapPart1 =  "<soap:Envelope " +
                          "xmlns:soap='http://www.w3.org/2001/12/soap-envelope' " +
                          "soap:encodingStyle='http://www.w3.org/2001/12/soap-encoding'>" +
                          "<soap:Body xmlns:em='http://eulermoz/soap#'>";

    this.soapPart2 =  "</soap:Body>" +
                         "</soap:Envelope>";

    this.exampleRequest =  "<em:Query> <em:Application>authen</em:Application>" +
                              "@prefix : &lt;authen#&gt;.\n" +
                              "?who :authenticated ?mailinglist." +
                           "</em:Query>";

    /**var soapExample1 =  "<soap:Envelope " +
     "xmlns:soap='http://www.w3.org/2001/12/soap-envelope' " +
     "soap:encodingStyle='http://www.w3.org/2001/12/soap-encoding'>" +
     "<soap:Body xmlns:em='http://eulermoz/soap#'>" +
     "<em:Query> <em:Application>authen</em:Application>" +
     "@prefix : <authen#>;.\n" +
     "?who :authenticated ?mailinglist." +
     "</em:Query>" +
     "</soap:Body>" +
     "</soap:Envelope>"; */
    /**
     * <em:Query> <em:Application>authen</em:Application>
     * <em:ObjectString/>
     * MailingList
     *
     * </em:Query>
     *
     * <em:ObjectString> means that the recieving server will replace MailingList
     * with: [em:ObjectString "MailingList"].
     * This can then match with a rule eg
     * { some antecedents } => {[em:ObjectString "MailingList"]}.
     * (The same mechanism will be used in the output of the server ie
     * if the result of the query is: [em:ObjectString "some_string"].
     * only the string will be returned in the response.
     */


    /**
     * The request is the part between <em:Query> and </em.query>
     * We use xmlHttpRequest for sending to the server
     */
    this.send = function(request, destination, caller) {
        netscape.security.PrivilegeManager.enablePrivilege("UniversalXPConnect");

       var xmlhttp = new XMLHttpRequest();
       try{
        var content = this.soapPart1 + request + this.soapPart2 + "\n\n";
        writeln("destination = " + destination);
        xmlhttp.open("POST", destination, true);
        xmlhttp.setRequestHeader('Content-Length', content.length);
        //xmlhttp.overrideMimeType('text/html');
        xmlhttp.onreadystatechange = function() {
            writeln("readystate = " + xmlhttp.readyState);
            if (xmlhttp.readyState == 4) {
                writeln("OK readyState4: ");
                writeln("Response: " + xmlhttp.responseText);
                // caller.soapRecieved(xmlhttp.responseText);
                xmlhttp = null;
            }
        };
        // Set request headers for message to send. Depends on the web service

        //xmlhttp.setRequestHeader('Content-Type',  'text/plain');

       // xmlhttp.setRequestHeader('SOAPAction', '');
        writeln("content = " + content);
        // Send request using POST
        //xmlhttp.sendAsBinary(content);
        xmlhttp.sendAsBinary(content);
        //writeln("response: " + xmlhttp.responseText);
       /* var request = "POST";
        var mode = request?"POST":"GET";
        xmlhttp.open(mode,url,true);
        if(mode=="POST"){http.setRequestHeader('Content-Type','application/x-www-form-urlencoded');}

        http.send(request);*/

        writeln("request sent");
        delete xmlhttp;
        }
         catch(exception) {
            writeln("response  : " + xmlhttp.responseText);

            writeln("WSclient.send: " + exception)
        }
    };


    this.testXmlHttpRequest = function() {
        try {
            netscape.security.PrivilegeManager.enablePrivilege("UniversalXPConnect");
            var xmlhttp = new XMLHttpRequest();
            xmlhttp.open('GET', 'http://www.yahoo.com/', true);
            //xmlhttp.open('GET', 'http://localhost:6673/help.sjs', true);
            if (xmlhttp.overrideMimeType)
                 xmlhttp.overrideMimeType('text/html');
            xmlhttp.onreadystatechange = function() {
                if (xmlhttp.readyState == 4) {
                    writeln("OK readyState4: " + xmlhttp.getAllResponseHeaders());
                    writeln("status = " + xmlhttp.status);
                    writeln("Response: " + xmlhttp.responseText);
                    // caller.soapRecieved(xmlhttp.responseText);
                }
            };
            xmlhttp.send(null);
        } catch(exception) {
            writeln("WSclient.testXmlHttpRequest: " + exception)
        }

    };

    this.testWithGet = function(){
        this.sendWithGet(this.exampleRequest, "http://127.0.0.1", "");

    };

    this.test = function() {
        this.send(this.exampleRequest, "http://127.0.0.1", "");
    };

}