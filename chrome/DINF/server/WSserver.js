
		/*
		 * server for the Web Service. The client sends a message to the server. The server
		 * accepts the messages.
		 * Threaded version.
		 *
         * Author: Guido J.M. Naudts Bouwel
     	 */

netscape.security.PrivilegeManager.enablePrivilege("UniversalXPConnect");
var threadManager;


function WSserver(){


    this.serverSocket;

    //this.threadManager;

    this.port = 80;


    this.start = function()
    {

        netscape.security.PrivilegeManager.enablePrivilege("UniversalXPConnect");

        var listener =
        {

            onSocketAccepted : function(socket, transport)
            {
                try {
                    netscape.security.PrivilegeManager.enablePrivilege("UniversalXPConnect");
                    writeln("On socket accepted");
                    // must start a client  now
                    var newClient = new client(transport, 0);
                    var threadID = threadManager.createThread(newClient);
                    /* if (threadID == 1){
                        threadManager.setPriority(1, "high");
                    }else{
                        threadManager.setPriority(threadID, "low");
                    }*/

                } catch(ex2) {
                    writeln("onSocketAccepted exception: " + ex2 + "\n");
                }
            },

            onStopListening : function(socket, status) {
                netscape.security.PrivilegeManager.enablePrivilege("UniversalXPConnect");
                socket.close();
            }
        };

        try {
            netscape.security.PrivilegeManager.enablePrivilege("UniversalXPConnect");
            threadManager = new ThreadManager();
            this.serverSocket = Components.classes["@mozilla.org/network/server-socket;1"]
                    .createInstance(Components.interfaces.nsIServerSocket);
            writeln("serverSocket created");
            this.serverSocket.init(this.port, false, -1);
            writeln("serverSocket initialized");
            this.serverSocket.asyncListen(listener);
            writeln("listener started");
            schedule(threadManager);
        } catch(ex) {
            writeln("start() exception: " + ex);
        }


        writeln("\nSERVER STARTED\n");
    };



    this.stop = function()
    {
        netscape.security.PrivilegeManager.enablePrivilege("UniversalXPConnect");
        this.serverSocket.close();

        writeln("\nSERVER STOPPED\n");
    };


}

function client(transport, threadID) {
            netscape.security.PrivilegeManager.enablePrivilege("UniversalXPConnect");
            this.outstream = transport.openOutputStream(0, 0, 0);
            this.ro = new readObject(transport);
            this.result = 0;
            this.counter = 0;
            this.maxCount = 20;
            this.data;
            this.webService = new WebService();

            this.ini = function() {

                try {
                    this.ro.init();
                    writeln("Thread " + this.threadID + " is ready to work.\n");
                } catch(err) {
                    writeln("Client " + this.threadID + " ini() exception: " + err + "\n");
                }

            };

            this.final = function() {
                try {
                    // got to send the response
                    var req = this.webService.extractXML(this.data);
                    var resp = this.webService.acceptSoap(req);
                    var sols = resp[1];
                    writeln("Client " + this.threadID + " solutions: " + sols + "\n");
                    var appli = resp[0];
                    var resp = this.webService.makeResp(appli, sols);
                    writeln("Client " + this.threadID + " response: " + resp + "\n");
                    netscape.security.PrivilegeManager.enablePrivilege("UniversalXPConnect");
                    this.outstream.write(resp, resp.length );
                    this.outstream.close();
                    this.ro.close();
                    //transport.close("EOT");
                } catch(err) {
                    writeln("Client " + this.threadID + " final() exception: " + err + "\n");
                }
            };

            this.next = function() {
                try {
                    // do something with the data
                    writeln("Thread " + this.threadID + " function next()\n");

                    this.data = this.ro.read();
                    writeln("Thread " + this.threadID + " recieved:\n " + this.data + "\n");
                    if ( this.data == undefined){
                        yield false;
                        // continues the loop
                    }else{
                        yield true;
                    }
                    // after this yield, this.final is executed.
                } catch(err) {
                    writeln("Client " + this.threadID + " next() exception: " + err + "\n");
                }
            };

        }


