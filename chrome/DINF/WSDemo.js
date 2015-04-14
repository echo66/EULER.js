/**
  * Author: Guido J.M. Naudts Bouwel
  */
function startWSDemo(){
    netscape.security.PrivilegeManager.enablePrivilege("UniversalXPConnect");
    var ps = Components.classes["@mozilla.org/embedcomp/prompt-service;1"]
         .getService(Components.interfaces.nsIPromptService);
    var rv = ps.confirmEx(window, "Demo WS", "Attention!! This demo will clear the screen.\n"
                      + "Continue? ",
                          ps.BUTTON_TITLE_IS_STRING * ps.BUTTON_POS_0 +
                          ps.BUTTON_TITLE_IS_STRING * ps.BUTTON_POS_1,
                          "Yes", "No", null, null, {});
    // rv = 0 if "Yes"; rv = 1 if "No"
    if ( rv == 1){
        return;
    }

    application.clearSource();
    application.clearMessages();
    application.clearQuery();
    alert("This demo will show how to create a webservice and then how to,\n" +
          "execute a query on it.\n" +
          "Some knowledge of Notation 3 (N3) is necessary.See:\n" +
          "http://www.w3.org/2000/10/swap/Primer\n" +
          "For a good intro to web services, see:\n" +
          "http://www.w3schools.com/webservices/default.asp\n"  );
    alert("First we load the N3 file with the menu \"Source code\"\n"+
            "and then \"Open\" and select the file \"business.n3\"\n" +
            "In the message zone you will see the messages eg:\n"+
            "File selected = D:\\assoc\\eulermoz\\rdftest\\testcases\\business.n3\n"+
            "File opened: D:\\assoc\\eulermoz\\rdftest\\testcases\\business.n3\n" +
            "Alternatively you can enter a N3 source in the textarea.");

    document.getElementById("sourceText").value += readAFile(getBasePath(),"testcases\\business.n3");
    writeMessage("File selected = " + getBasePath() + "testcases\\business.n3\n");
    writeMessage("File opened: " +  getBasePath() + "testcases\\business.n3\n");

    alert("Then we select from the menu 'Web Services' the item 'Save Web Service'.\n"
            + "This actually just puts the file in the wsApps directory.\n"
            + "Now the web service is created!!")

    alert("Then we type in a query.\n"
            + "You can also get a query by loading a query file and select a query from this file");
    document.getElementById("querySource").value =
           "@prefix : <http://test#>.\n" +
           "?who :hasReduction ?x.";

    alert("We then select from menu 'Web Services' the item 'Query Web Service'\n" +
            "and get the results  in the results zone.\n" +
            "For the name of the web service enter: business\n" +
            "For the other parameters just take the default.\n" +
            "Attention!! The window where you must enter the name of the web service \n" +
            "could be minimized.");

    queryWS();

    alert("Now you will se the solution of the query in the output zone.\n");


    //saveQuery();


}