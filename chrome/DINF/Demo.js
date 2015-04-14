/**
  * Author: Guido J.M. Naudts Bouwel
  */

function startDemoDinf(){
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
    
    alert("This demo will show how to load a N3 sourcefile,\n" +
          "execute a query on it and then save source + query(ies)\n" +
          "as an application.\n" +
          "Some knowledge of Notation 3 (N3) is necessary.See:\n" +
          "http://www.w3.org/2000/10/swap/Primer"  );
    alert("First we load the N3 file with the menu \"Source code\"\n"+
            "and then \"Open\" and select the file \"business.n3\"\n" +
            "In the message zone you will see the messages:\n"+
            "File selected = D:\\assoc\\eulermoz\\rdftest\\testcases\\business.n3\n"+
            "File opened: D:\\assoc\\eulermoz\\rdftest\\testcases\\business.n3");

    document.getElementById("sourceText").value += readAFile(getBasePath(),"testcases\\business.n3");
    writeMessage("File selected = " + getBasePath() + "testcases\\business.n3\n");
    writeMessage("File opened: " +  getBasePath() + "testcases\\business.n3\n");

    alert("Then we type in a query.\n");
    document.getElementById("querySource").value =
           "@prefix : <http://test#>.\n" +
           "?who :hasReduction ?x.";

    alert("We then execute the query with the button 'execute' \n" +
            "and get the results  in the results zone.\n");

    executeQuery();

    alert("We can copy the query to the list \"query menu list\".\n" +
            "There we make a collection of queries than can be saved to disk.\n" +
            "The system will ask a name for the query.\n" +
            " You can chose the default name.\n" +
            "Attention! The query window may be minimized!");

    addQuery();

    alert("Now we can save all the info we got into an application.\n" +
          "Therefore we open menu item 'Apps' and select 'Save App'.\n" +
          "If no application name is known the program will ask for an application name.\n" +
          "Here the name is already known and the program will select some " +
          "suitable defaults.\n" );

    saveQueryFile();


}