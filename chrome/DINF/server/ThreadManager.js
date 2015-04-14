/*
 * A thread object has: a threadID, a function object with functions
 * ini, next and final, and a priority (default 2) and a priority state
 * Author: Guido J.M. Naudts Secretarisdreef Bouwel
 */

function ThreadManager(){
    this.threadCounter = 0;
    this.threadList = [];
    this.highestPriority = 2;
    this.lowestPriority = 2;
    this.stop = false;
    this.currentThread;
    this.busy = false;

    //writeln("ThreadManager!!!!!!!!");
    
    this.createThread = function(threadObject, priority ){
        var cpr;
        if ( priority == "high"){
            cpr = 3;
        }else if ( priority == "low"){
            cpr = 1;
        }else{
            cpr = 2;
        }

        this.threadCounter++;
        threadObject.threadID = this.threadCounter;
        var thread = new Thread(this.threadCounter, cpr, threadObject);

        if ( cpr < this.lowestPriority){
            this.lowestPriority = cpr;
        }
        if ( cpr > this.highestPriority){
            this.highestPriority = cpr;
        }
        threadObject.ini();
        this.threadList.push( thread );
        thread.initialized = true;

        //writeln("thread created! " + this.threadList.length);

        return this.threadCounter;

    };

    /*
     * execute for each thread the next step, if the priority admits it.
     */
    this.schedule = function(){
       var interval;

       var result;
       var thread;
       var threadObject;
       if (this.busy){
           return;
       }
       this.busy = true;
       if ( this.threadList != null){
           for ( var i = 0; i < this.threadList.length; i++ ){
               thread = this.threadList[i];
               if ( ! thread.initialized ){
                   break;
               }
               if (checkThread(thread)){
                   thread.priorityState++;
                   interval = this.highestPriority  - this.lowestPriority;
                   //writeln("state = " + thread.priorityState + " interval = " + interval);

                   if ( thread.priorityState > interval){
                       thread.priorityState = thread.priority -1 ;
                       this.currentThread = thread;
                       result = thread.threadObject.next().next();
                       //writeln("ThreadManager.schedule result: " + result);

                       if ( result){ //thread.threadObject.next() ){
                           thread.threadObject.final();
                           this.threadList.splice(i, 1);
                       }
                   }
               }
           }
       }
       this.busy = false;
    };

    this.sleep = function(millis){
        var time = new Date();
        this.currentThread.wakeup = time.getTime() + millis;

    };

    this.setPriority = function(threadID, priority){
        //writeln("setPriority threadID = " + threadID + " priority " + priority);
        var cpr;
        if ( priority == "high"){
            cpr = 3;
        }else if ( priority == "low"){
            cpr = 1;
        }else{
            cpr = 2;
        }
        if ( cpr < this.lowestPriority){
            this.lowestPriority = cpr;
        }
        if ( cpr > this.highestPriority){
            this.highestPriority = cpr;
        }
        for (var i = 0; i < this.threadList.length; i++){
            thread = this.threadList[i];
            //writeln("for " + thread.threadID);
            if (thread.threadID == threadID){
                 //writeln("priority changed to " + cpr);
                thread.priority = cpr;
                thread.priorityState = cpr -1;
                break;
            }
        }


    };

}

function checkThread(thread){
    var time = new Date();
    if (thread.wakeup > time.getTime()){
        return false;
    }
    thread.wakeup = 0;
    return true;
}

      /**
       * Netscape compatible WaitForDelay function.
       * parameters:
       * (Number) delay in millisecond
      */
      function nsWaitForDelay(delay) {
          netscape.security.PrivilegeManager.enablePrivilege("UniversalXPConnect");
          // Get the current thread.
          var thread = Components.classes["@mozilla.org/thread-manager;1"].getService(Components.interfaces.nsIThreadManager).currentThread;
          // Create an inner property to be used later as a notifier.
          this.delayed = true;
          /* Call JavaScript setTimeout function
           * to execute this.delayed = false
           * after it finishes.
           */
           setTimeout("this.delayed = false;", delay);
           /**
            * Keep looping until this.delayed = false
            */
          while (this.delayed) {
          /**
            * This code will not freeze your browser as it's documented in here:
            * https://developer.mozilla.org/en/Code_snippets/Threads#Waiting_for_a_background_task_to_complete
            */
            thread.processNextEvent(true);
          }
      }

function Thread(threadID, priority, threadObject){
    this.threadID = threadID;
    this.priority = priority;
    this.threadObject = threadObject;
    this.priorityState = priority - 1;
    this.wakeup = 0;
    this.initialized = false;
};