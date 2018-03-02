

function syncloadsubmlfile (fn) {
    var req = new XMLHttpRequest();
    req.open('GET', "subml/" + fn, false);
    req.send(null);
    if(req.status == 200)
      return(req.responseText);
}

importScripts("subml.js");
