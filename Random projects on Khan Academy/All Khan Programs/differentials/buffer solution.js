//0 = concentration vs. time graph; 1 = equilibrium concentration vs. amt of acid graph
var whattograph = 0; 

//CONCENTRATIONS OF THINGS (VARIABLE) -- don't change the last two, keep first two equal
var weac = 2;    //concentration of weak acid in buffer 
var salt = 2;    //concentration of salt in buffer      
var prot = 0.1; //concentration of protons             
var coba = 0;    //concentration of conjugate base
var meta = 0;    //concentration of metal ions of salt

//RATE CONSTANTS
var acre = 0;   //weak acid reassociation
var acdi = 1; //weak acid dissociation
var sadi = 1;   //salt solution
var sare = 0;   //salt precipitation

//CALCULUS
var t;
var dt = 0.01; //each pixel corresponds to 0.01 seconds
var dw, ds, dp, dc, dm;
var tmax = 4;

//FOR SECOND GRAPH
var protnought;
var dprotnought = 0.01; 
var protnoughtmax = 2*max(weac, salt);

if(whattograph === 0){
    for(t = 0; t < tmax; t = t + dt){
        dw = dt * ( - acre * weac + acdi * coba * prot );
        dp = dt * ( + acre * weac - acdi * coba * prot );
        ds = dt * ( - sadi * salt + sare * coba * meta );
        dm = dt * ( + sadi * salt - sare * coba * meta );
        dc = dm + dp;
        weac = weac + dw;
        prot = prot + dw;
        salt = salt + ds;
        meta = meta + dm;
        coba = coba + dc;
        stroke(0, 0, 0);                         //black for protons
        point(t*400/tmax, 400 - prot*400/tmax);
        stroke(255, 0, 0);                       //red for weak acid
        point(t*400/tmax, 400 - weac*400/tmax);
        stroke(0, 255, 0);                       //green for salt
        point(t*400/tmax, 400 - salt*400/tmax);
        stroke(0, 0, 255);                       //blue for meta
        point(t*400/tmax, 400 - meta*400/tmax);
        stroke(255/3, 255/3, 255/3);             //grey for conjugate base
        point(t*400/tmax, 400 - coba*400/tmax);
    }
    fill(0, 0, 0);
    text("Protons", 350, 415 - prot*400/tmax);
    fill(255, 0, 0);
    text("Weak acid", 330, 400 - weac*400/tmax);
    fill(0, 255, 0);
    text("Salt", 370, 395 - salt*400/tmax);
    fill(0, 0, 255);
    text("Metal cations", 320, 390 - meta*400/tmax);
    fill(255/3, 255/3, 255/3);
    text("Conjugate base", 330, 400 - coba*400/tmax);
}

if(whattograph === 1){
    for(protnought = 0; protnought < protnoughtmax; protnought = protnought + dprotnought){
        prot = protnought;
        for(t = 0; t < 0; t = t + dt){
            dw = dt * ( - acre * weac + acdi * coba * prot );
            dp = dt * ( + acre * weac - acdi * coba * prot );
            ds = dt * ( - sadi * salt + sare * coba * meta );
            dm = dt * ( + sadi * salt - sare * coba * meta );
            dc = dm + dp;
            weac = weac + dw;
            prot = prot + dw;
            salt = salt + ds;
            meta = meta + dm;
            coba = coba + dc;
        }
        stroke(0, 0, 0);                         //black for protons
        point(protnought*400/protnoughtmax, 350 - prot*350/protnoughtmax);
        stroke(255, 0, 0);                       //red for weak acid
        point(protnought*400/protnoughtmax, 350 - weac*350/protnoughtmax);
        stroke(0, 255, 0);                       //green for salt
        point(protnought*400/protnoughtmax, 350 - salt*350/protnoughtmax);
        stroke(0, 0, 255);                       //blue for meta
        point(protnought*400/protnoughtmax, 350 - meta*350/protnoughtmax);
        stroke(255/3, 255/3, 255/3);             //grey for conjugate base
        point(protnought*400/protnoughtmax, 350 - coba*350/protnoughtmax);
    }
}


