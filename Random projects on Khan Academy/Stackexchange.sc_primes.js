/**INSPIRED BY: https://math.stackexchange.com/questions/1024969/sheldon-cooper-primes**/
/*NOTE: all printed numbers are in base-10, they satisfy the relevant properties when transformed into the correct base.*/

var fastcount = true; //PRELOADS PRIME LIST, set false if using large upper caps (> 180,000)

var base = 10;
var convbase = 2;
var uppercap = 99999;

var currenttest = 2;
var currentnum = 1;
var prime_index = 0;

var digitsreverse = [];
var digits = [];
var arrmirror = [];
var inv_digits = 0;
var prod = 1;

var yes_primes_indexed = 0;

var yes_arraysequal = 1;
var yes_palin = 0;
var yes_prime = 1;
var yes_emirp = 0;

var yes_specemirp = 0;
var yes_digitprod = 0;
var yes_binpalin = 0;
var yes_scprime = 0;

var prime_list = [];
var emirp_list = [];
var specemirp_list = [];
var digitprod_list = [];
var binpalin_list = [];
var scprime_list = [];

var mirrorarray = function(digs){
    arrmirror = [];
    for (var i = 0; i <= digs.length - 1; i++){
        arrmirror[i] = digs[digs.length - 1 - i];
    }
    return arrmirror;
};
var listdigitsinbase = function(num, b){
    digitsreverse = [];
    digits = [];
    while (num > 0){
        digitsreverse[digitsreverse.length] = num % b;
        num = (num - num % b)/b;
    }
    digits = mirrorarray(digitsreverse);
    return digits;
};
var inv_listdigitsinbase = function(digs, b){
    inv_digits = 0;
    for (var d = 0; d <= digs.length - 1; d+=1){
        inv_digits += digs[d]*pow(b, digs.length - 1 - d);
    }
    return inv_digits;
};
var mirrornum = function(num){
    return inv_listdigitsinbase(mirrorarray(listdigitsinbase(num, base)), base);
};
var check_arraysequal = function(digs1, digs2){
    yes_arraysequal = 1;
    for (var l = 0; l <= max(digs1.length, digs2.length) - 1; l++){
        if (digs1[l] !== digs2[l]){yes_arraysequal = 0;}
    }
    return yes_arraysequal;
};
var check_palindrome = function(digs){
    return check_arraysequal(digs, mirrorarray(digs));
};
var check_prime = function(num){
    yes_prime = 1;
    if (num === 0){yes_prime = 0;}
    if (num === 1){yes_prime = 0;}
    for (var t = 2; t <= sqrt(num); t++){
        if (num % t === 0){yes_prime = 0;}
    }
    return yes_prime;
};
var check_emirp = function(num){
    yes_emirp = 0;
    if (check_prime(num) === 1 && check_prime(mirrornum(num)) === 1){
        yes_emirp = 1;
    }
    return yes_emirp;
};
var position = function(num){
    for (var s = 0; s <= prime_list.length - 1; s++){
        if (prime_list[s] === num){return s + 1;}
    }
};
var check_specemirp = function(num){
    if (mirrornum(position(num)) === position(mirrornum(num))){
        return 1;
    }
    else {return 0;}
};
var digitprod = function(num, b){
    prod = 1;
    for (var e = 0; e <= listdigitsinbase(num, b).length - 1; e++){
        prod *= listdigitsinbase(num, b)[e];
    }
    return prod;
};
var check_digitprod = function(num, b){
    if (digitprod(num, b) === position(num)){return 1;}
    else {return 0;}
};

//PRE-GENERATE PRIME LIST

if (fastcount === true){
    for (var z = 2; z <= uppercap; z++){
        if (check_prime(z) === 1){
            prime_list[prime_list.length] = z;
        }
    }
}


var draw = function() {
    if (fastcount === false && yes_primes_indexed === 0){
        if (check_prime(currenttest) === 1){
            prime_list[prime_list.length] = currenttest;
        }
        currenttest += 1;
        if (currenttest > uppercap){yes_primes_indexed = 1;}
        frameRate(6000000000000000000000000000000000000000000000000000000000000);
        fill(0, 0, 0);
        background(255, 255, 255);
        text("Indexing primes... (up to "+uppercap+")", 115-1.36*listdigitsinbase(uppercap, 10).length, 175.2);
        text("Indexing primes... (up to "+uppercap+")", 115-1.36*listdigitsinbase(uppercap, 10).length, 175.2);
        text(currenttest, 200-3.4*listdigitsinbase(currenttest, 10).length, 195.2);
        text("Listing of special primes will commence once indexing is done", 35.2, 215.2);
        text("To speed up indexing, reduce 'uppercap'", 92, 235.2);
    }
    if (fastcount === true || yes_primes_indexed === 1){
        currentnum = prime_list[prime_index];
        if (check_emirp(currentnum) === 1){
            emirp_list[emirp_list.length] = currentnum;
            if (check_specemirp(currentnum) === 1){
                specemirp_list[specemirp_list.length] = currentnum;
                yes_specemirp = 1;
            }
        }
        if (check_digitprod(currentnum, base) === 1){
            digitprod_list[digitprod_list.length] = currentnum;
            yes_digitprod = 1;
        }
        if (check_palindrome(listdigitsinbase(currentnum, convbase)) === 1){
            binpalin_list[binpalin_list.length] = currentnum;
            yes_binpalin = 1;
        }
        if (yes_specemirp === 1 && yes_digitprod === 1 && yes_binpalin === 1){
            scprime_list[scprime_list.length] = currentnum;
            yes_scprime = 1;
        }
        prime_index += 1;
        yes_specemirp = 0;
        yes_digitprod = 0;
        yes_binpalin = 0;
        yes_scprime = 0;
        frameRate(6000000000000000000000000000000000000000000000000000000000000);
        
        fill(0, 0, 0);
        background(255, 255, 255);
    
        text("BASE "+base+", CONV-BASE "+2, 140, 80);
        text("BASE "+base+", CONV-BASE "+2, 140, 80);
        text("Emirps: ", 50, 100);
        text("Special emirps: ", 10, 120);
        text("Digit product ok: ", 5, 140);
        text("Conv palindrome: ", 0, 160);
        text("S Cooper prime: ", 5, 180);
    
        text(emirp_list, 100, 100);
        text(specemirp_list, 100, 120);
        text(digitprod_list, 100, 140);
        text(binpalin_list, 100, 160);
        text(scprime_list, 100, 180);
        
        text(currentnum, 200-3.4*listdigitsinbase(currentnum, 10).length, 195.2);
    }
};