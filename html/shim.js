

function Magic(name, obj) {
    return new Proxy(obj, {
        get(target, key, receiver) {
            console.log('get',name,key)
            if (!(key in target))
                throw new Error(`Miss ${key} in ${name}`)
            return Reflect.get(...arguments)
        }
    })
}

function Buffer() {
    
}

Buffer.prototype = {
    toString() {
        return new TextDecoder().decode(this)
    },
    slice(s,e) {
        let rval = this.subarray(s,e)
        Object.setPrototypeOf(rval, Buffer.prototype)
        return rval
    },
    
}

Object.setPrototypeOf(Buffer.prototype, Uint8Array.prototype)

Buffer.alloc = function(size) {
    console.log('alloc',size)
    let rval = new Uint8Array(size)
    Object.setPrototypeOf(rval, Buffer.prototype)
    return rval
}
Buffer.concat = function([a,b]) {
    let rval = new Uint8Array(a.length + b.length)
    rval.set(a)
    rval.set(b,a.length)
    Object.setPrototypeOf(rval, Buffer.prototype)
    return rval
}

let filesystem = {}
const enc = new TextEncoder('utf8')
function loadString(name, str) {
    filesystem[name] = enc.encode(str)
}

let shim = {
    os: {
        platform() { return "webshim" }
    },
    fs: {
        openSync(fn, mode) {
            return {fn, mode, pos: 0}
        },
        fstatSync({fn,mode,pos}) {
            console.log('fstatsync', filesystem[fn].length)
            return {size:filesystem[fn].length}
        },
        readSync(fd, buf, pos, len) {
            // no input for now, we can't do this sync and be interactive..
            // We throw because tinyidrisv2 doesn't exit on eof
            if (fd === 0) throw new Error("No stdin")
            let fbuf = filesystem[fd.fn]
            let end = pos + len
            let i = 0
            while (i < len && fd.pos < fbuf.length) {
                buf[pos + i++] = fbuf[fd.pos++]
            }
            return i
        },
        closeSync(fd) {
            // No-op
        },
    },
}
for (let name in shim) {
    shim[name] = Magic(name, shim[name])
}
function require(name) {
    console.log('required', name)
    return shim[name]
}

loadString('examples/tt/testpair.tt',`
data T : Type where {
    MkT : pi x : Integer . pi y : Integer . pi z : Integer . T
}

proj1 : pi x : T . Integer;
proj1 = lam x . case x of
                 MkT i j k => i;

proj2 : pi x : T . Integer;
proj2 = lam x . case x of
                 MkT i j k => j;

proj3 : pi x : T . Integer;
proj3 = lam x . case x of
                 MkT i j k => k;

proj1 (MkT 1 2 3);
proj2 (MkT 1 2 3);
proj3 (MkT 1 2 3);

data Pair : pi a : Type . pi b : Type . Type where {
    MkPair : pi a : Type . pi b : Type .
             pi x : a .    pi y : b . Pair a b
}

fst : pi a : Type . pi b : Type . pi p : Pair a b . a;
fst = lam a . lam b . lam p .
        case p of
             MkPair a' b' x y => x;

data Bool : Type where {
   False : Bool
 | True : Bool
}

fst Bool Integer (MkPair Bool Integer False 94);


2 ;

`)

loadString('examples/tt/testraw.tt',`
data Bool : Type where {
    False : Bool 
  | True : Bool
}

data Nat : Type where {
   Z : Nat
 | S : pi k : Nat . Nat
}

not : pi x : Bool . Bool;
not = lam x . case x of
                 False => True
               | True => False;

not True;
not False;

plus : pi x : Nat . pi y : Nat . Nat;
plus = lam x. lam y . 
           case x of
              Z => y
            | S k => S (plus k y);

plus (S (S Z)) (S (S (S Z)));


intToNat : pi x : Integer . Nat;
intToNat = lam x . case x of
                        0 => Z
                      | _ => S (intToNat (prim__sub_Integer x 1));


prim__sub_Integer 5 1;
intToNat 5;
intToNat;

natToInt : pi x : Nat . Integer;
natToInt = lam x . case x of
                      Z => 0
                    | S k => prim__add_Integer (natToInt k) 1;

natToInt (S (S Z));
prim__add_Integer 1 (prim__add_Integer (prim__add_Integer 1 1) 2);

(lam x . plus (S (S x)) (S (S x))  : pi x : Nat . Nat);
natToInt (plus (intToNat 50000) (intToNat 40000));
`)


loadString('shorter.tt', `
data Nat : Type where {
    Z : Nat
  | S : pi k : Nat . Nat
 }
 
plus : pi x : Nat . pi y : Nat . Nat;
plus = lam x. lam y . 
           case x of
              Z => y
            | S k => S (plus k y);

plus (S (S Z)) (S (S (S Z)));


intToNat : pi x : Integer . Nat;
intToNat = lam x . case x of
                        0 => Z
                      | _ => S (intToNat (prim__sub_Integer x 1));


prim__sub_Integer 5 1;
intToNat 5;
intToNat;

natToInt : pi x : Nat . Integer;
natToInt = lam x . case x of
                      Z => 0
                    | S k => prim__add_Integer (natToInt k) 1;

natToInt (S (S Z));
prim__add_Integer 1 (prim__add_Integer (prim__add_Integer 1 1) 2);

(lam x . plus (S (S x)) (S (S x))  : pi x : Nat . Nat);
natToInt (plus (intToNat 100) (intToNat 100));
`)

let process = Magic('process',{
    // argv: ['node', 'yaffle.js', 'examples/tt/testpair.tt'],
    argv: ['node', 'yaffle.js', 'shorter.tt'],
    stdout: Magic('stdout',{
        write(stuff) {
            console.log(stuff)
        }
    })
})
