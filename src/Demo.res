module Lambda = {
  type rec t = 
    | Var (string)
    | App (t, t)
    | Fun (string, t)

  let rec toString = (t : t) :string => {
    switch t {
      | Var(x) => x
      | App(m, n) => "(" ++ toString(m) ++ toString(n) ++ ")"
      | Fun(f, arg) => "(λ" ++ f ++ "." ++ toString(arg)++")"
    }
  }

  let rec equal = (s:t ,t: t) : bool => {
    switch (s,t) {
    | (Var(a), Var(b)) => a == b 
    | (App(m, n), App(p, q)) => equal(m, p) && equal(n, q)
    | (Fun(f, a), Fun(g, b)) => f == g && equal(a, b)
    | _ => false
    }
  }

  let rec getFreeVariables = (t: t): list<string> => {
    switch t {
    | Var(x) => list{x}
    | App(m, n) => Belt.List.concatMany([getFreeVariables(m), getFreeVariables(n)])
    | Fun(f, arg) => getFreeVariables(arg)->Belt.List.keep((x)=> x != f)
    }
  }
  
  let nameOrder = ref(0)
  // get a new name "@i", where i comes from a mutable int
  let getNewname = () : string => {
    nameOrder := nameOrder.contents + 1
    "@" ++ Js.Int.toString(nameOrder.contents)
  }

// When va contains unbounded variable with the same name of bounded varaibles in body,
// conflicts will occur.
// Solution: assign new name to those bounded varaiables in body which share the same names of unbounded variables.
  let rec subst = (x: string, va:t, body: t) : t => {
    switch body {
      | Var(a) if a == x => va
      | Var(_) => body
      | App(m, n) => App(subst(x, va, m), subst(x, va, n))
      | Fun(f, arg) => if Belt.List.has(getFreeVariables(va),f,String.equal) {
        let newSym = getNewname()
        let newArg = subst(f,Var(newSym),arg)
        if f == x {
          Fun(newSym,subst(newSym,va,newArg))
        }
        else {
          Fun(newSym, subst(x, va, newArg))
        }
      } 
      else {
        if f == x {
          body
        }
        else {
          Fun(f, subst(x, va, arg))
        }
      }
    }
  } 

  let rec eval = (t: t) => {
    switch t {
    | Var(_) => t
    | Fun(x, body) => Fun(x, eval(body))
    | App(f, arg) => {
        switch eval(f) {
        | Fun(x, body) => {
          let va = eval(arg)
          eval(subst(x, va, body))
          }
        | k => App(k, eval(arg))
        }
      }  
    }
  }


}

let input = {
  open Lambda
  Fun("x",Var("x"))
  // App(Fun("x",App(Var("x"),Var("x"))),Fun("y",App(Var("y"),Var("y"))))
  // App(Fun("x",Var("y")),App(Fun("z",App(Var("z"),Var("z"))),Fun("w",Var("w"))))
}
Js.log(Lambda.toString(input))

let output = {
  open Lambda
  eval(input)
}

Js.log(Lambda.toString(output))

let omega = {
  open Lambda
  let smallOmega = Fun("x",App(Var("x"),Var("x")))
  App(smallOmega, smallOmega)
}

Js.log(Lambda.toString(omega))


let ycomb = {
  open Lambda
  Fun("f",App(Fun("x",App(Var("f"),App(Var("x"),Var("x")))),Fun("x",App(Var("f"),App(Var("x"),Var("x"))))))
}

Js.log(Lambda.toString(ycomb))

let succ = {
  open Lambda
  Fun("n",Fun("f",Fun("x",App(Var("f"),App(App(Var("n"),Var("f")),Var("x"))))))
}

let zero = {
  open Lambda
  Fun("f",Fun("x",Var("x")))
}

let one = {
  open Lambda
  Fun("f",Fun("x",App(Var("f"),Var("x"))))
}

let toChurchNum = (n :int) => {
  let rec helper = (n : int, churchNum: Lambda.t) : Lambda.t => 
    if n < 0 {assert false}
    else {
      switch n {
        | 0 => churchNum
        | _ => helper(n-1, App(succ,churchNum))
      }
    }
  helper(n,zero)
}

let numbers = {
  list{
    toChurchNum(0),
    toChurchNum(1),
    toChurchNum(2),
    toChurchNum(3),
    toChurchNum(4),
    toChurchNum(5)
  }
}

List.iter((x)=>(Js.log(Lambda.toString(Lambda.eval(x)))), numbers)

let mul = {
  open Lambda
  Fun("n",Fun("m",App(Var("m"),Var("n"))))
}

let if_then_else = {
  open Lambda
  Fun("t",Fun("x",Fun("y",App(App(Var("t"),Var("x")),Var("y")))))
}

let trueC = {
  open Lambda
  Fun("x",Fun("y",Var("x")))
}

let falseC = {
  open Lambda
  Fun("x",Fun("y",Var("y")))
}

let add = {
  open Lambda
  Fun("n",Fun("m",Fun("f",Fun("x",App(App(Var("n"),Var("f")),App(App(Var("m"),Var("f")),Var("x")))))))
}

let iszero = {
  open Lambda
  Fun("n",App(App(Var("n"),Fun("z",falseC)),trueC))
}

let pair = {
  open Lambda
  Fun("x",Fun("y",Fun("z",App(App(Var("z"),Var("x")),Var("y")))))
}

let fst = {
  open Lambda
  Fun("p",App(Var("p"),trueC))
}

let snd = {
  open Lambda
  Fun("p",App(Var("p"),falseC))
}


let pred = {
  open Lambda
  Fun("n",App(
    fst,
    App(
      App(
        Var("n"),
        Fun("p",App(
          App(pair,App(
            snd,
            Var("p"))),
          App(succ,App(
            snd,
            Var("p")))))),
      App(
        App(
          pair,
          zero),
        zero))))
}

List.iter((x)=>(Js.log(Lambda.toString(Lambda.eval(App(pred,x))))), numbers)

let mulR = {
  open Lambda
  let f = {
    Fun("f",Fun("n",Fun("m",App(App(App(if_then_else,App(iszero,Var("n"))),zero),App(App(add,Var("m")),App(App(Var("f"),App(pred,Var("n"))),Var("m")))))))
  }
  App(Fun("Y",App(Var("Y"),f)),ycomb)
}

let mul2by2 = {
  open Lambda
  App(App(mulR,toChurchNum(2)),toChurchNum(2))
}
