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
// Solution: rename bounded varaiables in body with the same name of unbounded variables.
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

  let rec evalOneStep = (t:t) => {
    switch t {
    | Var(_) => t 
    | Fun(x, body) => Fun(x,evalOneStep(body))
    | App(f, arg) => {
      switch evalOneStep(f) {
      | Var(x) => App(Var(x), evalOneStep(arg))
      | App(m, n) => {
        App(App(m, n), arg)
      }
      | Fun(x, body) => {
        let va = evalOneStep(arg)
        subst(x, va, body)
      }
      }
    }
    }
  }

  let rec evalToFixedPoint = (t: t) => {
    let prevStr = toString(t)
    let succStr = toString(evalOneStep(t))
    Js.log("Prev: " ++ prevStr ++" ; Succ: " ++ succStr)
    if prevStr == succStr {
      Js.log("Reached fixed point: " ++ succStr)
      t
    }
    else {
      evalToFixedPoint(evalOneStep(t))
    }
  }

  let rec evalOneStepMem = (t:t, cache :list<(string,t)>) => {
    switch Belt.List.getAssoc(cache,toString(t),String.equal) {
    | Some(a) => {
      Js.log("Found recursive pattern: " ++ toString(t) ++ " which evaluates to: " ++ toString(a))
      (a,cache)
      }
    | None => {
      switch t {
      | Var(_) => (t, cache->Belt.List.setAssoc(toString(t),t,String.equal))
      | Fun(x, body) => {
        let (bodyNew,cacheNew) = evalOneStepMem(body,cache)
        (Fun(x,bodyNew),cacheNew->Belt.List.setAssoc(toString(t),t,String.equal))
      }
      | App(f, arg) => {
        switch evalOneStepMem(f,cache) {
        | (Var(x),cacheNew) => {
          let (argNew, cacheNewer) = evalOneStepMem(arg,cacheNew)
          (App(Var(x),argNew),cacheNewer->Belt.List.setAssoc(toString(t),t,String.equal))
          }
        | (App(m, n),cacheNew) => {
          let (argNew, cacheNewer) = evalOneStepMem(arg,cacheNew)
          (App(App(m,n),argNew),cacheNewer->Belt.List.setAssoc(toString(t),t,String.equal))
        }
        | (Fun(x, body),cacheNew) => {
          let (va,cacheNewer) = evalOneStepMem(arg, cacheNew)
          (subst(x,va,body),cacheNewer->Belt.List.setAssoc(toString(t),t,String.equal))
        }
        }
      }
      }
    }
    }
  }

  let evalToFixedPointMem = (t:t) => {
    let rec evalToFixedPointMemHelper = (t:t, cache:list<(string,t)>, t0:t) => {
      let prevStr = toString(t)
      let (tNext,cacheNew) = evalOneStepMem(t,cache)
      let succStr = toString(tNext)
      Js.log("Prev: " ++ prevStr ++" ; Succ: " ++ succStr)
      if prevStr == succStr {
        Js.log("Reached fixed point: " ++ succStr)
        t
      }
      else {
        evalToFixedPointMemHelper(tNext,cacheNew->Belt.List.setAssoc(prevStr,t0,String.equal),t0)
      }
    }
    evalToFixedPointMemHelper(t,list{},t)
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
  evalToFixedPointMem(input)
}

Js.log(Lambda.toString(output))

let omega = {
  open Lambda
  let smallOmega = Fun("x",App(Var("x"),Var("x")))
  App(smallOmega, smallOmega)
}

Js.log(Lambda.toString(omega))
Js.log(Lambda.toString(Lambda.evalToFixedPointMem(omega)))

let ycomb = {
  open Lambda
  Fun("f",App(Fun("x",App(Var("f"),App(Var("x"),Var("x")))),Fun("x",App(Var("f"),App(Var("x"),Var("x"))))))
}

Js.log(Lambda.toString(ycomb))
Js.log(Lambda.toString(Lambda.evalToFixedPointMem(App(ycomb,Var("F")))))

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
    // toChurchNum(2)
  //   toChurchNum(3),
  //   toChurchNum(4),
  //   toChurchNum(5)
  }
}

// List.iter((x)=>(Js.log(Lambda.toString(Lambda.eval(x)))), numbers)

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

// List.iter((x)=>(Js.log(Lambda.toString(Lambda.eval(App(pred,x))))), numbers)

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

// let resultR = Lambda.evalToFixedPointMem(mul2by2)
// let resultR2 = Lambda.evalToFixedPoint(resultR)
// let resultR3 = Lambda.evalToFixedPoint(mul2by2)
// Js.log(Lambda.toString(resultR3))

let bug = {
  open Lambda
  Fun("x",Fun("y",App(App(Var("x"),Var("y")),App(Fun("x",Var("x")),Var("x")))))
  // App(App(Fun("x",Fun("y",App(Var("y"),Var("x")))),Var("y")),Var("x"))
}
// Js.log(Lambda.toString(Lambda.evalToFixedPoint(bug)))
Js.log(Lambda.toString(Lambda.eval(mul2by2)))
// Js.log(Lambda.toString(Lambda.eval(bug)))