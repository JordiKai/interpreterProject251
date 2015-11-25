/* JordiKai Watanabe-Inouye
CS 251: Programming Languages
Interpreter
*/

//http://www.scheme.com/tspl4/binding.html#./binding:h4
//http://docs.racket-lang.org/reference/let.html

#include "value.h"
#include "linkedlist.h"
#include "talloc.h"
#include "interpreter.h"
#include "parser.h"
#include <string.h>
#include <stdbool.h>
#include <stdlib.h>
#include <stdio.h>
#include <assert.h>

//Creates a new VOID_TYPE value
Value *makeVoid()
{
  Value *newvoid = talloc(sizeof(Value));
  newvoid->type = VOID_TYPE;
  return newvoid;
}

//Used for error checking displays everything that is in a frame's bindings
void displayFrame(Frame *frame)
{
  Value *bindingsPointer = frame->bindings;
  printf("stack:\n");
  while (!isNull(bindingsPointer))
  {
    Value *binding = car(bindingsPointer);
    Value *variable = car(binding);
    Value *value = car(cdr(binding));
    switch (value->type)
    {
        //listed all types in enum to be explicit
        case NULL_TYPE:
            break;
        // Boolean, integer, real, and string literals evaluate to themselves
        case INT_TYPE:
            printf("%s = %i\n", variable->s, value->i);
            break;
        case DOUBLE_TYPE:
            printf("%s = %f\n", variable->s, value->d);
            break;
        case STR_TYPE:
            printf("%s = '%s'\n", variable->s, value->s);
            break;
        case BOOL_TYPE:
            printf("%s = %i\n", variable->s, value->i);
            break;
        case SYMBOL_TYPE:
            printf("%s = %s\n", variable->s, value->s);
            break;
        case PRIMITIVE_TYPE:
            printf("PF = %s\n", variable->s);
            break;
        case CONS_TYPE:
            printf("%s = ", variable->s);
            printTree(value);
            printf("\n");
            break;
        case PTR_TYPE:
            break;
        case OPEN_TYPE:
            break;
        case CLOSE_TYPE:
            break;
        case VOID_TYPE:
            break;
        case CLOSURE_TYPE:
            //printf("I'm a closure \n");
            break;
    }
    bindingsPointer = cdr(bindingsPointer);
  }
  printf("~~~~~~~~~~~~~~~\n");
}

//Used for low scale error checking displays Value type and associated value
void displayValue(Value *args)
{
  switch(args->type)
  {
    case NULL_TYPE:
      printf("NULL_TYPE");
      break;
    case INT_TYPE:
      printf("INT_TYPE: ");
      printf("%i \n", args->i);
      break;
    case DOUBLE_TYPE:
      printf("DOUBLE_TYPE: ");
      printf("%f \n", args->d);
      break;
    case STR_TYPE:
      printf("STR_TYPE: ");
      printf("%s \n", args->s);
      break;
    case SYMBOL_TYPE:
      printf("SYMBOL_TYPE: ");
      printf("%s \n", args->s);
      break;
    case CONS_TYPE:
      printf("CONS_TYPE: \n");
      printf("    CAR:\n    ");
      displayValue(car(args));
      printf("\n    CDR:\n    ");
      displayValue(cdr(args));
      break;
    case BOOL_TYPE:
      printf("BOOL_TYPE: ");
      if (args->i == 1)
      {
        printf("#t ");
      }
      else if (args->i == 0)
      {
        printf("#f ");
      }
      else
      {
          printf("Error with boolean \n");
          texit(1);
      }
      printf("\n");
      break;
    case OPEN_TYPE:
      break;
    case CLOSE_TYPE:
      break;
    default:
      printf("Unknown type\n");
      texit(1);
      break;
  }
}

//Prints out statement related to certain evaluation error when incountered and texits from the program, which cleans up any memory allocated
void evaluationError(int errorNum)
{
  if (errorNum == 0)
  {
    printf("Evaluation Error: Expression has fewer than 3 args \n");
  }
  else if (errorNum == 1)
  {
    printf("Evaluation Error: Expression evaluates to something other than a boolean \n");
  }
  else if (errorNum == 2)
  {
    printf("Evaluation Error: The list-of-bindings for let does not contain a nested list \n");
  }
  else if (errorNum == 3)
  {
    printf("Evaluation Error: Variable is not bound in the current frame or any of its ancestors \n");
  }
  else if (errorNum == 5)
  {
    printf("Evaluation Error: The expected number of arguments does not match the given number \n expected: 1 \n");
  }
  else if (errorNum == 6)
  {
    printf("Evaluation Error: The expected number of arguments does not match the given number \n expected: 2 \n");
  }
  else if (errorNum == 7)
  {
    printf("Evaluation Error: Expected number? \n");
  }
  else if (errorNum == 8)
  {
    printf("Evaluation Error: Expected Symbol, instead got Cons. \n");
  }
  else if (errorNum == 9)
  {
    printf("Evaluation Error: Not an identifier \n");
  }
  else if (errorNum == 10)
  {
    printf("TODO: Finish function\n");
  }
  else if (errorNum == 11)
  {
    printf("Evaluation Error: Reference to undefined identifier\n");
  }
  else
  {
    printf("Evaluation Error \n");
  }
  texit(1);
}

// Looks in the current frame and past frames for the particular symbol being queried to find what it is assigned to.
Value *lookUpSymbol(Value *expr, Frame *currentFrame)
{
  Value *bindingsHead;
  Frame *frameHead = currentFrame;
  // iterates through bindings of frame
  while (frameHead != NULL)
  {
    bindingsHead = frameHead->bindings;
    //while the bindings is not null for current frame look for value associated with variable
    while (!isNull(bindingsHead))
    {
      if(isNull(car(bindingsHead)))
      {
        evaluationError(4);
      }
      Value *binding = car(bindingsHead);
      Value *symbol = car(binding);
      assert(binding->type == CONS_TYPE);
      assert(symbol->type == SYMBOL_TYPE);
      //looks at bindings of cuurentFrame so see if it finds a matching expr
      if (!strcmp(symbol->s, expr->s))
      {
        Value *value = car(cdr(binding));
        return value;
      }
      bindingsHead = cdr(bindingsHead);
    }
    frameHead = frameHead->parent;
  }
  evaluationError(3);
  return expr;
}

//Helper Function- called when an if-stmt is found in the parse tree
Value *evalIf(Value *args, Frame *frame)
{
  Value *result;
  if (length(args) != 3)
  {
    evaluationError(0);
  }
  Value *boolExpr = car(args);
  //if the boolExpr is not BOOL_TYPE, eval to find out #t or #f
  if (boolExpr->type != BOOL_TYPE )
  {
    boolExpr= car(eval(boolExpr, frame));
    //if it doesn't evaluate to a BOOL_TYPE that means that wrong input was provided
    if(boolExpr->type != BOOL_TYPE)
    {
      printf("Hit eval error in evalIf \n");
      evaluationError(1);
    }
  }
  //checks type to find out what to set result as
  if (boolExpr->i == 1) //true
  {
    result = car(cdr(args));
  }
  else if (boolExpr->i == 0) //false
  {
    result = car(cdr(cdr(args)));
  }
  else // must be error
  {
     texit(1);
  }
  return result;
}

// Helper Function- called when a lambda-stmt is found in the parse tree
Value *evalLambda(Value *args, Frame *currentFrame)
{
  assert(length(args) == 2);
  Value *closure = talloc(sizeof(Value));
  closure->type = CLOSURE_TYPE;
  assert(car(args)->type == CONS_TYPE);
  closure->cl.paramNames = car(args);
  closure->cl.functionCode = car(cdr(args));
  closure->cl.frame = currentFrame;
  return closure;
}

// Helper Function- called when a define-stmt is found in the parse tree
Value *evalDefine(Value *args, Frame *currentFrame)
{
  while(currentFrame->parent != NULL)
  {
    currentFrame = currentFrame->parent;
  }
  Value *voidVal = makeVoid();
  assert(car(args)->type == SYMBOL_TYPE);
  assert(length(args) == 2);
  currentFrame->bindings = cons(args, currentFrame->bindings);
  return voidVal;
}

//Helper Function- called when a set!-stmt is found in the parse tree
//Credits: Bounced ideas off of Hami
Value *evalSetBang(Value *args, Frame *currentFrame)
{
  //alters the value of an existing binding, returns new value
  //check length of args; set! can only take two arguments
  if(length(args)!= 2) //assert(length(args) == 2);
  {
    evaluationError(6);
  }
  if(car(args)->type != SYMBOL_TYPE) //assert(car(args)->type == SYMBOL_TYPE);
  {
    evaluationError(9);
  }
  Value *void_return = makeVoid();
  Value *set = talloc(sizeof(Value));
  set->type = CONS_TYPE;
  Value *expr;
  //expr is set to whatever cdr(args) evaluates to
  if(!isNull(car(cdr(args))))
  {
    expr = eval(car(cdr(args)), currentFrame);
    set->c.cdr = expr;
  }
  //traverse frame bindings and search for identifier
  Value *identifier = car(args);
  set->c.car = identifier;
  Frame *frameHead = currentFrame;
  Value *bindingsHead;
  bool foundSymbol = false;
  while (frameHead != NULL && !foundSymbol)
  {
    bindingsHead = frameHead->bindings;
    //while the bindings is not null for current frame look for x
    while (!isNull(bindingsHead) && !foundSymbol)
    {
      if(isNull(car(bindingsHead)))
      {
        evaluationError(4);
      }
      Value *binding = car(bindingsHead);
      Value *symbol = car(binding);
      assert(binding->type == CONS_TYPE);
      assert(symbol->type == SYMBOL_TYPE);
      //looks at bindings of frame so see if it finds a matching identifier
      //if it finds a matching the reset the cdr to expr
      if(!strcmp(symbol->s, identifier->s))
      {
        //when reseting, need to know type of expr and type of old
        binding = set;
        foundSymbol = true;
        return void_return; // set! doesn't return anything, it just resets the value
      }
      //else continue traversing bindings
      bindingsHead = cdr(bindingsHead);
    }
    // continue traversing frames
    frameHead = frameHead->parent;
  }
  evaluationError(3);
  return void_return; // should never reach here
}

// Helper Function- called when a let-stmt is found in the parse tree
//Returns: the values of the final body expression (i.e. evaluated cdr(args))
//Credits: Bounced ideas off of and clarified with Dave
Frame *evalLet(Value *args, Frame *currentFrame)
{
    //arguments should be of length 2
    if(length(args) != 2)
    {
      evaluationError(6);
    }
    //'let' creates a frame containing variable & value; pointer to the frame that was active when it was created = parent
    Frame *newFrame = talloc(sizeof(Frame));
    newFrame->parent = currentFrame;
    newFrame->bindings = makeNull();
    assert(car(args)->type==CONS_TYPE);
    Value *argsPointer = car(args);
    Value *letThis;
    Value *symbol;
    Value *value;
    while (!isNull(argsPointer))
    {
      if(argsPointer->type != CONS_TYPE)
      {
        evaluationError(2);
      }
      letThis = car(argsPointer);
      if(length(letThis) != 2)
      {
        evaluationError(6);
      }
      symbol = car(letThis);
      assert(symbol->type == SYMBOL_TYPE);
      value = car(cdr(letThis));
      assert(value->type != NULL_TYPE);
      value = eval(value,currentFrame);
      newFrame->bindings = cons(letThis, newFrame->bindings);
      argsPointer = cdr(argsPointer);
    }
    return newFrame;
    //may have neglected to catch things not in scope
}

//Helper Function- called when a letrec-stmt is found in the parse tree
//Returns: the values of the final body expression (i.e. evaluated cdr(args))
//Credits: Bounced ideas off of and clarified with Dave and Edward
Frame *evalLetRec(Value *args, Frame *currentFrame)
{
  //'letrec' creates a frame containing variable & value; pointer to the currrent frame
  // allows defn of mutually recursive procedures

  /*NOTE:
  Dave- I know what we discussed in office hours but while trying to apply it, I noticed other groups had not and the assignment
  sheet linked through Moodle said we didn't have to account for the unidentified identifier rather for the input:

      (define y 5)
      (letrec ((x y) (y 3)) x)

  it would be fine if it returned 5...I'm not sure if I read wrong and by the time I checked with other people your office hours were done,
  and you were gone for the day
  */

  //arguments should be of length 2
  if(length(args) != 2)
  {
    evaluationError(6);
  }
  if(car(args)->type != CONS_TYPE) //the first argument MUST be a CONS_TYPE
  {
    evaluationError(2);
  }
  Frame *newFrame = talloc(sizeof(Frame));
  newFrame->parent = currentFrame;
  newFrame->bindings = makeNull();
  assert(car(args)->type==CONS_TYPE);
  Value *argsPointer = car(args);
  Value *letThis;
  Value *symbol;
  Value *value;
  while (!isNull(argsPointer))
  {
    if(argsPointer->type != CONS_TYPE)
    {
      evaluationError(2);
    }
    letThis = car(argsPointer);
    if(length(letThis) != 2)
    {
      evaluationError(6);
    }
    symbol = car(letThis);
    assert(symbol->type == SYMBOL_TYPE);
    value = car(cdr(letThis));
    assert(value->type != NULL_TYPE);
    value = eval(value,newFrame);
    newFrame->bindings = cons(letThis, newFrame->bindings);
    argsPointer = cdr(argsPointer);
  }
  return newFrame; // neglected to catch things not in scope evaluationError(11);
}

//Helper Function (recursive)- called when a let*-stmt is found in the parse tree
//Returns: the values of the final body expression (i.e. evaluated cdr(args))
//Credits: Bounced ideas off of and clarified with Dave
Frame *evalLetStar(Value *args, Frame *currentFrame)
{
  //let* is similar to let except that the expressions expr
  // are evaluated in sequence from left to right,
  // and each of these expressions is within the scope of the variables to the left
  // used when there is a linear dependency, layers of frames

  if(car(args)->type != CONS_TYPE) //the first argument MUST be a CONS_TYPE
  {
    evaluationError(2);
  }
  //creates a new frame everytime this function is called
  Frame *newFrame = talloc(sizeof(Frame));
  newFrame->parent = currentFrame;
  newFrame->bindings = makeNull();
  Value *argsPointer = args;
  if(argsPointer->type != CONS_TYPE)
  {
    evaluationError(2);
  }
  Value *letThis;
  letThis = car(argsPointer);
  if(length(letThis) != 2)
  {
    evaluationError(6);
  }
  Value *symbol;
  Value *value;
  symbol = car(letThis);
  assert(symbol->type == SYMBOL_TYPE);
  value = car(cdr(letThis));
  assert(value->type != NULL_TYPE);
  value = eval(value, newFrame->parent);
  letThis = cons(symbol, cons(value, makeNull()));
  // adding letThis to the bindings of the newFrame
  //each frame's bindings should be of length 1
  newFrame->bindings = cons(letThis, newFrame->bindings);
  argsPointer = cdr(argsPointer);
  if(isNull(argsPointer))
  {
    return newFrame;
  }
  return evalLetStar(argsPointer, newFrame);
}

//Helper Function- called when a cond-stmt is found in the parse tree
Value *evalCond(Value *args, Frame *currentFrame)
{
  //if there's nothing to return, return VOID_TYPE
  Value *result;
  if(isNull(args))
  {
    Value *result= makeVoid();
    return result;
  }
  Value *condResult;
  Value *cond;
  // eval the cdr(args), return the eval of the first stmt that evals to #t
  //if none of them eval to #t then return whatever the last case evals to
  while(!isNull(args))
  {
    condResult= car(args);
    //the length of the condition should be 2...well last item can be of length 1
    if(length(condResult)!=2)
    {
      //check to make sure it isn't 'else' statment, would only reach this case if a #t was not found before
      if(isNull(cdr(args)))
      {
        result = eval(car(condResult), currentFrame);
        return result;
      }
      //printf("Unexpected length of args \n");
      evaluationError(12);
    }
    //assuming that all of the conditions given have type BOOL_TYPE
    cond = eval(car(condResult), currentFrame);
    if(car(cond)->i == 1) //true
    {
      result = eval(car(cdr(condResult)), currentFrame);
      return result;
    }
    //else keep traversing
    args = cdr(args);
  }
  return result;
}

// Helper Function- called when a begin-stmt is found in the parse tree (JKJB)
Value *evalBegin(Value *args, Frame *currentFrame)
{
  //if there's nothing to return, return VOID_TYPE
  Value *result;
  if(isNull(args))
  {
    result = makeVoid();
    return result;
  }
  while(!isNull(args))
  {
    result = eval(car(args), currentFrame);
    args = cdr(args);
  }
  return result;
}

// Helper Function- called when an and-stmt is found in the parse tree (JKJB)
Value *evalAnd(Value *args, Frame *currentFrame)
{
  Value *result = talloc(sizeof(Value));
  result->type = BOOL_TYPE;
  // this should never be tested, according to Dave
  if(isNull(args))
  {
    result = makeVoid();
    return result;
  }
  bool allTrue = true;
  while(!isNull(args) && allTrue)
  {
    if(car(args)->type == BOOL_TYPE)
    {
      result = car(args);
    }
    else{
      result = car(eval(car(args), currentFrame));
    }
    if (result->type != BOOL_TYPE)
    {
      evaluationError(4);
    }
    if(result->i == 0)
    {
      allTrue = false;
    }
    args = cdr(args);
  }
  result->i = allTrue;
  result = cons(result, makeNull());
  return result;
}

// Helper Function- called when an or-stmt is found in the parse tree (JKJB)
Value *evalOr(Value *args, Frame *currentFrame)
{
  Value *result = talloc(sizeof(Value));
  result->type = BOOL_TYPE;
  // this should never be tested, according to Dave
  if(isNull(args))
  {
    result = makeVoid();
    return result;
  }
  bool allTrue = false;
  while(!isNull(args) && !allTrue)
  {
    if(car(args)->type == BOOL_TYPE)
    {
      result = car(args);
    }
    else{
      result = car(eval(car(args), currentFrame));
    }
    if (result->type != BOOL_TYPE)
    {
      evaluationError(4);
    }
    if(result->i == 1)
    {
      allTrue = true;
    }
    args = cdr(args);
  }
  result->i = allTrue;
  result = cons(result, makeNull());
  return result;
}

/* Construct a new frame whose parent frame is the environment stored in the closure.
Add bindings to the new frame mapping each formal parameter (found in the closure)
to the corresponding actual parameter (found in args).
Evaluate the function body (found in the closure) with the new frame as its
environment, and return the result of the call to eval. */
Value *apply(Value *function, Value *args)
{
  Value *tempBinding;
  Value *valueHead = makeNull();
  Value *result;
  Value *paramsHead;
  paramsHead = function->cl.paramNames;
  // check the length of the closure's params with the length of args
  if (length(args) != length(paramsHead))
  {
    evaluationError(5);
  }
  Frame *newFrame = talloc(sizeof(Frame));
  newFrame->parent = function->cl.frame;
  newFrame->bindings = makeNull();
  while (!isNull(args))
  {
    valueHead = cons(car(args), valueHead);
    tempBinding = cons(car(paramsHead), valueHead);
    newFrame->bindings = cons(tempBinding, newFrame->bindings);
    paramsHead = cdr(paramsHead);
    args = cdr(args);
  }
  result = eval(function->cl.functionCode, newFrame);
  return result;
}

// Helper Function- called when a primitive is found, applys primitive function to args
Value *applyPrimitive(Value *function, Value *args)
{
  return (*(function->pf))(args);
}

// Evaluates Scheme code by looking at a frame's bindings
// Returns whatever the value evaluates to
Value *eval(Value *tree, Frame *frame)
{
  Value *first;
  Value *args;
  Value *result;
  switch (tree->type)
  {
      //listed all types in enum to be explicit
      case NULL_TYPE:
        result = tree;
        break;
      case VOID_TYPE:
        result = tree;
        break;
      // Boolean, integer, real, and string literals evaluate to themselves
      case INT_TYPE:
        //printf("pooping ints\n");
        result = tree;
        break;
      case DOUBLE_TYPE:
        result = tree;
        break;
      case STR_TYPE:
        result = tree;
        break;
      case BOOL_TYPE:
        //printf("Found a BOOL_TYPE\n");
        result = tree;
        break;
      case PTR_TYPE:
        result = tree;
        break;
      case OPEN_TYPE:
        result = tree;
        break;
      case CLOSE_TYPE:
        result = tree;
        break;
      case CLOSURE_TYPE:
        result = tree;
        break;
      case SYMBOL_TYPE:
        result = eval(lookUpSymbol(tree, frame), frame);
        break;
      case PRIMITIVE_TYPE:
        result = tree;
        break;
      case CONS_TYPE:
        first = car(tree);
        args = cdr(tree);
        if (first->type == CONS_TYPE)
        {
          evaluationError(8);
        }
        if (!strcmp(first->s,"if"))
        {
          result = eval(evalIf(args, frame), frame);
        }
        else if (!strcmp(first->s,"let"))
        {
          frame = evalLet(args, frame);
          //Check that cdr is not null in evalLet
          if(cdr(args)->type == CONS_TYPE)
          {
            result = eval(car(cdr(args)), frame);
          }
          else
          {
            result = eval(cdr(args), frame);
          }
        }
        else if (!strcmp(first->s,"letrec"))
        {
          //only difference btwn let and letrec is that the frame being passed in is the currentFrame, rather than parent of currentFrame
          frame = evalLetRec(args, frame);
          if (cdr(args)->type == CONS_TYPE) //!isNull(cdr(args))
          {
            result = eval(car(cdr(args)), frame);
          }
          else
          {
            result = eval(cdr(args), frame);
          }
        }
        else if (!strcmp(first->s,"let*"))
        {
          if(length(args) != 2) //arguments should be of length 2
          {
            evaluationError(6);
          }
          frame = evalLetStar(car(args), frame);
          if (cdr(args)->type == CONS_TYPE) //!isNull(cdr(args))
          {
            result = eval(car(cdr(args)), frame);
          }
          else
          {
            result = eval(cdr(args), frame);
          }
        }
        else if (!strcmp(first->s,"quote"))
        {
          if (!isNull(args))
          {
            if (args->type !=CONS_TYPE)
            {
              evaluationError(4);
            }
            else if (length(args) != 1)
            {
              evaluationError(5);
            }
          }
          result = args; // After talking with Edward implementation later may have been easier if we had done car(args);
        }
        else if (!strcmp(first->s,"lambda"))
        {
          // create a closure
          result = evalLambda(args, frame);
        }
        else if (!strcmp(first->s,"define"))
        {
          //returns a special Value of type VOID_TYPE
          result = evalDefine(args, frame);
        }
        // Final implementations
        else if (!strcmp(first->s,"begin"))
        {
          result = evalBegin(args, frame);
        }
        else if (!strcmp(first->s,"and"))
        {
          result = evalAnd(args, frame);
        }
        else if (!strcmp(first->s,"or"))
        {
          result = evalOr(args, frame);
        }
        else if (!strcmp(first->s,"cond"))
        {
          result = evalCond(args, frame);
        }
        else if (!strcmp(first->s,"set!"))
        {
          result = evalSetBang(args, frame);
        }
        else
        {
          if (first->type == SYMBOL_TYPE)
          {
            result = eval(first, frame);
            if(result->type == CLOSURE_TYPE)
            {
              result = apply(result, args);
            }
            //saved primitive symbol as SYMBOL_TYPE
            if(result->type == PRIMITIVE_TYPE)
            {
              Value *temp = makeNull();
              Value *argsPointer = args;
              while(!isNull(argsPointer))
              {
                temp = cons(eval(car(argsPointer), frame), temp);
                argsPointer= cdr(argsPointer);
              }
              args = reverse(temp); //reverse stack, after evaling all parts
              //apply primitive function to args now that they are evaluated
              result = applyPrimitive(result, args);
            }
          }
          else
          {
            evaluationError(2);
          }
        }
        break;
  }
  return result;
}

//Prints evaluation to terminal
void printOutput(Value *result)
{
  while (!isNull(result) && result->type != VOID_TYPE)
  {
    if(result->type != CONS_TYPE)
    {
      Value *head = result;
      switch(head->type)
      {
        case NULL_TYPE:
          printf("");
          break;
        case INT_TYPE:
          printf("%i ", head->i);
          break;
        case DOUBLE_TYPE:
          printf("%f ", head->d);
          break;
        case STR_TYPE:
          printf("\"%s\" ", head->s);
          break;
        case CONS_TYPE:
          printf("(");
          printOutput(head);
          printf(")");
          break;
        case BOOL_TYPE:
          if (head->i == 1)
          {
            printf("#t ");
          }
          else if(head->i == 0)
          {
            printf("#f ");
          }
          else
          {
            printf("Hit eval error in printOutput \n");
            evaluationError(1);
          }
          break;
        case PTR_TYPE:
          break;
        case OPEN_TYPE:
          printf("printOutput OPEN \n");
          break;
        case CLOSE_TYPE:
          printf("printOutput CLOSE \n");
          break;
        case SYMBOL_TYPE:
          printf("%s ", head->s);
          break;
        case VOID_TYPE:
          break;
        case CLOSURE_TYPE:
          break;
        case PRIMITIVE_TYPE:
          printf("printOutput PRIMITIVE_TYPE\n");
          break;
      }
      break;
    }
    else
    {
      Value *head = car(result);
      switch(head->type)
      {
        case NULL_TYPE:
          printf("");
          break;
        case INT_TYPE:
          printf("%i ", head->i);
          if (cdr(result)->type != CONS_TYPE && !isNull(cdr(result)))
          {
            printf(" . ");
          }
          break;
        case DOUBLE_TYPE:
          printf("%f ", head->d);
          break;
        case STR_TYPE:
          printf("\"%s\" ", head->s);
          break;
        case CONS_TYPE:
          printf("(");
          printOutput(head);
          printf(")");
          break;
        case BOOL_TYPE:
          if (head->i == 1)
          {
            printf("#t ");
          }
          else if(head->i == 0)
          {
            printf("#f ");
          }
          else
          {
            printf("Hit eval error in printOutput \n");
            evaluationError(1);
          }
          break;
        case PTR_TYPE:
          break;
        case OPEN_TYPE:
          printf("printOutput OPEN \n");
          break;
        case CLOSE_TYPE:
          printf("printOutput CLOSE \n");
          break;
        case SYMBOL_TYPE:
          printf("%s ", head->s);
          break;
        case VOID_TYPE:
          break;
        case CLOSURE_TYPE:
          break;
        case PRIMITIVE_TYPE:
          printf("printOutput PRIMITIVE_TYPE\n");
          break;
      }
      result = cdr(result);
    }
  }
}

//Additional Primitives
Value *primitiveGreaterthanEqualto(Value *args)
{
  if(length(args)!=2)
  {
    evaluationError(6);
  }
  Value *greaterthanequalto = talloc(sizeof(Value));
  greaterthanequalto->type = BOOL_TYPE;
  Value *firstnum = car(args);
  Value *secondnum = car(cdr(args));
  //checks to make sure args is either type INT_TYPE or DOUBLE_TYPE
  if (firstnum->type == INT_TYPE && secondnum->type == INT_TYPE)
  {
    greaterthanequalto->i = firstnum->i >= secondnum->i;
  }
  else if (firstnum->type == INT_TYPE && secondnum->type == DOUBLE_TYPE)
  {
    greaterthanequalto->i = firstnum->i >= secondnum->d;
  }
  else if (firstnum->type == DOUBLE_TYPE && secondnum->type == INT_TYPE)
  {
    greaterthanequalto->i = firstnum->d >= secondnum->i;
  }
  else if (firstnum->type == DOUBLE_TYPE && secondnum->type == DOUBLE_TYPE)
  {
    greaterthanequalto->i = firstnum->d >= secondnum->d;
  }
  else
  {
    evaluationError(4);
  }
  greaterthanequalto = cons(greaterthanequalto, makeNull());
  return greaterthanequalto;
}

Value *primitiveLessthanEqualto(Value *args)
{
  if(length(args)!=2)
  {
    evaluationError(6);
  }
  Value *lessthanequalto = talloc(sizeof(Value));
  lessthanequalto->type = BOOL_TYPE;
  Value *firstnum = car(args);
  Value *secondnum = car(cdr(args));
  //checks to make sure args is either type INT_TYPE or DOUBLE_TYPE
  if (firstnum->type == INT_TYPE && secondnum->type == INT_TYPE)
  {
    lessthanequalto->i = firstnum->i <= secondnum->i;
  }
  else if (firstnum->type == INT_TYPE && secondnum->type == DOUBLE_TYPE)
  {
    lessthanequalto->i = firstnum->i <= secondnum->d;
  }
  else if (firstnum->type == DOUBLE_TYPE && secondnum->type == INT_TYPE)
  {
    lessthanequalto->i = firstnum->d <= secondnum->i;
  }
  else if (firstnum->type == DOUBLE_TYPE && secondnum->type == DOUBLE_TYPE)
  {
    lessthanequalto->i = firstnum->d <= secondnum->d;
  }
  else
  {
    evaluationError(4);
  }
  printf("Bool %i \n", lessthanequalto->i);
  lessthanequalto = cons(lessthanequalto, makeNull());
  return lessthanequalto;
}

Value *primitveList(Value *args)
{
  Value *list = makeNull();
  while(!isNull(args))
  {
    list = cons(car(args),list);
    args = cdr(args);
  }
  list = reverse(list);
  list = cons(list, makeNull());
  return list;
}

//Below are the required primitive functions, they take args, check for input errors, and apply whatever primitve call to them, return result of action
Value *primitiveModulo(Value *args)
{
  if(length(args)!=2)
  {
    evaluationError(6);
  }
  Value *mod = talloc(sizeof(Value));
  mod->type = INT_TYPE;
  Value *firstnum = car(args);
  Value *secondnum = car(cdr(args));
  if(firstnum->type == DOUBLE_TYPE && secondnum->type == DOUBLE_TYPE )
  {
    evaluationError(4);
  }
  mod->i = firstnum->i % secondnum->i;
  return mod;
}

Value *primitiveEqual(Value *args)
{
  if(length(args)!=2)
  {
    evaluationError(6);
  }
  Value *equal = talloc(sizeof(Value));
  equal->type = BOOL_TYPE;
  Value *firstnum = car(args);
  Value *secondnum = car(cdr(args));
  //checks to make sure args is either type INT_TYPE or DOUBLE_TYPE
  if (firstnum->type == INT_TYPE && secondnum->type == INT_TYPE)
  {
    equal->i = firstnum->i == secondnum->i;
  }
  else if (firstnum->type == INT_TYPE && secondnum->type == DOUBLE_TYPE)
  {
    equal->i = firstnum->i == secondnum->d;
  }
  else if (firstnum->type == DOUBLE_TYPE && secondnum->type == INT_TYPE)
  {
    equal->i = firstnum->d == secondnum->i;
  }
  else if (firstnum->type == DOUBLE_TYPE && secondnum->type == DOUBLE_TYPE)
  {
    equal->i = firstnum->d == secondnum->d;
  }
  else
  {
    evaluationError(4);
  }
  equal = cons(equal, makeNull());
  return equal;
}

Value *primitiveGreaterthan(Value *args)
{
  if(length(args)!=2)
  {
    evaluationError(6);
  }
  Value *greaterthan = talloc(sizeof(Value));
  greaterthan->type = BOOL_TYPE;
  Value *firstnum = car(args);
  Value *secondnum = car(cdr(args));
  //checks to make sure args is either type INT_TYPE or DOUBLE_TYPE
  if (firstnum->type == INT_TYPE && secondnum->type == INT_TYPE)
  {
    greaterthan->i = firstnum->i > secondnum->i;
  }
  else if (firstnum->type == INT_TYPE && secondnum->type == DOUBLE_TYPE)
  {
    greaterthan->i = firstnum->i > secondnum->d;
  }
  else if (firstnum->type == DOUBLE_TYPE && secondnum->type == INT_TYPE)
  {
    greaterthan->i = firstnum->d > secondnum->i;
  }
  else if (firstnum->type == DOUBLE_TYPE && secondnum->type == DOUBLE_TYPE)
  {
    greaterthan->i = firstnum->d > secondnum->d;
  }
  else
  {
    evaluationError(4);
  }
  greaterthan = cons(greaterthan, makeNull());
  return greaterthan;
}

Value *primitiveLessthan(Value *args)
{
  if(length(args)!=2)
  {
    evaluationError(6);
  }
  Value *lessthan = talloc(sizeof(Value));
  lessthan->type = BOOL_TYPE;
  Value *firstnum = car(args);
  Value *secondnum = car(cdr(args));
  //checks to make sure args is either type INT_TYPE or DOUBLE_TYPE
  if (firstnum->type == INT_TYPE && secondnum->type == INT_TYPE)
  {
    lessthan->i = firstnum->i < secondnum->i;
  }
  else if (firstnum->type == INT_TYPE && secondnum->type == DOUBLE_TYPE)
  {
    lessthan->i = firstnum->i < secondnum->d;
  }
  else if (firstnum->type == DOUBLE_TYPE && secondnum->type == INT_TYPE)
  {
    lessthan->i = firstnum->d < secondnum->i;
  }
  else if (firstnum->type == DOUBLE_TYPE && secondnum->type == DOUBLE_TYPE)
  {
    lessthan->i = firstnum->d < secondnum->d;
  }
  else
  {
    evaluationError(4);
  }
  lessthan = cons(lessthan, makeNull());
  return lessthan;
}

Value *primitiveMultiply (Value *args)
{
  // takes any number of numeric arguments >= 2
  if(length(args)!=2)
  {
    evaluationError(6);
  }
  Value *total = talloc(sizeof(Value));
  total->type = DOUBLE_TYPE;
  total->d = 1.0;
  Value *nextargs = args;
  while(!isNull(nextargs))
  {
    //checks to make sure args is either type INT_TYPE or DOUBLE_TYPE
    if (car(nextargs)->type != INT_TYPE && car(nextargs)->type != DOUBLE_TYPE)
    {
      evaluationError(7);
    }
    if(car(nextargs)->type == DOUBLE_TYPE)
    {
      total->d = total->d * car(nextargs)->d;
      nextargs = cdr(nextargs);
    }
    else //if(car(nextargs)->type == INT_TYPE)
    {
      total->d = total->d * car(nextargs)->i;
      nextargs = cdr(nextargs);
    }
  }
  return total;
}

Value *primitiveDivide (Value *args)
{
  //returns a real if the numbers do not divide evenly
  // assume ONLY 2 numeric arguments
  if(length(args)!=2)
  {
    //printf("Length of given arguments: %i\n", length(args));
    evaluationError(6);
  }
  Value *total = talloc(sizeof(Value));
  total->type = DOUBLE_TYPE;
  Value *firstnum = car(args);
  Value *secondnum = car(cdr(args));
  //checks to make sure args is either type INT_TYPE or DOUBLE_TYPE
  if (firstnum->type == INT_TYPE && secondnum->type == INT_TYPE)
  {
    total->d = (float) firstnum->i / (float) secondnum->i;
  }
  else if (firstnum->type == INT_TYPE && secondnum->type == DOUBLE_TYPE)
  {
    total->d = (float) firstnum->i / secondnum->d;
  }
  else if (firstnum->type == DOUBLE_TYPE && secondnum->type == INT_TYPE)
  {
    total->d = firstnum->d / (float) secondnum->i;
  }
  else if (firstnum->type == DOUBLE_TYPE && secondnum->type == DOUBLE_TYPE)
  {
    total->d = firstnum->d / secondnum->d;
  }
  else
  {
    evaluationError(4);
  }
  return total;
}

Value *primitiveSubtract (Value *args)
{
  // assume ONLY 2 numeric arguments
  if(length(args)!=2)
  {
    evaluationError(6);
  }
  Value *total = talloc(sizeof(Value));
  total->type = DOUBLE_TYPE;
  Value *firstnum = car(args);
  Value *secondnum = car(cdr(args));
  //checks to make sure args is either type INT_TYPE or DOUBLE_TYPE
  if (firstnum->type == INT_TYPE && secondnum->type == INT_TYPE)
  {
    total->d = (float) firstnum->i - (float) secondnum->i;
  }
  else if (firstnum->type == INT_TYPE && secondnum->type == DOUBLE_TYPE)
  {
    total->d = (float) firstnum->i - secondnum->d;
  }
  else if (firstnum->type == DOUBLE_TYPE && secondnum->type == INT_TYPE)
  {
    total->d = firstnum->d - (float) secondnum->i;
  }
  else if (firstnum->type == DOUBLE_TYPE && secondnum->type == DOUBLE_TYPE)
  {
    total->d = firstnum->d - secondnum->d;
  }
  else
  {
    evaluationError(4);
  }
  return total;
}

Value *primitiveAdd (Value *args)
{
  // the add primitive's length is not restricted, however must check that all are of type INT_TYPE or DOUBLE_TYPE
  // eg (+) returns 0 and (+ 3.0) returns 3.0
  Value *total = talloc(sizeof(Value));
  total->type = DOUBLE_TYPE; //set as int type for now but if any item is a double
  total->d = 0;
  if(length(args) == 0)
  {
    return total;
  }
  bool isInt = true;
  while(!isNull(args))
  {
    if(car(args)->type != INT_TYPE && car(args)->type != DOUBLE_TYPE)
    {
      evaluationError(7);
    }
    if (car(args)->type == INT_TYPE)
    {
      total->d = car(args)->i + total->d;
    }
    if (car(args)->type == DOUBLE_TYPE)
    {
      total->d = car(args)->d + total->d;
    }
    args = cdr(args);
  }
  return total;
}

Value *primitiveNull (Value *args)
{
  args = car(args);
  Value *result = talloc(sizeof(Value));
  result->type = CONS_TYPE;
  result->c.cdr = makeNull();
  if (length(args)!=1)
  {
    evaluationError(5);
  }
  Value *primBool= talloc(sizeof(Value));
  primBool->type = BOOL_TYPE;
  if (isNull(car(args)))
  {
    primBool->i = 1;
  }
  else
  {
    primBool->i = 0;
  }
  result->c.car = primBool;
  return result;
}

// Checks for input errors and returns the car of the args passed in
Value *primitiveCar (Value *args)
{
  args = car(args);
 Value *result;
 if (length(args)!=1)
 {
   evaluationError(5);
 }
 if (args->type != CONS_TYPE)
 {
   evaluationError(4);
 }
 else
 {
   if(car(args)->type != CONS_TYPE)
   {
     evaluationError(4);
   }
   else
   {
     result = cons(car(car(args)), makeNull());
   }
 }
 return result;
}

// Checks for input errors and returns the cdr of the args passed in
Value *primitiveCdr (Value *args)
{
  args = car(args);
  Value *result;
  if (length(args)!=1)
  {
    evaluationError(5);
  }
  if (args->type != CONS_TYPE)
  {
    evaluationError(4);
  }
  else
  {
    if(car(args)->type != CONS_TYPE)
    {
      evaluationError(4);
    }
    else
    {
      result = cons(cdr(car(args)), makeNull());
    }
  }
  return result;
}

//John Blake and I meet to fix this issue from the previous assginment
// We realise that this is not a great solution, but in interest of saving time and testing other cases it worked.
Value *primitiveCons(Value *args)
{
  Value *result = makeNull();
  if(length(args) != 2)
  {
    evaluationError(6);
  }
  Value *argslist = makeNull();
  Value *firstArg;
  Value *secondArg;
  if (car(args)->type == CONS_TYPE)
  {
    firstArg = car(car(args));
  }
  else
  {
    firstArg = car(cons(car(args), makeNull()));
  }
  args = cdr(args);
  if (car(args)->type == CONS_TYPE)
  {
    secondArg = car(car(args));
  }
  else
  {
    evaluationError(101);
  }
  args = cons(cons(firstArg, secondArg), makeNull());
  return result;
}

//Binds primitive functions to GlobalFrame
void bind (char *name, Value *(*primfunction)(struct Value *), Frame *frame)
{
  //Add primitive functions to top-level bindings list
  Value *primitiveSymbol = talloc(sizeof(Value));
  // if this doesn't work try string value type
  primitiveSymbol->type = SYMBOL_TYPE;
  primitiveSymbol->s = name;
  Value *value = talloc(sizeof(Value));
  value->type = PRIMITIVE_TYPE;
  value->pf = primfunction;
  value = cons(value, makeNull());
  Value *wrappedPrimitive = cons(primitiveSymbol, value);
  frame->bindings = cons(wrappedPrimitive, frame->bindings);
}

void interpret(Value *tree)
{
  //Create pointer to the Global Frame (global variable that's going to be passed through and modified throughout)
  Frame *GlobalFrame = talloc(sizeof(Frame));
  GlobalFrame->parent = NULL;
  GlobalFrame->bindings = makeNull();
  bind("+", primitiveAdd, GlobalFrame);
  bind("null?", primitiveNull, GlobalFrame);
  bind("car", primitiveCar, GlobalFrame);
  bind("cdr", primitiveCdr, GlobalFrame);
  bind("cons", primitiveCons, GlobalFrame);
  bind("*", primitiveMultiply, GlobalFrame);
  bind("-", primitiveSubtract, GlobalFrame);
  bind("/", primitiveDivide, GlobalFrame);
  bind("modulo", primitiveModulo, GlobalFrame);
  bind("<", primitiveLessthan, GlobalFrame);
  bind(">", primitiveGreaterthan, GlobalFrame);
  bind("=", primitiveEqual, GlobalFrame);
  //extra primitives
  bind(">=", primitiveGreaterthanEqualto, GlobalFrame);
  bind("<=", primitiveLessthanEqualto, GlobalFrame);
  bind("list", primitveList, GlobalFrame);

  Value *result;
  //traverse through whole tree
  while (!isNull(tree))
  {
    result = eval(car(tree), GlobalFrame);
    printOutput(result);
    printf("\n");
    tree = cdr(tree);
  }
}
