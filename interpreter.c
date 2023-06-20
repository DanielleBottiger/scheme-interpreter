#include <limits.h>
#include "value.h"
#include "linkedlist.h"
#include "talloc.h"
#include <stdlib.h>
#include <stdbool.h>
#include <stdio.h>
#include <string.h>
#include <assert.h>
#include "parser.h"
#include <math.h>

#ifndef _INTERPRETER
#define _INTERPRETER
void displayToken1(Value *token);
Value *eval(Value *tree, Frame *frame);

Frame *makeFrame(Frame *parent)
{
  Frame *frame = talloc(sizeof(Frame));
  frame->parent = parent;       // parent  value.  is being assigned correctly. I know this from being able to print the bindings in a frame's parent.
  frame->bindings = makeNull(); // start with empty list of bindings.
  return frame;
}

Value *lookUpSymbol(Value *tree, Frame *frame)
{
  Frame *currentFrame = frame;

  while (currentFrame != NULL)
  {
    Value *bindings = currentFrame->bindings;

    while (bindings->type == CONS_TYPE)
    {
      Value *variable = car(bindings); // This will be like x = 3;

      if (!strcmp(car(variable)->s, tree->s))
      {
        return eval(cdr(variable), frame);
      }
      bindings = cdr(bindings);
    }
    currentFrame = currentFrame->parent;
  }
  printf("Evaluation Error: Symbol %s not found.", tree->s);
  texit(0);
  return makeNull();
}

Value *evalDefine(Value *args, Frame *frame)
{
  Value *values = args;
  Value *content = eval(car(cdr(values)), frame);
  Value *symbol = cons(car(values), content);

  frame->bindings = cons(symbol, (frame->bindings));
  return makeNull();
}

Value *evalLambda(Value *args, Frame *frame)
{

  Value *closureValue = makeNull();
  closureValue->type = CLOSURE_TYPE;
  closureValue->cl.frame = frame;
  closureValue->cl.paramNames = car(args);
  closureValue->cl.functionCode = car(cdr(args));
  return closureValue;
}

Value *evalIf(Value *args, Frame *frame)
{

  Value *test = car(args);
  args = cdr(args);

  Value *TRUEexpression = car(args);
  args = cdr(args);

  Value *FALSEexpression = car(args);

  test = eval(test, frame);

  if (test->type == BOOL_TYPE)
  {
    if (test->i == 0)
    {
      return eval(FALSEexpression, frame);
    }
    else if (test->i == 1)
    {
      return eval(TRUEexpression, frame);
    }
    else
    {
      printf("\nEvaluation Error: Boolean does not have true or false value.\n");
      return makeNull();
    }
  }
  else
  {
    printf("\nEvaluation Error: if statement did not evaluate to a Boolean.");
    return makeNull();
  }
}

Value *evalLet(Value *args, Frame *frame)
{

  Value *parameters = args->c.car; // parameters
  Value *code = args->c.cdr;       // body of code
  Value *firstCode = car(cdr(args));

  while (parameters->type == CONS_TYPE)
  {

    Value *variable = car(car(parameters));
    Value *value = car(cdr(car(parameters)));
    Value *symbol = cons(variable, value);

    frame->bindings = cons(symbol, frame->bindings);
    parameters = cdr(parameters);
  }

  return eval(firstCode, makeFrame(frame));
}

Value *evalEach(Value *args, Frame *frame)
{
  if (args->type == NULL_TYPE)
  {
    return makeNull();
  }
  else
  {
    return cons(eval(car(args), frame), evalEach(cdr(args), frame));
  }
}

Value *applyClosure(Value *function, Value *args)
{

  Value *actualParameter = makeNull();
  Value *formalParamter = makeNull();
  Value *returnResult = makeNull();
  Value *match1 = makeNull();
  Value *match2 = makeNull();
  Value *codebody = function->cl.functionCode;

  formalParamter = function->cl.paramNames;
  int typeofVal = INT_MAX; // never goes to while loop
  if (args->type == CONS_TYPE)
  {
    typeofVal = args->type;                   // go into loop
    formalParamter = function->cl.paramNames; // only set when in while loop
  }
  while (formalParamter->type == CONS_TYPE)
  {
    match1 = car(formalParamter);
    match2 = car(args);
    match2 = cons(match1, match2);
    actualParameter = cons(match2, actualParameter);
    // next
    formalParamter = cdr(formalParamter);
    args = cdr(args);
  }
  Frame *closure = makeFrame(function->cl.frame);
  closure->bindings = actualParameter;

  return eval(codebody, closure);
}

Value *applyPrimitive(Value *primitive, Value *args)
{
  return primitive->pf(args);
}

Value *primitiveAdd(Value *args)
{
  Value *first = car(args);
  Value *second = cdr(args);

  if (second->type == NULL_TYPE)
  {
    return first;
  }
  else
  {
    Value *result = makeNull();
    if (first->type == INT_TYPE)
    {
      result->type = INT_TYPE;
      result->i = first->i + primitiveAdd(second)->i;
    }
    else
    {
      result->type = DOUBLE_TYPE;
      result->d = first->d + primitiveAdd(second)->d;
    }
    return result;
  }
}

Value *primitiveNull(Value *args)
{
  Value *isNull = makeNull();
  isNull->type = BOOL_TYPE;

  if (args->type == NULL_TYPE)
  {
    isNull->i = 1;
  }
  if (args->type == CONS_TYPE)
  {
    if (car(args)->type == NULL_TYPE)
      isNull->i = 1;
    else
      isNull->i = 0;
  }
  else
  {
    isNull->i = 0;
  }

  return isNull;
}

Value *primitiveCar(Value *args)
{

  if (args->type == CONS_TYPE)
  {
    if (car(args)->type == CONS_TYPE)
    {
      return car(car(args));
    }
    else
    {
      return car(args);
    }
  }
  else
  {
    return args;
  }
}

Value *primitiveCdr(Value *args)
{
  Value *argsPointer = args;
  if (argsPointer->type == CONS_TYPE)
  {
    if (car(argsPointer)->type == CONS_TYPE)
    {
      return cdr(car(argsPointer));
    }
    else
    {
      return cdr(argsPointer);
    }
  }
  else
  {
    printf("Evaluation Error: not a list.");
    return makeNull();
  }
}

Value *primitiveCons(Value *args)
{
  Value *dot = makeNull();
  dot->type = DOT_TYPE;
  dot->c.car = car(args);
  dot->c.cdr = car(cdr(args));
  Value *notdot = cons(car(args), car(cdr(args)));

  if ((cdr(args)->type == CONS_TYPE) || ((car(cdr(args))->type != 0)))
  {
    return notdot;
  }
  return dot;
}

Value *evalAnd(Value *args, Frame *frame)
{
  while (args->type == CONS_TYPE)
  {
    if (eval(car(args), frame)->i == 0)
    { // if it's false.
      return eval(car(args), frame);
    }
    args = cdr(args);
  }
  Value *trueValue = makeNull();
  trueValue->type = BOOL_TYPE;
  trueValue->i = 1;
  return trueValue;
}

Value *evalOr(Value *args, Frame *frame)
{
  while (args->type == CONS_TYPE)
  {
    if (eval(car(args), frame)->i == 1)
    { // if it's true.
      return eval(car(args), frame);
    }
    args = cdr(args);
  }
  Value *falseValue = makeNull();
  falseValue->type = BOOL_TYPE;
  falseValue->i = 0;
  return falseValue;
}

// Works! Amazing I'm so proud of myself I thought this was gonna suck!!
Value *evalLetStar(Value *args, Frame *frame)
{
  Value *parameters = args->c.car; // parameters
  Value *code = args->c.cdr;       // body of code
  Value *firstCode = car(cdr(args));

  while (parameters->type == CONS_TYPE)
  {

    Value *variable = car(car(parameters));
    Value *value = eval(car(cdr(car(parameters))), frame);
    Value *symbol = cons(variable, value);
    frame->bindings = cons(symbol, frame->bindings);
    parameters = cdr(parameters);
    frame = makeFrame(frame);     // Makes new frame and assigns it.
    frame->bindings = makeNull(); // Adds the start of new bindings.
  }
  return eval(firstCode, frame);
}

Value *evalLetRec(Value *args, Frame *frame)
{
  Value *parameters = args->c.car; // parameters
  Value *code = args->c.cdr;       // body of code
  Value *firstCode = car(cdr(args));
  Frame *letRecFrame = makeFrame(frame); // needs new frame for evaluation, sets parent frame to the input frame.
  Value *unspecified = makeNull();
  unspecified->type = UNSPECIFIED_TYPE;

  while (parameters->type == CONS_TYPE)
  {
    Value *variable = car(car(parameters));
    Value *value = car(cdr(car(parameters))); // does not evaluate value so it doesn't throw error from circle dependencies.
    Value *symbol = cons(variable, value);
    frame->bindings = cons(symbol, frame->bindings);
    parameters = cdr(parameters);
  }
  while (parameters->type == CONS_TYPE)
  {
    Value *evaluatedCode = cons(eval(car(args), letRecFrame), evaluatedCode);
    Frame *childFrame = makeFrame(NULL);
    childFrame->bindings = evaluatedCode;
  }

  return eval(firstCode, letRecFrame);
}

// Works as far as I can tell.
Value *evalSet(Value *args, Frame *frame)
{
  Frame *currentFrame = frame;

  while (currentFrame != NULL)
  {
    Value *bindings = currentFrame->bindings;

    while (bindings->type == CONS_TYPE)
    {
      Value *variable = car(bindings);
      if (!strcmp(car(variable)->s, car(args)->s))
      {
        variable->c.cdr = car(cdr(args));
        return makeNull();
      }
      bindings = cdr(bindings);
    }
    currentFrame = currentFrame->parent;
  }
  printf("Evaluation Error: Symbol %s not found.", car(args)->s);
  texit(0);
  return makeNull();
}

Value *evalBegin(Value *args, Frame *frame)
{
  // Evaluate everything, only return last.
  Value *current = makeNull();
  while (args->type == CONS_TYPE)
  {
    current = eval(car(args), frame);
    args = cdr(args);
  }
  return current;
}

Value *primitiveSubtract(Value *args)
{
  Value *first = car(args);
  Value *second = cdr(args);

  if (second->type == NULL_TYPE)
  {
    return first;
  }
  else
  {
    Value *result = makeNull();
    if (first->type == INT_TYPE)
    {
      result->type = INT_TYPE;
      result->i = first->i - primitiveAdd(second)->i;
    }
    else
    {
      result->type = DOUBLE_TYPE;
      result->d = first->d - primitiveAdd(second)->d;
    }
    return result;
  }
}

Value *primitiveLessThan(Value *args)
{                           // <
  Value *first = car(args); // should be same type. I don't think we need to account for multiple types.

  Value *result = makeNull();
  if (first->type == INT_TYPE)
  {
    if (primitiveSubtract(args)->i < 0)
    {
      result->type = BOOL_TYPE;
      result->i = 1; // I believe 1 is true.
      return result;
    }
    else
    {
      result->type = BOOL_TYPE;
      result->i = 0;
      return result;
    }
  }
  else if (first->type == DOUBLE_TYPE)
  {
    if (primitiveSubtract(args)->d < 0)
    {
      result->type = BOOL_TYPE;
      result->i = 1;
      return result;
    }
    else
    {
      result->type = BOOL_TYPE;
      result->i = 0;
      return result;
    }
  }
  else
  {
    printf("Evaluation Error: Arguments in < not doubles or ints.");
    return result;
  }

  return result;
}

Value *primtiveGreaterThan(Value *args)
{                           // >
  Value *first = car(args); // should be same type. I don't think we need to account for multiple types.

  Value *result = makeNull();
  if (first->type == INT_TYPE)
  {
    if (primitiveSubtract(args)->i > 0)
    {
      result->type = BOOL_TYPE;
      result->i = 1; // I believe 1 is true.
      return result;
    }
    else
    {
      result->type = BOOL_TYPE;
      result->i = 0;
      return result;
    }
  }
  else if (first->type == DOUBLE_TYPE)
  {
    if (primitiveSubtract(args)->d > 0)
    {
      result->type = BOOL_TYPE;
      result->i = 1;
      return result;
    }
    else
    {
      result->type = BOOL_TYPE;
      result->i = 0;
      return result;
    }
  }
  else
  {
    printf("Evaluation Error: Arguments in < not doubles or ints.");
    return result;
  }

  return result;
}

Value *primtiveEqual(Value *args)
{ // =
  Value *isEqual = makeNull();
  isEqual->type = BOOL_TYPE;
  Value *first = car(args);
  Value *second = car(cdr(args));

  if (first->type == INT_TYPE)
  {
    if (first->i == second->i)
    {
      isEqual->i = 1;
    }
    else
    {
      isEqual->i = 0;
    }
  }
  if (first->type == DOUBLE_TYPE)
  {
    if (first->i == second->i)
    {
      isEqual->i = 1;
    }
    else
    {
      isEqual->i = 0;
    }
  }
  return isEqual;
}

void bind(char *name, Value *(*function)(struct Value *), Frame *frame)
{
  // Add primitive functions to top-level bindings list
  Value *value = talloc(sizeof(Value));
  value->type = PRIMITIVE_TYPE;
  value->pf = function;

  Value *symbol = talloc(sizeof(Value));
  symbol->type = SYMBOL_TYPE;
  symbol->s = name;

  Value *primitive = cons(symbol, value);
  frame->bindings = cons(primitive, frame->bindings);
}

Value *eval(Value *tree, Frame *frame)
{
  switch (tree->type)
  {
  case INT_TYPE:
  {
    return tree;
    break;
  }
  case STR_TYPE:
  {
    return tree;
    break;
  }
  case DOUBLE_TYPE:
  {
    return tree;
    break;
  }
  case BOOL_TYPE:
  {
    return tree;
    break;
  }
  case SYMBOL_TYPE:
  {
    return lookUpSymbol(tree, frame); // These are variables!! So like say earlier we had (define x 6) so x = 6. This has to find what x is in the frame!
    break;
  }
  case CONS_TYPE:
  {
    Value *first = car(tree);
    Value *args = cdr(tree);
    // Sanity and error checking on first...
    if (first->type == NULL_TYPE)
    { // NEW
      return first;
    }
    else if (!strcmp(first->s, "if"))
    {
      return evalIf(args, frame);
    }
    else if (!strcmp(first->s, "let"))
    {
      return evalLet(args, frame); // let makes a new frame.
    }
    else if (!strcmp(first->s, "quote"))
    {
      if (cdr(args)->type == NULL_TYPE)
      {
        return car(args);
      }
      else
      {
        printf("Evaluation error\n");
        texit(0);
      }
    }
    else if (!strcmp(first->s, "define"))
    {
      return evalDefine(args, frame);
    }
    else if (!strcmp(first->s, "lambda"))
    {
      return evalLambda(args, frame);
    }
    else if (!strcmp(first->s, "and"))
    {
      return evalAnd(args, frame);
    }
    else if (!strcmp(first->s, "or"))
    {
      return evalOr(args, frame);
    }
    else if (!strcmp(first->s, "let*"))
    {
      return evalLetStar(args, frame);
    }
    else if (!strcmp(first->s, "letrec"))
    {
      return evalLetRec(args, frame);
    }
    else if (!strcmp(first->s, "set!"))
    {
      return evalSet(args, frame);
    }
    else if (!strcmp(first->s, "begin"))
    {
      return evalBegin(args, frame);
    }
    else
    {
      // If not a special form, evaluate the first, evaluate the args, then
      // apply the first to the args.
      Value *evaledOperator = eval(first, frame);
      if (evaledOperator->type != PRIMITIVE_TYPE)
      {
        Value *evaledArgs = evalEach(args, frame);
        return applyClosure(evaledOperator, evaledArgs);
      }
      else
      {
        Value *evaledArgs = evalEach(args, frame);
        return applyPrimitive(evaledOperator, evaledArgs);
      }
    }
    // apply handles closures and primitives
    break;
  }
  case CLOSURE_TYPE:
    break;
  case OPENBRACKET_TYPE:
    break;
  case CLOSEBRACKET_TYPE:
    break;
  case DOT_TYPE:
    break;
  case SINGLEQUOTE_TYPE:
    break;
  case VOID_TYPE:
    break;
  case OPEN_TYPE:
    break;
  case CLOSE_TYPE:
    break;
  case NULL_TYPE:
    return tree;
  case PTR_TYPE:
    break;
  case PRIMITIVE_TYPE:
    break;
  case UNSPECIFIED_TYPE:
    break;
  }
  return tree;
}

void interpret(Value *tree)
{
  // Make top-level bindings list
  Frame *frame = makeFrame(NULL);
  frame->bindings = makeNull();

  bind("+", primitiveAdd, frame);
  bind("null?", primitiveNull, frame);
  bind("car", primitiveCar, frame);
  bind("cdr", primitiveCdr, frame);
  bind("cons", primitiveCons, frame);
  bind("-", primitiveSubtract, frame);
  bind("<", primitiveLessThan, frame);
  bind(">", primtiveGreaterThan, frame);
  bind("=", primtiveEqual, frame);

  Value *interpretted = makeNull(); // list of evaluated things.

  while (tree->type == CONS_TYPE)
  {
    Value *first = tree->c.car;
    Value *rest = tree->c.cdr;
    interpretted = cons(eval(first, frame), makeNull());
    Value *please = car(interpretted);
    if (please->type == CONS_TYPE)
    {
      printf("(");
    }
    displayToken1(interpretted);
    if (please->type == CONS_TYPE)
    {
      printf(")");
    }
    tree = rest; // going to the next S-expression.
  }
}

void displayToken1(Value *token)
{
  // taken from parser
  // same as display but doesn't show type. Just the value, not type displayed.
  switch (token->type)
  {
  case INT_TYPE:
    printf("%i ", token->i);
    break;
  case DOUBLE_TYPE:
    printf("%f ", token->d);
    break;
  case STR_TYPE:
    printf("%s ", token->s);
    break;
  case CONS_TYPE:
    // printf("(");
    displayToken1(token->c.car);
    if (token->c.cdr->type != CONS_TYPE && token->c.cdr->type != NULL_TYPE)
    { // check for dots
      printf(". ");
    }
    displayToken1(token->c.cdr);
    // printf(")");
    break;
  case NULL_TYPE:
    // printf("NULL ");
    break;
  case PTR_TYPE:
    printf("%p ", token->p);
    break;
  case OPEN_TYPE:
    printf("%s ", token->s);
    break;
  case CLOSE_TYPE:
    printf("%s ", token->s);
    break;
  case BOOL_TYPE:
    if (token->i == 0)
    {
      printf("#f ");
    }
    else
    {
      printf("#t ");
    }
    break;
  case SYMBOL_TYPE:
    printf("%s ", token->s);
    break;
  case OPENBRACKET_TYPE:
    break;
  case CLOSEBRACKET_TYPE:
    break;
  case DOT_TYPE:
    displayToken1(token->c.car);
    printf("this is broken currently trying to dsiplay dot type which should never happen\n");
    printf(" . ");
    displayToken1(token->c.cdr);
    break;
  case SINGLEQUOTE_TYPE:
    break;
  case VOID_TYPE:
    break;
  case CLOSURE_TYPE:
    break;
  case PRIMITIVE_TYPE:
    break;
  case UNSPECIFIED_TYPE:
    break;
  }
}
#endif