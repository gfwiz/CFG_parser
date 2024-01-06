module FinalProject01 where

import Control.Applicative(liftA, liftA2, liftA3)
import Data.List

import CFGParsing

bottomUp :: (Eq nt, Eq t) => CFG nt t -> [t] -> [[ParseStep nt t]]
bottomUp cfg input =
  let (nts, ts, start, rules) = cfg in
  let startingConfig = ([], input) in
  let goalConfig = ([NoBar start], []) in
  parser [shift, reduce] rules startingConfig goalConfig
-------------------------------------------------------------------------------
-------------------------------------------------------------------------------
-- IMPORTANT: Please do not change anything above here.
--            Write all your code below this line.
-------------------------------------------------------------------------------
-------------------------------------------------------------------------------

--creates the setup for a top down parsing approach
topDown :: (Eq nt, Eq t) => CFG nt t -> [t] -> [[ParseStep nt t]]
topDown cfg input = 
    let (nts, ts, start, rules) = cfg in
    let startingConfig = ([NoBar start], input) in
    let goalConfig = ([], []) in
    parser [match, predict] rules startingConfig goalConfig

--creates the structure for a left corner approach
leftCorner :: (Eq nt, Eq t) => CFG nt t -> [t] -> [[ParseStep nt t]]
leftCorner cfg input = 
    let (nts, ts, start, rules) = cfg in
    let startingConfig = ([Bar start], input) in
    let goalConfig = ([], []) in
    parser [matchLC, shiftLC, predictLC, connectLC] rules startingConfig goalConfig

--appends the start parse step to the list of parse paths outputted by its helper function pathsToGoalCFG
parser :: (Eq nt, Eq t) =>
          [[RewriteRule nt t] -> Config nt t -> [ParseStep nt t]] ->
          [RewriteRule nt t] -> Config nt t -> Config nt t ->
          [[ParseStep nt t]]                                   
parser transitions rules startConfig goalConfig =
    --append the inital parse step to the beginning of all valid parse paths
    map (ParseStep NoTransition NoRule startConfig:) (pathsToGoalCFG transitions rules startConfig goalConfig [])
  
--creates a list of all possible parse paths
pathsToGoalCFG :: (Eq nt, Eq t) =>
                  [[RewriteRule nt t] -> Config nt t -> [ParseStep nt t]] ->
                  [RewriteRule nt t] -> Config nt t -> Config nt t -> [ParseStep nt t] ->
                  [[ParseStep nt t]]
pathsToGoalCFG transitions rules config goalConfig steps 
  | steps == [] && config == goalConfig = [[]]
  --checks to see if the last step in the list of steps is the goal config
  | steps /= [] && getConfig (last steps) == goalConfig = [steps]
  -- applies pathsToGoalCFG to all possible next steps
  | otherwise = concatMap (\nextStep -> pathsToGoalCFG transitions rules (getConfig nextStep) goalConfig (steps ++ [nextStep])) (applyTransitions transitions rules config)

--runs all the transitions on a given config and returns a list of all the possible parse steps
applyTransitions :: (Eq nt, Eq t) => [[RewriteRule nt t] -> Config nt t -> [ParseStep nt t]] -> [RewriteRule nt t] -> Config nt t -> [ParseStep nt t]
applyTransitions transitions rules config = concatMap (\transFunc -> transFunc rules config) transitions

--implementations of different transitions for use in parser
--processes TRules and checks if the t in the TRules matches the head of the input list
--if it does then it creates a parse step which removes the t from the input list and adds the nt to the stack
shift :: (Eq nt, Eq t) => [RewriteRule nt t] -> Config nt t -> [ParseStep nt t]
shift [] _ = []
shift (NTRule nt nts:restRules) (stack, input) = shift restRules (stack, input)
shift (NoRule:restRules) (stack, input) = shift restRules (stack, input)
shift (TRule nt t:restRules) (stack, input)
  | input /= [] && t == (head input) = [ParseStep Shift (TRule nt t) ((stack++[NoBar nt]), tail input)] ++ shift restRules (stack, input)
  | otherwise = shift restRules (stack, input)
       
--processes NTRules and checks if the the last n elements on the stack are the same as the rhs of the NTRule
--if they are the same then it creates a parse step which removes the last n elements of the stack and adds the lhs of the NTRule to the stack
reduce :: (Eq nt, Eq t) => [RewriteRule nt t] -> Config nt t -> [ParseStep nt t]
reduce [] _ = []
reduce (TRule nt t:restRules) (stack, input) = reduce restRules (stack, input)
reduce (NoRule:restRules) (stack, input) = reduce restRules (stack, input)
reduce (NTRule nt nts:restRules) (stack, input)
--checks too see if all elements of the rhs of the NTRule are the same as the last elements of the stack
  | length stack >= length nts && nts == (drop (length stack - length nts) (removeBar stack)) = [ParseStep Reduce (NTRule nt nts) ((take (length stack - (length nts)) stack)++(addNoBar [nt]), input)] ++ reduce restRules (stack, input) 
  | otherwise = reduce restRules (stack, input)

--checks the stack and the input list and if the t in the TRules matches the head of the input list and the nt in the TRule matches the head of the stack
--then it creates a parse step that removes the t from the input list and the nt from the stack
match :: (Eq nt, Eq t) => [RewriteRule nt t] -> Config nt t -> [ParseStep nt t]
match [] _ = []
match (NTRule nt nts:restRules) (stack, input) = match restRules (stack, input)
match (NoRule:restRules) (stack, input) = match restRules (stack, input)
match (TRule nt t:restRules) (stack, input)
  | input /= [] && length stack >= 1 && NoBar nt == (head stack) && t == head input = [ParseStep Match (TRule nt t) (tail stack, tail input)] ++ match restRules (stack, input)
  | otherwise = match restRules (stack, input)
  
--processes NTRules and predicts that if the first element on the stack is the same as lhs of NTRule then it will add the rhs of the NTRule to the stack
predict :: (Eq nt, Eq t) => [RewriteRule nt t] -> Config nt t -> [ParseStep nt t]
predict [] _ = []
predict (TRule nt t:restRules) (stack, input) = predict restRules (stack, input)
predict (NoRule:restRules) (stack, input) = predict restRules (stack, input)
predict (NTRule nt nts:restRule) (stack, input)
  | length stack >= 2 && NoBar nt == (head stack) = [ParseStep Predict (NTRule nt nts) ((addNoBar (nts)) ++ tail stack, input)] ++ predict restRule (stack, input)
  | otherwise = predict restRule (stack, input)

--same as the match function but now utilizes the Bar notation for nonterminals
--checks to see if the first element of the stack is the barred nt of terminal rule
matchLC :: (Eq nt, Eq t) => [RewriteRule nt t] -> Config nt t -> [ParseStep nt t]
matchLC [] _ = []
matchLC (NTRule nt nts:restRules) (stack, input) = matchLC restRules (stack, input)
matchLC (NoRule:restRules) (stack, input) = matchLC restRules (stack, input)
matchLC (TRule nt t:restRules) (stack, input)
  | input /= [] && length stack >= 1 && (head stack) == Bar nt && t == head input = [ParseStep Match (TRule nt t) (tail stack, tail input)] ++ matchLC restRules (stack, input)
  | otherwise = matchLC restRules (stack, input)

--same as the shift function but now utilizes the Bar notation for nonterminals
shiftLC :: (Eq nt, Eq t) => [RewriteRule nt t] -> Config nt t -> [ParseStep nt t]
shiftLC [] _ = []
shiftLC (NTRule nt nts:restRules) (stack, input) = shiftLC restRules (stack, input)
shiftLC (NoRule:restRules) (stack, input) = shiftLC restRules (stack, input)
shiftLC (TRule nt t:restRules) (stack, input)
  | input /= [] && length stack == 1 && t == (head input) = [ParseStep Shift (TRule nt t) (([NoBar nt] ++ stack), tail input)] ++ shiftLC restRules (stack, input)
  | otherwise = shiftLC restRules (stack, input)


--is ran when no possible shift, matches, or connects are possible
--checks to see if the top of the stack contains the first nonterminal in the rhs of a NTRule, (head nts)
--if it is, then it predicts that this rule is correct and adds the rest of the rhs rule to the stack and the lhs
predictLC :: (Eq nt, Eq t) => [RewriteRule nt t] -> Config nt t -> [ParseStep nt t]
predictLC [] _ = []
predictLC (TRule nt t:restRules) (stack, input) = predictLC restRules (stack, input)
predictLC (NoRule:restRules) (stack, input) = predictLC restRules (stack, input)
predictLC (NTRule nt nts:restRules) (stack, input)
  | length stack >= 2 && (head stack) == NoBar (head nts) = [ParseStep Predict (NTRule nt nts) (addBars (tail nts) ++ [NoBar nt] ++ (tail stack), input)] ++ predictLC restRules (stack, input)
  | otherwise = predictLC restRules (stack, input)

--checks to see if the top of the stack contains the first nonterminal in the rhs of a NTRule, (head nts)
--if so it also checks if the next item in the stack is the same as the lhs of a NTRule, nt
--then it creates a parse step which removes the top two items from the stack, (head nts) and nt, and adds the rest of the rhs of the NTRule to the stack
connectLC :: (Eq nt, Eq t) => [RewriteRule nt t] -> Config nt t -> [ParseStep nt t]
connectLC [] _ = []
connectLC (TRule nt t:restRules) (stack, input) = connectLC restRules (stack, input)
connectLC (NoRule:restRules) (stack, input) = connectLC restRules (stack, input)
connectLC (NTRule nt nts:restRules) (stack, input)
  | length stack >= 2 && (head stack) == NoBar (head nts) && (head (tail stack)) == Bar nt = [ParseStep Connect (NTRule nt nts) (addBars (tail nts) ++ (drop 2 stack) , input)] ++ connectLC restRules (stack, input)
  | otherwise = connectLC restRules (stack, input)

--removes the bar notation from a nonterminal node, for comparison purposes within transition functions
removeBar :: [Stack nt] -> [nt]
removeBar [] = []
removeBar (nt:ts) = case nt of
                      Bar nt1 -> [nt1] ++ (removeBar ts)
                      NoBar nt1 -> [nt1] ++ (removeBar ts)

--adds NoBar to a list of nonterminal nodes to add to stack in transitions
addNoBar :: [nt] -> [Stack nt]
addNoBar [] = []
addNoBar (nt1:nts) = [NoBar nt1] ++ (addNoBar nts)

--add Bar to a list of nonterminal nodes to add to stack in transitions
addBars :: [nt] -> [Stack nt]
addBars [] = []
addBars (nt1:nts) = [Bar nt1] ++ (addBars nts)

--warmup questions
isRuleCNF :: RewriteRule nt t -> Bool
isRuleCNF (NTRule nt [nt1, nt2]) = True
isRuleCNF (TRule nt t) = True
isRuleCNF (NoRule) = True
isRuleCNF _ = False

isCNF :: CFG nt t -> Bool
isCNF (nts, ts, i, rs) = all isRuleCNF rs

pathsToGoalFSA :: (Eq st, Eq sy) =>((st,[sy]), [(st,[sy])]) -> [(st,sy,st)] ->[(st,[sy])] -> [[(st,[sy])]]
pathsToGoalFSA (current, history) rules fs =
  case elem current fs of
    True -> [history ++ [current]]
    False -> case consumeFSA rules (head [current]) of
              [] -> []
              (x:xs) -> pathsToGoalFSA (x, history++[current]) rules fs ++ case xs of 
                                                                            [] -> []
                                                                            _ -> pathsToGoalFSA ((head xs), history ++ [current]) rules fs
