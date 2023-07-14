module Vl.Algo where

import Data.List qualified as List
import Data.List.Extra qualified as List
import Data.Map qualified as Map
import Data.Set qualified as Set

import Relude

import Vl.Lens

data Node k v
  = Node
      { _key      :: k
      , _adjLists :: Set.Set k
      , _value    :: v
      }
makeFieldsNoPrefix ''Node

-- | FIXME: probably busted
topologicalSortByDfs :: forall k v. (Ord k, Eq k) => [Node k v] -> [Node k v]
topologicalSortByDfs graph = executingState @[Node k v] [] $ visitAll graph
  where
  visitAll :: [Node k v] -> State [Node k v] ()
  visitAll nodes = do
    filterM isUnvisited nodes >>= \case
      []     -> pass -- terminate
      (x:xs) -> visit [] x *> visitAll xs -- x must already been visited, so skip it for less milliseconds

  lookupGraph :: k -> Maybe (Node k v)
  lookupGraph k = List.find (\node -> node^.key == k) graph

  lookupNeighbors :: Node k v -> [Node k v]
  lookupNeighbors node = mapMaybe lookupGraph (Set.toList (node^.adjLists))

  nodeEqual :: Node k v -> Node k v -> Bool
  nodeEqual a b = a^.key == b^.key

  isIn :: [Node k v] -> Node k v -> Bool
  isIn list node = List.notNull $ filter (nodeEqual node) list

  isVisited :: Node k v -> State [Node k v] Bool
  isVisited node = do
    visited <- get
    pure $ isIn visited node

  isUnvisited :: Node k v -> State [Node k v] Bool
  isUnvisited = fmap not . isVisited

  visit :: [Node k v] -> Node k v -> State [Node k v] ()
  visit path this = do
    nexts <- filterM isUnvisited $ filter (not . isIn path) $ lookupNeighbors this
    traverse_ (visit (this : path)) nexts
    modify (this :)
