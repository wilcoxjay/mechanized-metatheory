Module Type MAP.
  Parameter key value : Type.
  Parameter t : Type.

  Parameter empty : t.

  Parameter get : key -> t -> option value.
  Parameter shadow : key -> value -> t -> t.
  Parameter delete : key -> t -> t.

  Axiom get_empty : 
    forall k, get k empty = None.

  Axiom get_shadow_same : 
    forall k v m, 
      get k (shadow k v m) = Some v.
  Axiom get_shadow_diff : 
    forall k k' v m, 
      k <> k' -> 
      get k' (shadow k v m) = get k' m.

  Axiom get_delete_same : 
    forall k m, 
      get k (delete k m) = None.
  Axiom get_delete_diff : 
    forall k k' m, 
      k <> k' -> 
      get k' (delete k m) = get k' m.

  Axiom delete_shadow_same : 
    forall k v m, 
      delete k (shadow k v m) = delete k m.
  Axiom delete_shadow_diff : 
    forall k' k v m, 
      k <> k' -> 
      delete k' (shadow k v m) = shadow k v (delete k' m).

  Axiom delete_empty : 
    forall k, 
      delete k empty = empty.
End MAP.
