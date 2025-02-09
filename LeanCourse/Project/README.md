## Personal Info

Please fill out the following. Fill in the project topic once you have decided.
```
First & last name: Ruth Plümer
Project topic: Pushout of topological spaces
Partner (optional): /
```

## Contents of the project

The file 'Sample.lean' contains the main finished results of the formalization project, including
  * The definition of the Adjunction Space (AdjunctionSpace) and the topology on it (instTopologicalSpaceAdjunction). equivalence_of_images is the equivalence relation on the disjoint union used to define the Adjunction space.
  Note that there are two different descriptions of the adjunction space often found in the literature: one assumes that A (the subspace along which we glue one space to the other one) is a subset of X, the other assumes that A is a subspace of Y. In the project, it is assumed that A is a subspace of Y (or rather, that A and Y are distinct spaces and there is an embedding from A to Y).
  The two canonical maps into the adjunction space are called pushout_map_left and pushout_map_right in the formalization project.
  * Proofs of the universal properties of the disjoint union (univ_prop_coprod), the quotient space (univ_prop_quotSpace) and the adjunction space (univ_prop_adjunctionSpace).
  * A proof that the left canonical map into the pushout is an embedding (pushout_map_left_embd), using that it is both injective and inducing.
  * A proof that if A is closed in Y, the left canonical map into the pushout is a closed embedding
  (pushout_map_left_closedEmbd_if_subspace_closed)
  * A proof that if A is closed in Y, the the right canonical map into the pushout restricted to Y \setminus f2(A)
  is an open embedding (pushout_map_left_restrict_openEmbd_if_subspace_closed).
  * A proof that if f1 is a quotient map, so is the right canonical map into the pushout (pushout_map_right_quotmap_if).
  * A proof that if A is nonempty and X and Y are connected spaces, the adjunction space is connected as well (adjunction_connected_if_comps_connected)
  * A proof that f2(A) is closed in Y and X and Y are T1-Spaces, the adjunction space is a T1-space (adjunction_t1_if_comps_t1).

The file 'sideprojects.lean' contains some attempts of proofs for some other facts about pushouts in topological spaces that I couldn't finish to formalize, that is
  * The lemma that if X and Y are T4-spaces and f2(A) is closed in Y, the adjunction space is a T4-space as well
  (adjunction_t4_if_comps_t4). To prove this, one needs to apply the Tietze Extension theorem several times, so I proved a restated version of the Tietze Extension Theorem first.
  * The lemma that if X and Y are path connected and A is nonempty, the adjunction space is path connected as well (adjunction_path_connected_if_comps_path_connected). This turned out to be especially tough since paths are defined as continuous maps from UnitInterval to some topological space. To concatenate paths, one needs to re-define them as maps from [0, 1/2] and [1/2, 1], respectively, which is rather ugly because of the coercion issues.

While formalizing, I used the following resouces:
  * The wikipedia page on Adjunction Spaces (https://en.wikipedia.org/wiki/Adjunction_space)
  * The script 'General Topology' by Tammo tom Dieck (pp. 28-29). It uses a different notation than my project (in this script, A is assumed to be a subspace of X, not Y). Unfortunately, it contains some errors, for example the T1 and T4 property of the adjunction space hold only if A is a closed subspace of Y (or X with the notation of the script). The proofs for the more general statements as provided in the script are wrong.
  * I got stuck on proving preconnectedness when proving adjunction_connected_if_comps_connected and asked for help in the zulip forum (Thread : https://leanprover.zulipchat.com/#narrow/channel/113489-new-members/topic/Canonical.20way.20of.20proving.20connectedness.3F). The theorem preconnected_space_iff_clopen I used in my project is not my own work, but something another user suggested and I do not fully comprehend it.
