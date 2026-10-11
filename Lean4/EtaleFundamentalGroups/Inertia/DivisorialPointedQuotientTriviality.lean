/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Inertia.DivisorialPointedQuotientEndpoint

/-!
# Triviality from pointed divisorial quotients

The actual pointed finite-cover quotient recovers normalization-prime ideal
inertia after the canonical deck-group and base-point conjugation transports.
Consequently, coprimality of its finite image with every prime forces ideal
inertia to be trivial.

The declarations live in `DivisorialPointedQuotientEndpoint` so that the
comparison, range transport, and triviality proofs share one local instance
graph.  This module is the narrow compatibility facade for that API.
-/
