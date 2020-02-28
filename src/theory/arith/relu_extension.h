/*********************                                                        */
/*! \file relu_extension.h
 ** \verbatim
 ** Top contributors (to current version):
 ** Ahmed Irfan, Aleksandar Zeljic, Andrew Reynolds, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Extensions for handling of relu functions.
 **
 ** Extensions to the theory of arithmetic handling of relu functions
 ** via axiom instantiations. (TODO:?)
 **/

#ifndef CVC4__THEORY__ARITH__RELU_EXTENSION_H
#define CVC4__THEORY__ARITH__RELU_EXTENSION_H

#include <stdint.h>

#include <map>
#include <queue>
#include <set>
#include <unordered_map>
#include <utility>
#include <vector>

#include "context/cdhashset.h"
#include "context/cdinsert_hashmap.h"
#include "context/cdlist.h"
#include "context/cdqueue.h"
#include "context/context.h"
#include "expr/kind.h"
#include "expr/node.h"
#include "theory/arith/nl_lemma_utils.h"
#include "theory/arith/nl_model.h"
#include "theory/arith/theory_arith.h"
#include "theory/uf/equality_engine.h"

namespace CVC4 {
namespace theory {
namespace arith {

typedef std::map<Node, unsigned> NodeMultiset;

// TODO : refactor/document this class (#1287)
/** Relu extension class
 *
 * This class implements model-based refinement schemes
 * for non-linear arithmetic, described in:
 * relu4.pdf
 *
 * It's main functionality is a check(...) method,
 * which is called by TheoryArithPrivate either:
 * TODO: Will we need a different class to call this file?
 * (1) at full effort with no conflicts or lemmas emitted, or TODO: Probably won't need this
 * (2) at last call effort.
 * In this method, this class calls d_out->lemma(...)
 * for valid arithmetic theory lemmas, based on the current set of assertions,
 * where d_out is the output channel of TheoryArith.
 */
class ReluExtension {
 public:
  ReluExtension(TheoryArith& containing, eq::EqualityEngine* ee); //TODO: Do we need equality engine?
  ~ReluExtension();
  /** Get current substitution MAYBE
   *
   * This function and the one below are
   * used for context-dependent
   * simplification, see Section 3.1 of
   * "Designing Theory Solvers with Extensions"
   * by Reynolds et al. FroCoS 2017.
   *
   * effort : an identifier indicating the stage where
   *          we are performing context-dependent simplification,
   * vars : a set of arithmetic variables.
   *
   * This function populates subs and exp, such that for 0 <= i < vars.size():
   *   ( exp[vars[i]] ) => vars[i] = subs[i]
   * where exp[vars[i]] is a set of assertions
   * that hold in the current context. We call { vars -> subs } a "derivable
   * substitution" (see Reynolds et al. FroCoS 2017).
   */
  bool getCurrentSubstitution(int effort, const std::vector<Node>& vars,
                              std::vector<Node>& subs,
                              std::map<Node, std::vector<Node> >& exp);
  /** Is the term n in reduced form? MAYBE
   *
   * Used for context-dependent simplification.
   *
   * effort : an identifier indicating the stage where
   *          we are performing context-dependent simplification,
   * on : the original term that we reduced to n,
   * exp : an explanation such that ( exp => on = n ).
   *
   * We return a pair ( b, exp' ) such that
   *   if b is true, then:
   *     n is in reduced form
   *     if exp' is non-null, then ( exp' => on = n )
   * The second part of the pair is used for constructing
   * minimal explanations for context-dependent simplifications.
   */
  std::pair<bool, Node> isExtfReduced(int effort, Node n, Node on,
                                      const std::vector<Node>& exp) const;
  /** Check at effort level e.
   *
   * This call may result in (possibly multiple) calls to d_out->lemma(...)
   * where d_out is the output channel of TheoryArith.
   *
   * If e is FULL, then we attempt to fix assigments to satisfy ReLUs.
   * If e is LAST_CALL, add lemmas based on ReLU case-splitting
   */
  void check(Theory::Effort e);
  /** intercept model
   *
   * This method is called during TheoryArith::collectModelInfo, which is
   * invoked after the linear arithmetic solver passes a full effort check
   * with no lemmas.
   *
   * The argument arithModel is a map of the form { v1 -> c1, ..., vn -> cn }
   * which represents the linear arithmetic theory solver's contribution to the
   * current candidate model. That is, its collectModelInfo method is requesting
   * that equalities v1 = c1, ..., vn = cn be added to the current model, where
   * v1, ..., vn are arithmetic variables and c1, ..., cn are constants. Notice
   * arithmetic variables may be real-valued terms belonging to other theories,
   * or abstractions of applications of multiplication.
   *
   * This method requests that the non-linear solver inspect this model and
   * do any number of the following:
   * (1) Attempt to trivially fix broken ReLUs
   * (2) FIX broken RELU constraints and all known phases and ask for assignment.
   *
   * REVISIT Notice that in the former case, the lemmas it constructs are not sent out
   * immediately. Instead, they are put in temporary vectors d_cmiLemmas
   * and d_cmiLemmasPp, which are then sent out (if necessary) when a last call
   * effort check is issued to this class.
   */
  void interceptModel(std::map<Node, Node>& arithModel);
  /** Does this class need a call to check(...) at last call effort? */
  bool needsCheckLastEffort() const { return d_needsLastCall; }
  /** presolve
   *
   * This function is called during TheoryArith's presolve command.
   * In this function, we send lemmas we accumulated during preprocessing,
   * for instance, definitional lemmas from expandDefinitions are sent out
   * on the output channel of TheoryArith in this function.
   */
  void presolve();
 private:
  /** Model-based refinement
   *
   * This is the main entry point of this class for generating lemmas on the
   * output channel of the theory of arithmetic.
   *
   * It is currently run at last call effort. It applies lemma schemas
   * described in Reynolds et al. FroCoS 2017 that are based on ruling out
   * the current candidate model.
   *
   * This function returns true if a lemma was added to the vector lems/lemsPp.
   * Otherwise, it returns false. In the latter case, the model object d_model
   * may have information regarding how to construct a model, in the case that
   * we determined the problem is satisfiable.
   *
   * The argument lemSE is the "side effect" of the lemmas in mlems and mlemsPp
   * (for details, see checkLastCall).
   */
  bool modelBasedRefinement(std::vector<Node>& mlems,
                            std::vector<Node>& mlemsPp,
                            std::map<Node, NlLemmaSideEffect>& lemSE);

  typedef context::CDHashSet<Node, NodeHashFunction> NodeSet;

   // constraint information (context-independent)
  struct ConstraintInfo {
   public:
    Node d_rhs;
    Node d_coeff;
    Kind d_type;
  }; /* struct ConstraintInfo */

  /** check last call
   *
   * Check assertions for consistency in the effort LAST_CALL with a subset of
   * the assertions, false_asserts, that evaluate to false in the current model.
   *
   * xts : the list of (non-reduced) extended terms in the current context.
   *
   * REVISIT
   * This method adds lemmas to arguments lems, lemsPp, and wlems, each of
   * which are intended to be sent out on the output channel of TheoryArith
   * under certain conditions.
   *
   * If the set lems or lemsPp is non-empty, then no further processing is
   * necessary. The last call effort check should terminate and these
   * lemmas should be sent. The set lemsPp is distinguished from lems since
   * the preprocess flag on the lemma(...) call should be set to true.
   *
   * The "waiting" lemmas wlems contain lemmas that should be sent on the
   * output channel as a last resort. In other words, only if we are not
   * able to establish SAT via a call to checkModel(...) should wlems be
   * considered. This set typically contains tangent plane lemmas.
   *
   * The argument lemSE is the "side effect" of the lemmas from the previous
   * three calls. If a lemma is mapping to a side effect, it should be
   * processed via a call to processSideEffect(...) immediately after the
   * lemma is sent (if it is indeed sent on this call to check).
   */
  int checkLastCall(const std::vector<Node>& assertions,
                    const std::vector<Node>& false_asserts,
                    const std::vector<Node>& xts,
                    std::vector<Node>& lems,
                    std::vector<Node>& lemsPp,
                    std::vector<Node>& wlems,
                    std::map<Node, NlLemmaSideEffect>& lemSE);
  //---------------------------------------term utilities
  static bool isArithKind(Kind k);
  static Node mkLit(Node a, Node b, int status, bool isAbsolute = false);
  static Node mkBounded( Node l, Node a, Node u );
  //---------------------------------------end term utilities

  void registerConstraint(Node atom);
  /** assign order ids MAYBE*/
  void assignOrderIds(std::vector<Node>& vars,
                      NodeMultiset& d_order,
                      bool isConcrete,
                      bool isAbsolute);

  /** get assertions
   *
   * Let M be the set of assertions known by THEORY_ARITH. This function adds a
   * set of literals M' to assertions such that M' and M are equivalent.
   *
   * Examples of how M' differs with M:
   * (1) M' may not include t < c (in M) if t < c' is in M' for c' < c, where
   * c and c' are constants,
   * (2) M' may contain t = c if both t >= c and t <= c are in M.
   */
  void getAssertions(std::vector<Node>& assertions);
  /** check model
   *
   * Returns the subset of assertions whose concrete values we cannot show are
   * true in the current model.
   *
   */
  std::vector<Node> checkModelEval(const std::vector<Node>& assertions);

  //---------------------------check model
  /** Check model
   *
   * Checks the current model based on solving for equalities, and using error
   * bounds on the Taylor approximation.
   *
   * If this function returns true, then all assertions in the input argument
   * "assertions" are satisfied for all interpretations of variables within
   * their computed bounds (as stored in d_check_model_bounds).
   *
   * For details, see Section 3 of Cimatti et al CADE 2017 under the heading
   * "Detecting Satisfiable Formulas".
   *
   * The arguments lemmas and gs store the lemmas and guard literals to be sent
   * out on the output channel of TheoryArith as lemmas and calls to
   * ensureLiteral respectively.
   */
  bool checkModel(const std::vector<Node>& assertions,
                  const std::vector<Node>& false_asserts,
                  std::vector<Node>& lemmas,
                  std::vector<Node>& gs);
  //---------------------------end check model


  /**
   * Potentially adds lemmas to the set out and clears lemmas. Returns
   * the number of lemmas added to out. We do not add lemmas that have already
   * been sent on the output channel of TheoryArith.
   */
  unsigned filterLemmas(std::vector<Node>& lemmas, std::vector<Node>& out);
  /** singleton version of above */
  unsigned filterLemma(Node lem, std::vector<Node>& out);

  /**
   * Send lemmas in out on the output channel of theory of arithmetic.
   */
  void sendLemmas(const std::vector<Node>& out,
                  bool preprocess,
                  std::map<Node, NlLemmaSideEffect>& lemSE);
  /** Process side effect se */
  void processSideEffect(const NlLemmaSideEffect& se);



  /** cache of all lemmas sent on the output channel (user-context-dependent) */
  NodeSet d_lemmas;
  /** cache of terms t for which we have added the lemma ( t = 0 V t != 0 ). */
  NodeSet d_zero_split;

  /** commonly used terms */
  Node d_zero;
  Node d_true;
  Node d_false;

  // The theory of arithmetic containing this extension.
  TheoryArith& d_containing;

  // pointer to used equality engine
  eq::EqualityEngine* d_ee;
  // needs last call effort
  bool d_needsLastCall;

  // if d_c_info[lit][x] = ( r, coeff, k ), then ( lit <=>  (coeff * x) <k> r )
  std::map<Node, std::map<Node, ConstraintInfo> > d_c_info;
  std::map<Node, std::map<Node, bool> > d_c_info_maxm;
  std::vector<Node> d_constraints;

  // per last-call effort

  // model values/orderings

  /** The non-linear model object
   *
   * This class is responsible for computing model values for arithmetic terms
   * and for establishing when we are able to answer "SAT".
   */
  NlModel d_model;
 private:
  //per last-call effort check

  //-------------------------------------------- lemmas
  // ------------------------------------------- end lemma
}; /* class ReluExtension */

}  // namespace arith
}  // namespace theory
}  // namespace CVC4

#endif /* CVC4__THEORY__ARITH__RELU_EXTENSION_H */
