/*********************                                                        */
/*! \file nonlinear_extension.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Ahmed Irfan, Aleksandar Zeljic, Andrew Reynolds, Tim King, Aina Niemetz
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

#include "theory/arith/relu_extension.h"

#include <cmath>
#include <set>

#include "expr/node_algorithm.h"
#include "expr/node_builder.h"
#include "options/arith_options.h"
#include "theory/arith/arith_msum.h"
#include "theory/arith/arith_utilities.h"
#include "theory/arith/theory_arith.h"
#include "theory/ext_theory.h"
#include "theory/quantifiers/quant_util.h"
#include "theory/theory_model.h"

using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace arith {

namespace {

// Return true if a collection c contains an elem k. Compatible with map and set
// containers.
template <class Container, class Key>
bool Contains(const Container& c, const Key& k) {
  return c.find(k) != c.end();
}

// Inserts value into the set/map c if the value was not present there. Returns
// true if the value was inserted.
template <class Container, class Value>
bool InsertIfNotPresent(Container* c, const Value& value) {
  return (c->insert(value)).second;
}

// Returns true if a vector c contains an elem t.
template <class T>
bool IsInVector(const std::vector<T>& c, const T& t) {
  return std::find(c.begin(), c.end(), t) != c.end();
}

// Returns the a[key] and assertion fails in debug mode.
inline unsigned getCount(const NodeMultiset& a, Node key) {
  NodeMultiset::const_iterator it = a.find(key);
  Assert(it != a.end());
  return it->second;
}

// Returns a[key] if key is in a or value otherwise.
unsigned getCountWithDefault(const NodeMultiset& a, Node key, unsigned value) {
  NodeMultiset::const_iterator it = a.find(key);
  return (it == a.end()) ? value : it->second;
}

// Returns true if for any key then a[key] <= b[key] where the value for any key
// not present is interpreted as 0.
bool isSubset(const NodeMultiset& a, const NodeMultiset& b) {
  for (NodeMultiset::const_iterator it_a = a.begin(); it_a != a.end(); ++it_a) {
    Node key = it_a->first;
    const unsigned a_value = it_a->second;
    const unsigned b_value = getCountWithDefault(b, key, 0);
    if (a_value > b_value) {
      return false;
    }
  }
  return true;
}

// Given two multisets return the multiset difference a \ b.
NodeMultiset diffMultiset(const NodeMultiset& a, const NodeMultiset& b) {
  NodeMultiset difference;
  for (NodeMultiset::const_iterator it_a = a.begin(); it_a != a.end(); ++it_a) {
    Node key = it_a->first;
    const unsigned a_value = it_a->second;
    const unsigned b_value = getCountWithDefault(b, key, 0);
    if (a_value > b_value) {
      difference[key] = a_value - b_value;
    }
  }
  return difference;
}

// Return a vector containing a[key] repetitions of key in a multiset a.
std::vector<Node> ExpandMultiset(const NodeMultiset& a) {
  std::vector<Node> expansion;
  for (NodeMultiset::const_iterator it_a = a.begin(); it_a != a.end(); ++it_a) {
    expansion.insert(expansion.end(), it_a->second, it_a->first);
  }
  return expansion;
}

void debugPrintBound(const char* c, Node coeff, Node x, Kind type, Node rhs) {
  Node t = ArithMSum::mkCoeffTerm(coeff, x);
  Trace(c) << t << " " << type << " " << rhs;
}

// REMOVE
struct SortNlModel
{
  SortNlModel()
      : d_nlm(nullptr),
        d_isConcrete(true),
        d_isAbsolute(false),
        d_reverse_order(false)
  {
  }
  /** pointer to the model */
  NlModel* d_nlm;
  /** are we comparing concrete model values? */
  bool d_isConcrete;
  /** are we comparing absolute values? */
  bool d_isAbsolute;
  /** are we in reverse order? */
  bool d_reverse_order;
  /** the comparison */
  bool operator()(Node i, Node j) {
    int cv = d_nlm->compare(i, j, d_isConcrete, d_isAbsolute);
    if (cv == 0) {
      return i < j;
    }
    return d_reverse_order ? cv < 0 : cv > 0;
  }
};


}  // namespace

ReluExtension::ReluExtension(TheoryArith& containing,
                                       eq::EqualityEngine* ee)
    : d_lemmas(containing.getUserContext()),
      d_zero_split(containing.getUserContext()),
      d_containing(containing),
      d_ee(ee),
      d_needsLastCall(false),
      d_model(containing.getSatContext()),
      d_builtModel(containing.getSatContext(), false)
{
  d_true = NodeManager::currentNM()->mkConst(true);
  d_false = NodeManager::currentNM()->mkConst(false);
  d_zero = NodeManager::currentNM()->mkConst(Rational(0));
  d_order_points.push_back(d_zero);
}

ReluExtension::~ReluExtension() {}

// Returns a reference to either map[key] if it exists in the map
// or to a default value otherwise.
//
// Warning: special care must be taken if value is a temporary object.
template <class MapType, class Key, class Value>
const Value& FindWithDefault(const MapType& map, const Key& key,
                             const Value& value) {
  typename MapType::const_iterator it = map.find(key);
  if (it == map.end()) {
    return value;
  }
  return it->second;
}

  // REMOVE?
bool ReluExtension::getCurrentSubstitution(
    int effort, const std::vector<Node>& vars, std::vector<Node>& subs,
    std::map<Node, std::vector<Node> >& exp) {
  // get the constant equivalence classes
  std::map<Node, std::vector<int> > rep_to_subs_index;

  bool retVal = false;
  for (unsigned i = 0; i < vars.size(); i++) {
    Node n = vars[i];
    if (d_ee->hasTerm(n)) {
      Node nr = d_ee->getRepresentative(n);
      if (nr.isConst()) {
        subs.push_back(nr);
        Trace("nl-subs") << "Basic substitution : " << n << " -> " << nr
                         << std::endl;
        exp[n].push_back(n.eqNode(nr));
        retVal = true;
      } else {
        rep_to_subs_index[nr].push_back(i);
        subs.push_back(n);
      }
    } else {
      subs.push_back(n);
    }
  }

  // return true if the substitution is non-trivial
  return retVal;

  // d_containing.getValuation().getModel()->getRepresentative( n );
}

std::pair<bool, Node> ReluExtension::isExtfReduced(
    int effort, Node n, Node on, const std::vector<Node>& exp) const {
  if (n != d_zero) {
    Kind k = n.getKind();
    return std::make_pair(k != NONLINEAR_MULT && !isTranscendentalKind(k),
                          Node::null());
  }
  Assert(n == d_zero);
  if (on.getKind() == NONLINEAR_MULT)
  {
    Trace("nl-ext-zero-exp") << "Infer zero : " << on << " == " << n
                             << std::endl;
    // minimize explanation if a substitution+rewrite results in zero
    const std::set<Node> vars(on.begin(), on.end());

    for (unsigned i = 0, size = exp.size(); i < size; i++)
    {
      Trace("nl-ext-zero-exp") << "  exp[" << i << "] = " << exp[i]
                               << std::endl;
      std::vector<Node> eqs;
      if (exp[i].getKind() == EQUAL)
      {
        eqs.push_back(exp[i]);
      }
      else if (exp[i].getKind() == AND)
      {
        for (const Node& ec : exp[i])
        {
          if (ec.getKind() == EQUAL)
          {
            eqs.push_back(ec);
          }
        }
      }

      for (unsigned j = 0; j < eqs.size(); j++)
      {
        for (unsigned r = 0; r < 2; r++)
        {
          if (eqs[j][r] == d_zero && vars.find(eqs[j][1 - r]) != vars.end())
          {
            Trace("nl-ext-zero-exp") << "...single exp : " << eqs[j]
                                     << std::endl;
            return std::make_pair(true, eqs[j]);
          }
        }
      }
    }
  }
  return std::make_pair(true, Node::null());
}


void ReluExtension::registerConstraint(Node atom) {
  if (!IsInVector(d_constraints, atom)) {
    d_constraints.push_back(atom);
    Trace("nl-ext-debug") << "Register constraint : " << atom << std::endl;
    std::map<Node, Node> msum;
    if (ArithMSum::getMonomialSumLit(atom, msum))
    {
      Trace("nl-ext-debug") << "got monomial sum: " << std::endl;
      if (Trace.isOn("nl-ext-debug")) {
        ArithMSum::debugPrintMonomialSum(msum, "nl-ext-debug");
      }
      unsigned max_degree = 0;
      std::vector<Node> all_m;
      std::vector<Node> max_deg_m;
      for (std::map<Node, Node>::iterator itm = msum.begin(); itm != msum.end();
           ++itm) {
        if (!itm->first.isNull()) {
          all_m.push_back(itm->first);
          registerMonomial(itm->first);
          Trace("nl-ext-debug2")
              << "...process monomial " << itm->first << std::endl;
          Assert(d_m_degree.find(itm->first) != d_m_degree.end());
          unsigned d = d_m_degree[itm->first];
          if (d > max_degree) {
            max_degree = d;
            max_deg_m.clear();
          }
          if (d >= max_degree) {
            max_deg_m.push_back(itm->first);
          }
        }
      }
      // isolate for each maximal degree monomial
      for (unsigned i = 0; i < all_m.size(); i++) {
        Node m = all_m[i];
        Node rhs, coeff;
        int res = ArithMSum::isolate(m, msum, coeff, rhs, atom.getKind());
        if (res != 0) {
          Kind type = atom.getKind();
          if (res == -1) {
            type = reverseRelationKind(type);
          }
          Trace("nl-ext-constraint") << "Constraint : " << atom << " <=> ";
          if (!coeff.isNull()) {
            Trace("nl-ext-constraint") << coeff << " * ";
          }
          Trace("nl-ext-constraint")
              << m << " " << type << " " << rhs << std::endl;
          d_c_info[atom][m].d_rhs = rhs;
          d_c_info[atom][m].d_coeff = coeff;
          d_c_info[atom][m].d_type = type;
        }
      }
      for (unsigned i = 0; i < max_deg_m.size(); i++) {
        Node m = max_deg_m[i];
        d_c_info_maxm[atom][m] = true;
      }
    } else {
      Trace("nl-ext-debug") << "...failed to get monomial sum." << std::endl;
    }
  }
}

bool ReluExtension::isReluKind(Kind k) {
  return k == RELU;
}

Node ReluExtension::mkLit(Node a, Node b, int status, bool isAbsolute)
{
  if (status == 0) {
    Node a_eq_b = a.eqNode(b);
    if (!isAbsolute)
    {
      return a_eq_b;
    }
    else
    {
      // return mkAbs( a ).eqNode( mkAbs( b ) );
      Node negate_b = NodeManager::currentNM()->mkNode(UMINUS, b);
      return a_eq_b.orNode(a.eqNode(negate_b));
    }
  } else if (status < 0) {
    return mkLit(b, a, -status);
  } else {
    Assert(status == 1 || status == 2);
    NodeManager* nm = NodeManager::currentNM();
    Kind greater_op = status == 1 ? GEQ : GT;
    if (!isAbsolute)
    {
      return nm->mkNode(greater_op, a, b);
    }
    else
    {
      // return nm->mkNode( greater_op, mkAbs( a ), mkAbs( b ) );
      Node zero = mkRationalNode(0);
      Node a_is_nonnegative = nm->mkNode(GEQ, a, zero);
      Node b_is_nonnegative = nm->mkNode(GEQ, b, zero);
      Node negate_a = nm->mkNode(UMINUS, a);
      Node negate_b = nm->mkNode(UMINUS, b);
      return a_is_nonnegative.iteNode(
          b_is_nonnegative.iteNode(nm->mkNode(greater_op, a, b),
                                   nm->mkNode(greater_op, a, negate_b)),
          b_is_nonnegative.iteNode(nm->mkNode(greater_op, negate_a, b),
                                   nm->mkNode(greater_op, negate_a, negate_b)));
    }
  }
}


Node ReluExtension::mkBounded( Node l, Node a, Node u ) {
  return NodeManager::currentNM()->mkNode(
      AND,
      NodeManager::currentNM()->mkNode(GEQ, a, l),
      NodeManager::currentNM()->mkNode(LEQ, a, u));
}
void ReluExtension::sendLemmas(const std::vector<Node>& out,
                                    bool preprocess,
                                    std::map<Node, NlLemmaSideEffect>& lemSE)
{
  std::map<Node, NlLemmaSideEffect>::iterator its;
  for (const Node& lem : out)
  {
    Trace("nl-ext-lemma") << "ReluExtension::Lemma : " << lem << std::endl;
    d_containing.getOutputChannel().lemma(lem, false, preprocess);
    // process the side effect
    its = lemSE.find(lem);
    if (its != lemSE.end())
    {
      processSideEffect(its->second);
    }
    // add to cache if not preprocess
    if (!preprocess)
    {
      d_lemmas.insert(lem);
    }
    // also indicate this is a tautology
    d_model.addTautology(lem);
  }
}

void ReluExtension::processSideEffect(const NlLemmaSideEffect& se)
{
  for (const std::tuple<Node, unsigned, Node>& sp : se.d_secantPoint)
  {
    Node tf = std::get<0>(sp);
    unsigned d = std::get<1>(sp);
    Node c = std::get<2>(sp);
    d_secant_points[tf][d].push_back(c);
  }
}

unsigned ReluExtension::filterLemma(Node lem, std::vector<Node>& out)
{
  Trace("nl-ext-lemma-debug")
      << "ReluExtension::Lemma pre-rewrite : " << lem << std::endl;
  lem = Rewriter::rewrite(lem);
  if (d_lemmas.find(lem) != d_lemmas.end()
      || std::find(out.begin(), out.end(), lem) != out.end())
  {
    Trace("nl-ext-lemma-debug")
        << "ReluExtension::Lemma duplicate : " << lem << std::endl;
    return 0;
  }
  out.push_back(lem);
  return 1;
}

unsigned ReluExtension::filterLemmas(std::vector<Node>& lemmas,
                                          std::vector<Node>& out)
{
  if (options::nlExtEntailConflicts())
  {
    // check if any are entailed to be false
    for (const Node& lem : lemmas)
    {
      Node ch_lemma = lem.negate();
      ch_lemma = Rewriter::rewrite(ch_lemma);
      Trace("nl-ext-et-debug")
          << "Check entailment of " << ch_lemma << "..." << std::endl;
      std::pair<bool, Node> et = d_containing.getValuation().entailmentCheck(
          options::TheoryOfMode::THEORY_OF_TYPE_BASED, ch_lemma);
      Trace("nl-ext-et-debug") << "entailment test result : " << et.first << " "
                               << et.second << std::endl;
      if (et.first)
      {
        Trace("nl-ext-et") << "*** Lemma entailed to be in conflict : " << lem
                           << std::endl;
        // return just this lemma
        if (filterLemma(lem, out) > 0)
        {
          lemmas.clear();
          return 1;
        }
      }
    }
  }

  unsigned sum = 0;
  for (const Node& lem : lemmas)
  {
    sum += filterLemma(lem, out);
  }
  lemmas.clear();
  return sum;
}

void ReluExtension::getAssertions(std::vector<Node>& assertions)
{
  Trace("nl-ext") << "Getting assertions..." << std::endl;
  NodeManager* nm = NodeManager::currentNM();
  // get the assertions
  std::map<Node, Rational> init_bounds[2];
  std::map<Node, Node> init_bounds_lit[2];
  unsigned nassertions = 0;
  std::unordered_set<Node, NodeHashFunction> init_assertions;
  for (Theory::assertions_iterator it = d_containing.facts_begin();
       it != d_containing.facts_end();
       ++it)
  {
    nassertions++;
    const Assertion& assertion = *it;
    Node lit = assertion.d_assertion;
    init_assertions.insert(lit);
    // check for concrete bounds
    bool pol = lit.getKind() != NOT;
    Node atom_orig = lit.getKind() == NOT ? lit[0] : lit;

    std::vector<Node> atoms;
    if (atom_orig.getKind() == EQUAL)
    {
      if (pol)
      {
        // t = s  is ( t >= s ^ t <= s )
        for (unsigned i = 0; i < 2; i++)
        {
          Node atom_new = nm->mkNode(GEQ, atom_orig[i], atom_orig[1 - i]);
          atom_new = Rewriter::rewrite(atom_new);
          atoms.push_back(atom_new);
        }
      }
    }
    else
    {
      atoms.push_back(atom_orig);
    }

    for (const Node& atom : atoms)
    {
      // non-strict bounds only
      if (atom.getKind() == GEQ || (!pol && atom.getKind() == GT))
      {
        Node p = atom[0];
        Assert(atom[1].isConst());
        Rational bound = atom[1].getConst<Rational>();
        if (!pol)
        {
          if (atom[0].getType().isInteger())
          {
            // ~( p >= c ) ---> ( p <= c-1 )
            bound = bound - Rational(1);
          }
        }
        unsigned bindex = pol ? 0 : 1;
        bool setBound = true;
        std::map<Node, Rational>::iterator itb = init_bounds[bindex].find(p);
        if (itb != init_bounds[bindex].end())
        {
          if (itb->second == bound)
          {
            setBound = atom_orig.getKind() == EQUAL;
          }
          else
          {
            setBound = pol ? itb->second < bound : itb->second > bound;
          }
          if (setBound)
          {
            // the bound is subsumed
            init_assertions.erase(init_bounds_lit[bindex][p]);
          }
        }
        if (setBound)
        {
          Trace("nl-ext-init") << (pol ? "Lower" : "Upper") << " bound for "
                               << p << " : " << bound << std::endl;
          init_bounds[bindex][p] = bound;
          init_bounds_lit[bindex][p] = lit;
        }
      }
    }
  }
  // for each bound that is the same, ensure we've inferred the equality
  for (std::pair<const Node, Rational>& ib : init_bounds[0])
  {
    Node p = ib.first;
    Node lit1 = init_bounds_lit[0][p];
    if (lit1.getKind() != EQUAL)
    {
      std::map<Node, Rational>::iterator itb = init_bounds[1].find(p);
      if (itb != init_bounds[1].end())
      {
        if (ib.second == itb->second)
        {
          Node eq = p.eqNode(nm->mkConst(ib.second));
          eq = Rewriter::rewrite(eq);
          Node lit2 = init_bounds_lit[1][p];
          Assert(lit2.getKind() != EQUAL);
          // use the equality instead, thus these are redundant
          init_assertions.erase(lit1);
          init_assertions.erase(lit2);
          init_assertions.insert(eq);
        }
      }
    }
  }

  for (const Node& a : init_assertions)
  {
    assertions.push_back(a);
  }
  Trace("nl-ext") << "...keep " << assertions.size() << " / " << nassertions
                  << " assertions." << std::endl;
}

std::vector<Node> ReluExtension::checkModelEval(
    const std::vector<Node>& assertions)
{
  std::vector<Node> false_asserts;
  for (size_t i = 0; i < assertions.size(); ++i) {
    Node lit = assertions[i];
    Node atom = lit.getKind()==NOT ? lit[0] : lit;
    Node litv = d_model.computeConcreteModelValue(lit);
    Trace("nl-ext-mv-assert") << "M[[ " << lit << " ]] -> " << litv;
    if (litv != d_true)
    {
      Trace("nl-ext-mv-assert") << " [model-false]" << std::endl;
      false_asserts.push_back(lit);
    }
    else
    {
      Trace("nl-ext-mv-assert") << std::endl;
    }
  }
  return false_asserts;
}

bool ReluExtension::checkModel(const std::vector<Node>& assertions,
                                    const std::vector<Node>& false_asserts,
                                    std::vector<Node>& lemmas,
                                    std::vector<Node>& gs)
{
  Trace("nl-ext-cm") << "--- check-model ---" << std::endl;

  // get the presubstitution
  Trace("nl-ext-cm-debug") << "  apply pre-substitution..." << std::endl;
  std::vector<Node> pvars;
  std::vector<Node> psubs;
  for (std::pair<const Node, Node>& tb : d_tr_base)
  {
    pvars.push_back(tb.first);
    psubs.push_back(tb.second);
  }
  // initialize representation of assertions
  std::vector<Node> passertions;
  for (const Node& a : assertions)
  {
    Node pa = a;
    if (!pvars.empty())
    {
      pa = arithSubstitute(pa, pvars, psubs);
      pa = Rewriter::rewrite(pa);
    }
    if (!pa.isConst() || !pa.getConst<bool>())
    {
      Trace("nl-ext-cm-assert") << "- assert : " << pa << std::endl;
      passertions.push_back(pa);
    }
  }

  // get model bounds for all transcendental functions
  Trace("nl-ext-cm-debug") << "  get bounds for transcendental functions..."
                           << std::endl;
  for (std::pair<const Kind, std::vector<Node> >& tfs : d_f_map)
  {
    Kind k = tfs.first;
    for (const Node& tf : tfs.second)
    {
      bool success = true;
      // tf is Figure 3 : tf( x )
      Node atf = d_model.computeConcreteModelValue(tf);
      Trace("nl-ext-cm-debug")
          << "Value for is " << tf << " is " << atf << std::endl;
      Node bl;
      Node bu;
      if (k == PI)
      {
        bl = d_pi_bound[0];
        bu = d_pi_bound[1];
      }
      else if (d_model.isRefineableTfFun(tf))
      {
        d_model.setUsedApproximate();
        std::pair<Node, Node> bounds = getTfModelBounds(tf, d_taylor_degree);
        bl = bounds.first;
        bu = bounds.second;
      }
      if (!bl.isNull() && !bu.isNull())
      {
        // We have rewritten an application of a transcendental function
        // based on the current model values.It could be that the model value
        // rewrites sin(x) ---> sin(-c) ---> -sin(c), thus we need
        // to negate the bounds in this case.
        if (atf.getKind() != tf.getKind())
        {
          if (atf.getKind() == MULT && atf.getNumChildren() == 2
              && atf[0] == d_neg_one)
          {
            atf = atf[1];
            Node btmp = bl;
            bl = ArithMSum::negate(bu);
            bu = ArithMSum::negate(btmp);
          }
        }
        success = d_model.addCheckModelBound(atf, bl, bu);
      }
      if (!success)
      {
        Trace("nl-ext-cm-debug")
            << "...failed to set bound for transcendental function."
            << std::endl;
        return false;
      }
    }
  }
  bool ret = d_model.checkModel(
      passertions, false_asserts, d_taylor_degree, lemmas, gs);
  return ret;
}


std::vector<Node> ReluExtension::checkSplitZero() {
  std::vector<Node> lemmas;
  for (unsigned i = 0; i < d_ms_vars.size(); i++) {
    Node v = d_ms_vars[i];
    if (d_zero_split.insert(v)) {
      Node eq = v.eqNode(d_zero);
      eq = Rewriter::rewrite(eq);
      Node literal = d_containing.getValuation().ensureLiteral(eq);
      d_containing.getOutputChannel().requirePhase(literal, true);
      lemmas.push_back(literal.orNode(literal.negate()));
    }
  }
  return lemmas;
}

/** An argument trie, for computing congruent terms */
class ArgTrie
{
 public:
  /** children of this node */
  std::map<Node, ArgTrie> d_children;
  /** the data of this node */
  Node d_data;
  /**
   * Set d as the data on the node whose path is [args], return either d if
   * that node has no data, or the data that already occurs there.
   */
  Node add(Node d, const std::vector<Node>& args)
  {
    ArgTrie* at = this;
    for (const Node& a : args)
    {
      at = &(at->d_children[a]);
    }
    if (at->d_data.isNull())
    {
      at->d_data = d;
    }
    return at->d_data;
  }
};

int ReluExtension::checkLastCall(const std::vector<Node>& assertions,
                                      const std::vector<Node>& false_asserts,
                                      const std::vector<Node>& xts,
                                      std::vector<Node>& lems,
                                      std::vector<Node>& lemsPp,
                                      std::vector<Node>& wlems,
                                      std::map<Node, NlLemmaSideEffect>& lemSE)
{
  d_ms_vars.clear();
  d_ms_proc.clear();
  d_ms.clear();
  d_mterms.clear();
  d_m_nconst_factor.clear();
  d_tplane_refine.clear();
  d_ci.clear();
  d_ci_exp.clear();
  d_ci_max.clear();
  d_f_map.clear();
  d_tf_region.clear();

  std::vector<Node> lemmas;
  NodeManager* nm = NodeManager::currentNM();

  Trace("nl-ext-mv") << "Extended terms : " << std::endl;
  // register the extended function terms
  std::map< Node, Node > mvarg_to_term;
  std::vector<Node> tr_no_base;
  bool needPi = false;
  // for computing congruence
  std::map<Kind, ArgTrie> argTrie;
  for (unsigned i = 0, xsize = xts.size(); i < xsize; i++)
  {
    Node a = xts[i];
    d_model.computeConcreteModelValue(a);
    d_model.computeAbstractModelValue(a);
    d_model.printModelValue("nl-ext-mv", a);
    Kind ak = a.getKind();
    if (ak == NONLINEAR_MULT)
    {
      d_ms.push_back( a );

      //context-independent registration
      registerMonomial(a);

      std::map<Node, std::vector<Node> >::iterator itvl = d_m_vlist.find(a);
      Assert(itvl != d_m_vlist.end());
      for (unsigned k = 0; k < itvl->second.size(); k++) {
        if (!IsInVector(d_ms_vars, itvl->second[k])) {
          d_ms_vars.push_back(itvl->second[k]);
        }
        Node mvk = d_model.computeAbstractModelValue(itvl->second[k]);
        if( !mvk.isConst() ){
          d_m_nconst_factor[a] = true;
        }
      }
      // mark processed if has a "one" factor (will look at reduced monomial)?
    }
    else if (a.getNumChildren() > 0)
    {
      if (ak == SINE)
      {
        needPi = true;
      }
      bool consider = true;
      // if is an unpurified application of SINE, or it is a transcendental
      // applied to a trancendental, purify.
      if (isTranscendentalKind(ak))
      {
        if (ak == SINE && d_tr_is_base.find(a) == d_tr_is_base.end())
        {
          consider = false;
        }
        else
        {
          for (const Node& ac : a)
          {
            if (isTranscendentalKind(ac.getKind()))
            {
              consider = false;
              break;
            }
          }
        }
        if (!consider)
        {
          tr_no_base.push_back(a);
        }
      }
      if( consider ){
        std::vector<Node> repList;
        for (const Node& ac : a)
        {
          Node r = d_model.computeConcreteModelValue(ac);
          repList.push_back(r);
        }
        Node aa = argTrie[ak].add(a, repList);
        if (aa != a)
        {
          // apply congruence to pairs of terms that are disequal and congruent
          Assert(aa.getNumChildren() == a.getNumChildren());
          Node mvaa = d_model.computeAbstractModelValue(a);
          Node mvaaa = d_model.computeAbstractModelValue(aa);
          if (mvaa != mvaaa)
          {
            std::vector<Node> exp;
            for (unsigned j = 0, size = a.getNumChildren(); j < size; j++)
            {
              exp.push_back(a[j].eqNode(aa[j]));
            }
            Node expn = exp.size() == 1 ? exp[0] : nm->mkNode(AND, exp);
            Node cong_lemma = nm->mkNode(OR, expn.negate(), a.eqNode(aa));
            lemmas.push_back( cong_lemma );
          }
        }
        else
        {
          d_f_map[ak].push_back(a);
        }
      }
    }
    else if (ak == PI)
    {
      needPi = true;
      d_f_map[ak].push_back(a);
    }
    else
    {
      Assert(false);
    }
  }
  // initialize pi if necessary
  if (needPi && d_pi.isNull())
  {
    mkPi();
    getCurrentPiBounds(lemmas);
  }

  filterLemmas(lemmas, lems);
  if (!lems.empty())
  {
    Trace("nl-ext") << "  ...finished with " << lems.size()
                    << " new lemmas during registration." << std::endl;
    return lems.size();
  }

  // process SINE phase shifting
  for (const Node& a : tr_no_base)
  {
    if (d_tr_base.find(a) == d_tr_base.end())
    {
      Node y =
          nm->mkSkolem("y", nm->realType(), "phase shifted trigonometric arg");
      Node new_a = nm->mkNode(a.getKind(), y);
      d_tr_is_base[new_a] = true;
      d_tr_base[a] = new_a;
      Node lem;
      if (a.getKind() == SINE)
      {
        Trace("nl-ext-tf") << "Basis sine : " << new_a << " for " << a
                           << std::endl;
        Assert(!d_pi.isNull());
        Node shift = nm->mkSkolem("s", nm->integerType(), "number of shifts");
        // FIXME : do not introduce shift here, instead needs model-based
        // refinement for constant shifts (#1284)
        lem = nm->mkNode(
            AND,
            mkValidPhase(y, d_pi),
            nm->mkNode(
                ITE,
                mkValidPhase(a[0], d_pi),
                a[0].eqNode(y),
                a[0].eqNode(nm->mkNode(
                    PLUS,
                    y,
                    nm->mkNode(MULT, nm->mkConst(Rational(2)), shift, d_pi)))),
            new_a.eqNode(a));
      }
      else
      {
        // do both equalities to ensure that new_a becomes a preregistered term
        lem = nm->mkNode(AND, a.eqNode(new_a), a[0].eqNode(y));
      }
      // must do preprocess on this one
      Trace("nl-ext-lemma")
          << "ReluExtension::Lemma : purify : " << lem << std::endl;
      lemsPp.push_back(lem);
    }
  }
  if (!lemsPp.empty())
  {
    Trace("nl-ext") << "  ...finished with " << lemsPp.size()
                    << " new lemmas SINE phase shifting." << std::endl;
    return lemsPp.size();
  }
  Trace("nl-ext") << "We have " << d_ms.size() << " monomials." << std::endl;

  // register constants
  registerMonomial(d_one);
  for (unsigned j = 0; j < d_order_points.size(); j++) {
    Node c = d_order_points[j];
    d_model.computeConcreteModelValue(c);
    d_model.computeAbstractModelValue(c);
  }

  // register variables
  Trace("nl-ext-mv") << "Variables in monomials : " << std::endl;
  for (unsigned i = 0; i < d_ms_vars.size(); i++) {
    Node v = d_ms_vars[i];
    registerMonomial(v);
    d_model.computeConcreteModelValue(v);
    d_model.computeAbstractModelValue(v);
    d_model.printModelValue("nl-ext-mv", v);
  }
  if (Trace.isOn("nl-ext-mv"))
  {
    Trace("nl-ext-mv") << "Arguments of trancendental functions : "
                       << std::endl;
    for (std::pair<const Kind, std::vector<Node> >& tfl : d_f_map)
    {
      Kind k = tfl.first;
      if (k == SINE || k == EXPONENTIAL)
      {
        for (const Node& tf : tfl.second)
        {
          Node v = tf[0];
          d_model.computeConcreteModelValue(v);
          d_model.computeAbstractModelValue(v);
          d_model.printModelValue("nl-ext-mv", v);
        }
      }
    }
  }
  // LEMMA time
  return 0;
}

void ReluExtension::check(Theory::Effort e) {
  Trace("nl-ext") << std::endl;
  Trace("nl-ext") << "ReluExtension::check, effort = " << e
                  << ", built model = " << d_builtModel.get() << std::endl;
  if (e == Theory::EFFORT_FULL)
  {
    d_containing.getExtTheory()->clearCache();
    d_needsLastCall = true;
    if (options::nlExtRewrites()) {
      std::vector<Node> nred;
      if (!d_containing.getExtTheory()->doInferences(0, nred)) {
        Trace("nl-ext") << "...sent no lemmas, # extf to reduce = "
                        << nred.size() << std::endl;
        if (nred.empty()) {
          d_needsLastCall = false;
        }
      } else {
        Trace("nl-ext") << "...sent lemmas." << std::endl;
      }
    }
  }
  else
  {
    // If we computed lemmas during collectModelInfo, send them now.
    if (!d_cmiLemmas.empty() || !d_cmiLemmasPp.empty())
    {
      sendLemmas(d_cmiLemmas, false, d_cmiLemmasSE);
      sendLemmas(d_cmiLemmasPp, true, d_cmiLemmasSE);
      return;
    }
    // Otherwise, we will answer SAT. The values that we approximated are
    // recorded as approximations here.
    TheoryModel* tm = d_containing.getValuation().getModel();
    for (std::pair<const Node, std::pair<Node, Node>>& a : d_approximations)
    {
      if (a.second.second.isNull())
      {
        tm->recordApproximation(a.first, a.second.first);
      }
      else
      {
        tm->recordApproximation(a.first, a.second.first, a.second.second);
      }
    }
  }
}

bool ReluExtension::modelBasedRefinement(
    std::vector<Node>& mlems,
    std::vector<Node>& mlemsPp,
    std::map<Node, NlLemmaSideEffect>& lemSE)
{
  // get the assertions
  std::vector<Node> assertions;
  getAssertions(assertions);

  Trace("nl-ext-mv-assert")
      << "Getting model values... check for [model-false]" << std::endl;
  // get the assertions that are false in the model
  const std::vector<Node> false_asserts = checkModelEval(assertions);

  // get the extended terms belonging to this theory
  std::vector<Node> xts;
  d_containing.getExtTheory()->getTerms(xts);

  if (Trace.isOn("nl-ext-debug"))
  {
    Trace("nl-ext-debug") << "  processing ReluExtension::check : "
                          << std::endl;
    Trace("nl-ext-debug") << "     " << false_asserts.size()
                          << " false assertions" << std::endl;
    Trace("nl-ext-debug") << "     " << xts.size()
                          << " extended terms: " << std::endl;
    Trace("nl-ext-debug") << "       ";
    for (unsigned j = 0; j < xts.size(); j++)
    {
      Trace("nl-ext-debug") << xts[j] << " ";
    }
    Trace("nl-ext-debug") << std::endl;
  }

  // compute whether shared terms have correct values
  unsigned num_shared_wrong_value = 0;
  std::vector<Node> shared_term_value_splits;
  // must ensure that shared terms are equal to their concrete value
  Trace("nl-ext-mv") << "Shared terms : " << std::endl;
  for (context::CDList<TNode>::const_iterator its =
           d_containing.shared_terms_begin();
       its != d_containing.shared_terms_end();
       ++its)
  {
    TNode shared_term = *its;
    // compute its value in the model, and its evaluation in the model
    Node stv0 = d_model.computeConcreteModelValue(shared_term);
    Node stv1 = d_model.computeAbstractModelValue(shared_term);
    d_model.printModelValue("nl-ext-mv", shared_term);
    if (stv0 != stv1)
    {
      num_shared_wrong_value++;
      Trace("nl-ext-mv") << "Bad shared term value : " << shared_term
                         << std::endl;
      if (shared_term != stv0)
      {
        // split on the value, this is non-terminating in general, TODO :
        // improve this
        Node eq = shared_term.eqNode(stv0);
        shared_term_value_splits.push_back(eq);
      }
      else
      {
        // this can happen for transcendental functions
        // the problem is that we cannot evaluate transcendental functions
        // (they don't have a rewriter that returns constants)
        // thus, the actual value in their model can be themselves, hence we
        // have no reference point to rule out the current model.  In this
        // case, we may set incomplete below.
      }
    }
  }
  Trace("nl-ext-debug") << "     " << num_shared_wrong_value
                        << " shared terms with wrong model value." << std::endl;
  bool needsRecheck;
  do
  {
    d_model.resetCheck();
    needsRecheck = false;
    // complete_status:
    //   1 : we may answer SAT, -1 : we may not answer SAT, 0 : unknown
    int complete_status = 1;
    // lemmas that should be sent later
    std::vector<Node> wlems;
    // We require a check either if an assertion is false or a shared term has
    // a wrong value
    if (!false_asserts.empty() || num_shared_wrong_value > 0)
    {
      complete_status = num_shared_wrong_value > 0 ? -1 : 0;
      checkLastCall(
          assertions, false_asserts, xts, mlems, mlemsPp, wlems, lemSE);
      if (!mlems.empty() || !mlemsPp.empty())
      {
        return true;
      }
    }
    Trace("nl-ext") << "Finished check with status : " << complete_status
                    << std::endl;

    // if we did not add a lemma during check and there is a chance for SAT
    if (complete_status == 0)
    {
      Trace("nl-ext")
          << "Check model based on bounds for irrational-valued functions..."
          << std::endl;
      // check the model based on simple solving of equalities and using
      // error bounds on the Taylor approximation of transcendental functions.
      std::vector<Node> lemmas;
      std::vector<Node> gs;
      if (checkModel(assertions, false_asserts, lemmas, gs))
      {
        complete_status = 1;
      }
      for (const Node& mg : gs)
      {
        Node mgr = Rewriter::rewrite(mg);
        mgr = d_containing.getValuation().ensureLiteral(mgr);
        d_containing.getOutputChannel().requirePhase(mgr, true);
        d_builtModel = true;
      }
      filterLemmas(lemmas, mlems);
      if (!mlems.empty())
      {
        return true;
      }
    }

    // if we have not concluded SAT
    if (complete_status != 1)
    {
      // flush the waiting lemmas
      if (!wlems.empty())
      {
        mlems.insert(mlems.end(), wlems.begin(), wlems.end());
        Trace("nl-ext") << "...added " << wlems.size() << " waiting lemmas."
                        << std::endl;
        return true;
      }
      // resort to splitting on shared terms with their model value
      // if we did not add any lemmas
      if (num_shared_wrong_value > 0)
      {
        complete_status = -1;
        if (!shared_term_value_splits.empty())
        {
          std::vector<Node> stvLemmas;
          for (const Node& eq : shared_term_value_splits)
          {
            Node req = Rewriter::rewrite(eq);
            Node literal = d_containing.getValuation().ensureLiteral(req);
            d_containing.getOutputChannel().requirePhase(literal, true);
            Trace("nl-ext-debug") << "Split on : " << literal << std::endl;
            Node split = literal.orNode(literal.negate());
            filterLemma(split, stvLemmas);
          }
          if (!stvLemmas.empty())
          {
            mlems.insert(mlems.end(), stvLemmas.begin(), stvLemmas.end());
            Trace("nl-ext") << "...added " << stvLemmas.size()
                            << " shared term value split lemmas." << std::endl;
            return true;
          }
        }
        else
        {
          // this can happen if we are trying to do theory combination with
          // trancendental functions
          // since their model value cannot even be computed exactly
        }
      }

      // we are incomplete
      if (options::nlExtIncPrecision() && d_model.usedApproximate())
      {
        d_taylor_degree++;
        needsRecheck = true;
        // increase precision for PI?
        // Difficult since Taylor series is very slow to converge
        Trace("nl-ext") << "...increment Taylor degree to " << d_taylor_degree
                        << std::endl;
      }
      else
      {
        Trace("nl-ext") << "...failed to send lemma in "
                           "NonLinearExtension, set incomplete"
                        << std::endl;
        d_containing.getOutputChannel().setIncomplete();
      }
    }
  } while (needsRecheck);

  // did not add lemmas
  return false;
}

void ReluExtension::interceptModel(std::map<Node, Node>& arithModel)
{
  if (!needsCheckLastEffort())
  {
    // no non-linear constraints, we are done
    return;
  }
  Trace("nl-ext") << "ReluExtension::interceptModel begin" << std::endl;
  d_model.reset(d_containing.getValuation().getModel(), arithModel);
  // run a last call effort check
  d_cmiLemmas.clear();
  d_cmiLemmasPp.clear();
  d_cmiLemmasSE.clear();
  if (!d_builtModel.get())
  {
    Trace("nl-ext") << "interceptModel: do model-based refinement" << std::endl;
    modelBasedRefinement(d_cmiLemmas, d_cmiLemmasPp, d_cmiLemmasSE);
  }
  if (d_builtModel.get())
  {
    Trace("nl-ext") << "interceptModel: do model repair" << std::endl;
    d_approximations.clear();
    // modify the model values
    d_model.getModelValueRepair(arithModel, d_approximations);
  }
}

void ReluExtension::presolve()
{
  Trace("nl-ext") << "ReluExtension::presolve" << std::endl;
}

void ReluExtension::assignOrderIds(std::vector<Node>& vars,
                                        NodeMultiset& order,
                                        bool isConcrete,
                                        bool isAbsolute)
{
  SortNlModel smv;
  smv.d_nlm = &d_model;
  smv.d_isConcrete = isConcrete;
  smv.d_isAbsolute = isAbsolute;
  smv.d_reverse_order = false;
  std::sort(vars.begin(), vars.end(), smv);

  order.clear();
  // assign ordering id's
  unsigned counter = 0;
  unsigned order_index = isConcrete ? 0 : 1;
  Node prev;
  for (unsigned j = 0; j < vars.size(); j++) {
    Node x = vars[j];
    Node v = d_model.computeModelValue(x, isConcrete);
    if( !v.isConst() ){
      Trace("nl-ext-mvo") << "..do not assign order to " << x << " : " << v << std::endl;
      //don't assign for non-constant values (transcendental function apps)
      break;
    }
    Trace("nl-ext-mvo") << "  order " << x << " : " << v << std::endl;
    if (v != prev) {
      // builtin points
      bool success;
      do {
        success = false;
        if (order_index < d_order_points.size()) {
          Node vv = d_model.computeModelValue(d_order_points[order_index],
                                              isConcrete);
          if (d_model.compareValue(v, vv, isAbsolute) <= 0)
          {
            counter++;
            Trace("nl-ext-mvo") << "O[" << d_order_points[order_index]
                                << "] = " << counter << std::endl;
            order[d_order_points[order_index]] = counter;
            prev = vv;
            order_index++;
            success = true;
          }
        }
      } while (success);
    }
    if (prev.isNull() || d_model.compareValue(v, prev, isAbsolute) != 0)
    {
      counter++;
    }
    Trace("nl-ext-mvo") << "O[" << x << "] = " << counter << std::endl;
    order[x] = counter;
    prev = v;
  }
  while (order_index < d_order_points.size()) {
    counter++;
    Trace("nl-ext-mvo") << "O[" << d_order_points[order_index]
                        << "] = " << counter << std::endl;
    order[d_order_points[order_index]] = counter;
    order_index++;
  }
}


// status 0 : n equal, -1 : n superset, 1 : n subset
void ReluExtension::MonomialIndex::addTerm(Node n,
                                                const std::vector<Node>& reps,
                                                ReluExtension* nla,
                                                int status, unsigned argIndex) {
  if (status == 0) {
    if (argIndex == reps.size()) {
      d_monos.push_back(n);
    } else {
      d_data[reps[argIndex]].addTerm(n, reps, nla, status, argIndex + 1);
    }
  }
  for (std::map<Node, MonomialIndex>::iterator it = d_data.begin();
       it != d_data.end(); ++it) {
    if (status != 0 || argIndex == reps.size() || it->first != reps[argIndex]) {
      // if we do not contain this variable, then if we were a superset,
      // fail (-2), otherwise we are subset.  if we do contain this
      // variable, then if we were equal, we are superset since variables
      // are ordered, otherwise we remain the same.
      int new_status =
          std::find(reps.begin(), reps.end(), it->first) == reps.end()
              ? (status >= 0 ? 1 : -2)
              : (status == 0 ? -1 : status);
      if (new_status != -2) {
        it->second.addTerm(n, reps, nla, new_status, argIndex);
      }
    }
  }
  // compare for subsets
  for (unsigned i = 0; i < d_monos.size(); i++) {
    Node m = d_monos[i];
    if (m != n) {
      // we are superset if we are equal and haven't traversed all variables
      int cstatus = status == 0 ? (argIndex == reps.size() ? 0 : -1) : status;
      Trace("nl-ext-mindex-debug") << "  compare " << n << " and " << m
                                   << ", status = " << cstatus << std::endl;
      if (cstatus <= 0 && nla->isMonomialSubset(m, n)) {
        nla->registerMonomialSubset(m, n);
        Trace("nl-ext-mindex-debug") << "...success" << std::endl;
      } else if (cstatus >= 0 && nla->isMonomialSubset(n, m)) {
        nla->registerMonomialSubset(n, m);
        Trace("nl-ext-mindex-debug") << "...success (rev)" << std::endl;
      }
    }
  }
}
}  // namespace arith
}  // namespace theory
}  // namespace CVC4
