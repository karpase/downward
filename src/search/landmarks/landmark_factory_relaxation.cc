#include "landmark_factory_relaxation.h"

#include "exploration.h"
#include "landmark.h"

#include "../task_utils/task_properties.h"

using namespace std;

namespace landmarks {
LandmarkFactoryRelaxation::LandmarkFactoryRelaxation(const options::Options &opts)
    : LandmarkFactory(opts) {
}

void LandmarkFactoryRelaxation::generate_landmarks(const shared_ptr<AbstractTask> &task) {
    TaskProxy task_proxy(*task);
    Exploration exploration(task_proxy, log);
    generate_relaxed_landmarks(task, exploration);
    postprocess(task_proxy, exploration);
}

void LandmarkFactoryRelaxation::postprocess(
    const TaskProxy &task_proxy, Exploration &exploration) {
    lm_graph->set_landmark_ids();
    calc_achievers(task_proxy, exploration);
    mk_acyclic_graph();
}

void LandmarkFactoryRelaxation::discard_noncausal_landmarks(
    const TaskProxy &task_proxy, Exploration &exploration) {
    // TODO: Check if the code works correctly in the presence of axioms.
    task_properties::verify_no_conditional_effects(task_proxy);
    int num_all_landmarks = lm_graph->get_num_landmarks();
    lm_graph->remove_node_if(
        [this, &task_proxy, &exploration](const LandmarkNode &node) {
            return !is_causal_landmark(task_proxy, exploration, node.get_landmark());
        });
    int num_causal_landmarks = lm_graph->get_num_landmarks();
    if (log.is_at_least_normal()) {
        log << "Discarded " << num_all_landmarks - num_causal_landmarks
            << " non-causal landmarks" << endl;
    }
}

bool LandmarkFactoryRelaxation::is_causal_landmark(
    const TaskProxy &task_proxy, Exploration &exploration,
    const Landmark &landmark) const {
    /* Test whether the relaxed planning task is unsolvable without using any operator
       that has "landmark" as a precondition.
       Similar to "relaxed_task_solvable" above.
     */

    assert(!landmark.conjunctive);

    if (landmark.is_true_in_goal)
        return true;
    vector<vector<int>> lvl_var;
    vector<utils::HashMap<FactPair, int>> lvl_op;
    // Initialize lvl_var to numeric_limits<int>::max()
    VariablesProxy variables = task_proxy.get_variables();
    lvl_var.resize(variables.size());
    for (VariableProxy var : variables) {
        lvl_var[var.get_id()].resize(var.get_domain_size(),
                                     numeric_limits<int>::max());
    }
    unordered_set<int> exclude_op_ids;
    vector<FactPair> exclude_props;
    for (OperatorProxy op : task_proxy.get_operators()) {
        if (is_landmark_precondition(op, landmark)) {
            exclude_op_ids.insert(op.get_id());
        }
    }
    // Do relaxed exploration
    exploration.compute_reachability_with_excludes(
        lvl_var, exclude_props, exclude_op_ids);

    // Test whether all goal propositions have a level of less than numeric_limits<int>::max()
    for (FactProxy goal : task_proxy.get_goals())
        if (lvl_var[goal.get_variable().get_id()][goal.get_value()] ==
            numeric_limits<int>::max())
            return true;

    return false;
}

void LandmarkFactoryRelaxation::calc_achievers(
    const TaskProxy &task_proxy, Exploration &exploration) {
    assert(!achievers_calculated);
    VariablesProxy variables = task_proxy.get_variables();
    for (auto &lm_node : lm_graph->get_nodes()) {
        Landmark &landmark = lm_node->get_landmark();
        for (const FactPair &lm_fact : landmark.facts) {
            const vector<int> &ops = get_operators_including_eff(lm_fact);
            landmark.possible_achievers.insert(ops.begin(), ops.end());

            if (variables[lm_fact.var].is_derived())
                landmark.is_derived = true;
        }

        vector<vector<int>> lvl_var;
        relaxed_task_solvable(task_proxy, exploration, lvl_var, landmark);

        for (int op_or_axom_id : landmark.possible_achievers) {
            OperatorProxy op = get_operator_or_axiom(task_proxy, op_or_axom_id);

            if (possibly_reaches_lm(op, lvl_var, landmark)) {
                landmark.first_achievers.insert(op_or_axom_id);
            }
        }
    }
    achievers_calculated = true;
}

bool LandmarkFactoryRelaxation::relaxed_task_solvable(
    const TaskProxy &task_proxy, Exploration &exploration,
    const Landmark &exclude) const {
    vector<vector<int>> lvl_var;
    return relaxed_task_solvable(task_proxy, exploration, lvl_var, exclude);
}

bool LandmarkFactoryRelaxation::relaxed_task_solvable(
    const TaskProxy &task_proxy, Exploration &exploration,
    vector<vector<int>> &lvl_var, const Landmark &exclude) const {
    /*
      Test whether the relaxed planning task is solvable without achieving the
      propositions in "exclude" (do not apply operators that would add a
      proposition from "exclude"). As a side effect, collect in lvl_var the
      earliest possible point in time when a proposition can be achieved in the
      relaxed task.
    */

    OperatorsProxy operators = task_proxy.get_operators();
    VariablesProxy variables = task_proxy.get_variables();
    lvl_var.resize(variables.size());
    for (VariableProxy var : variables) {
        lvl_var[var.get_id()].resize(var.get_domain_size(),
                                     numeric_limits<int>::max());
    }
    // Extract propositions from "exclude"
    unordered_set<int> exclude_op_ids;
    vector<FactPair> exclude_props;
    for (OperatorProxy op : operators) {
        if (achieves_non_conditional(op, exclude))
            exclude_op_ids.insert(op.get_id());
    }
    exclude_props.insert(exclude_props.end(),
                         exclude.facts.begin(), exclude.facts.end());

    // Do relaxed exploration
    exploration.compute_reachability_with_excludes(
        lvl_var, exclude_props, exclude_op_ids);

    // Test whether all goal propositions have a level of less than numeric_limits<int>::max()
    for (FactProxy goal : task_proxy.get_goals())
        if (lvl_var[goal.get_variable().get_id()][goal.get_value()] ==
            numeric_limits<int>::max())
            return false;

    return true;
}

bool LandmarkFactoryRelaxation::achieves_non_conditional(
    const OperatorProxy &o, const Landmark &landmark) const {
    /* Test whether the landmark is achieved by the operator unconditionally.
    A disjunctive landmark is achieved if one of its disjuncts is achieved. */
    for (EffectProxy effect: o.get_effects()) {
        for (const FactPair &lm_fact : landmark.facts) {
            FactProxy effect_fact = effect.get_fact();
            if (effect_fact.get_pair() == lm_fact) {
                if (effect.get_conditions().empty())
                    return true;
            }
        }
    }
    return false;
}
}
