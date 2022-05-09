#include "ff_heuristic.h"

#include "../option_parser.h"
#include "../plugin.h"

#include "../task_utils/task_properties.h"
#include "../utils/logging.h"

#include "../search_engines/eager_search.h"
#include "../evaluators/g_evaluator.h"
#include "../open_lists/best_first_open_list.h"

#include <cassert>

using namespace std;

namespace ff_heuristic {
// construction and destruction
FFHeuristic::FFHeuristic(const Options &opts)
    : AdditiveHeuristic(opts),
      relaxed_plan(task_proxy.get_operators().size(), false) {
    if (log.is_at_least_normal()) {
        log << "Initializing FF heuristic..." << endl;
    }
    use_learned_weights = opts.get<bool>("use_learned_weights");
    if (use_learned_weights) {
        assert(opts.get_list<string>("operator_names").size() == opts.get_list<string>("operator_weights").size());
        for (size_t i = 0; i < opts.get_list<std::string>("operator_names").size(); i++) {
            op_weights[opts.get_list<std::string>("operator_names")[i]] = opts.get_list<double>("operator_weights")[i];
        }
    }
}

void FFHeuristic::mark_preferred_operators_and_relaxed_plan(
    const State &state, PropID goal_id) {
    Proposition *goal = get_proposition(goal_id);
    if (!goal->marked) { // Only consider each subgoal once.
        goal->marked = true;
        OpID op_id = goal->reached_by;
        if (op_id != NO_OP) { // We have not yet chained back to a start node.
            UnaryOperator *unary_op = get_operator(op_id);
            bool is_preferred = true;
            for (PropID precond : get_preconditions(op_id)) {
                mark_preferred_operators_and_relaxed_plan(
                    state, precond);
                if (get_proposition(precond)->reached_by != NO_OP) {
                    is_preferred = false;
                }
            }
            int operator_no = unary_op->operator_no;
            if (operator_no != -1) {
                // This is not an axiom.
                relaxed_plan[operator_no] = true;
                if (is_preferred) {
                    OperatorProxy op = task_proxy.get_operators()[operator_no];
                    assert(task_properties::is_applicable(op, state));
                    set_preferred(op);
                }
            }
        }
    }
}



int FFHeuristic::compute_heuristic(const State &ancestor_state) {
    State state = convert_ancestor_state(ancestor_state);
    int h_add = compute_add_and_ff(state);
    if (h_add == DEAD_END)
        return h_add;

    // Collecting the relaxed plan also sets the preferred operators.
    for (PropID goal_id : goal_propositions)
        mark_preferred_operators_and_relaxed_plan(state, goal_id);

    int h_ff = 0;
    double adj_h_ff = 0.0;
    std::unordered_map<std::string, int> op_type_counts;

    for (size_t op_no = 0; op_no < relaxed_plan.size(); ++op_no) {
        if (relaxed_plan[op_no]) {
            relaxed_plan[op_no] = false; // Clean up for next computation.
            h_ff += task_proxy.get_operators()[op_no].get_cost();

            if (use_learned_weights) {
                string op_type = task_proxy.get_operators()[op_no].get_name().substr(0,task_proxy.get_operators()[op_no].get_name().find(" "));
                if (use_learned_weights) {
                    adj_h_ff += op_weights[op_type];
                }
            }
        }
    }

    if (use_learned_weights) {
        return ceil(adj_h_ff);
    } else {
        return h_ff;
    }
}


static shared_ptr<Heuristic> _parse(OptionParser &parser) {
    parser.document_synopsis("FF heuristic", "");
    parser.document_language_support("action costs", "supported");
    parser.document_language_support("conditional effects", "supported");
    parser.document_language_support(
        "axioms",
        "supported (in the sense that the planner won't complain -- "
        "handling of axioms might be very stupid "
        "and even render the heuristic unsafe)");
    parser.document_property("admissible", "no");
    parser.document_property("consistent", "no");
    parser.document_property("safe", "yes for tasks without axioms");
    parser.document_property("preferred operators", "yes");

    parser.add_option<bool>("use_learned_weights", "use learned weights", "false");
    parser.add_list_option<string>("operator_names", "operator names","[]" );
    parser.add_list_option<double>("operator_weights", "operator weights (same order as names)","[]");

    Heuristic::add_options_to_parser(parser);
    Options opts = parser.parse();    
    if (parser.dry_run())
        return nullptr;
    else
        return make_shared<FFHeuristic>(opts);
}

static Plugin<Evaluator> _plugin("ff", _parse);
}
