#include <storm/api/storm.h>
#include <storm-parsers/api/storm-parsers.h>
#include <storm-parsers/parser/PrismParser.h>
#include <storm/storage/prism/Program.h>
#include <storm/storage/jani/Property.h>
#include <storm/modelchecker/results/CheckResult.h>
#include <storm/modelchecker/results/ExplicitQuantitativeCheckResult.h>
#include <storm/utility/initialize.h>

#include <algorithm>
#include <iostream>
#include <fstream> // for read/write on files
#include <stdexcept>
#include <string> //
#include <sstream>// for std::ostringstream

typedef storm::models::sparse::Dtmc<double> Dtmc;
typedef storm::expressions::Variable Variable;



struct Module_node {
    std::string module_name;
    std::set<storm::expressions::Variable> def; //Names of the defined variables
    std::set<storm::expressions::Variable> ref; //Names of the referenced/declared variables
    std::set<std::string> act; //Names of the used actions inside module

    void reset_node(){
        this->module_name.clear();
        this->def.clear();
        this->ref.clear();
        this->act.clear();
    }
};

std::set<storm::expressions::Variable> extract_globals_def(storm::prism::Program program){
    std::set<storm::expressions::Variable> def={};
    //globals 
    for(auto boolvar : program.getGlobalBooleanVariables()){
        //get var of declarated variable
        def.insert(boolvar.getExpressionVariable());
    }

    for(auto intvar : program.getGlobalIntegerVariables()){
        //get var of declarated variable
        def.insert(intvar.getExpressionVariable());
    }


    //constants
    for(auto constant : program.getConstants()){
        def.insert(constant.getExpressionVariable());
    }

    //formulas 
    for(auto formula : program.getFormulas()){
        def.insert(formula.getExpressionVariable());
    }

    //init block 
    if(program.hasInitialConstruct()){
        program.getInitialConstruct().getInitialStatesExpression().gatherVariables(def);
    }
    return def;
}

std::set<storm::expressions::Variable> extract_globals_ref(storm::prism::Program program){
    std::set<storm::expressions::Variable> ref={};
    //globals 
    for(auto boolvar : program.getGlobalBooleanVariables()){
        //get var of declarated variable
        ref.insert(boolvar.getExpressionVariable());

        // get vars of used variables for declaration
        boolvar.getInitialValueExpression().gatherVariables(ref);
    }

    for(auto intvar : program.getGlobalIntegerVariables()){
        //get var of declarated variable
        ref.insert(intvar.getExpressionVariable());

        // get vars of used variables for range
        intvar.getRangeExpression().gatherVariables(ref);

        // get names of used variables for init value
        intvar.getInitialValueExpression().gatherVariables(ref);
    }


    //constants
    for(auto constant : program.getConstants()){
        ref.insert(constant.getExpressionVariable());
        constant.getExpression().gatherVariables(ref);
    }

    //formulas 
    for(auto formula : program.getFormulas()){
        ref.insert(formula.getExpressionVariable());
        formula.getExpression().gatherVariables(ref);
    }

    
    return ref;
    
}

std::set<storm::expressions::Variable> extract_def(storm::prism::Module module){
    std::set<storm::expressions::Variable> def={};
    for(auto boolvar : module.getBooleanVariables()){
        //get var of declarated variable
        def.insert(boolvar.getExpressionVariable());
    }

    for(auto intvar : module.getIntegerVariables()){
        //get var of declarated variable
        def.insert(intvar.getExpressionVariable());
    }

    // now for Coms
    for(auto com : module.getCommands()){
        //now for updates
        for(auto u : com.getUpdates()){
            //now for assignments
            for(auto a : u.getAssignments()){
                def.insert(a.getVariable());
            }
        }
    }
    return def;
}


std::set<storm::expressions::Variable> extract_ref(storm::prism::Module module){
    std::set<storm::expressions::Variable> ref={};
    for(auto boolvar : module.getBooleanVariables()){
        //get var of declarated variable
        ref.insert(boolvar.getExpressionVariable());

        // get vars of used variables for declaration
        if(boolvar.hasInitialValue()){
            boolvar.getInitialValueExpression().gatherVariables(ref);
        }

    }

    for(auto intvar : module.getIntegerVariables()){
        //get var of declarated variable
        ref.insert(intvar.getExpressionVariable());

        // get vars of used variables for range
        intvar.getRangeExpression().gatherVariables(ref);

        // get names of used variables for init value
        if(intvar.hasInitialValue()){
            intvar.getInitialValueExpression().gatherVariables(ref);
        }

    }

    // now for Coms
    for(auto com : module.getCommands()){
        //first for guards
        com.getGuardExpression().gatherVariables(ref);

        //now for updates
        for(auto u : com.getUpdates()){
            //first for rate
            u.getLikelihoodExpression().gatherVariables(ref);

            //now for assignments
            for(auto a : u.getAssignments()){
                a.getExpression().gatherVariables(ref);
            }
        }
    }
    return ref;
}


std::set<std::string> extract_actions(storm::prism::Module module){
    std::set<std::string> act={};
    for(auto com : module.getCommands()){
        std::string action=com.getActionName();
        if(action.length() != 0) {act.insert(com.getActionName());}
    }
    return act;
}

std::vector<Module_node> get_module_nodes(storm::prism::Program p){
    std::vector<Module_node> program_module_nodes={};
    Module_node ins;
    std::vector<storm::prism::Module> Mods = p.getModules();
    for(storm::prism::Module m : Mods) {
        ins.module_name=m.getName();
        // !!REF!!
        ins.ref=extract_ref(m);

        // !!DEF!!
        ins.def=extract_def(m);


        // !!ACTIONS!!
        ins.act=extract_actions(m);

        program_module_nodes.push_back(ins);
    }

    //add vglob 
    ins.module_name= "global";
    ins.ref= extract_globals_ref(p);
    ins.def= extract_globals_def(p);
    ins.act.clear();
    program_module_nodes.push_back(ins);
    
    return program_module_nodes;
}

// MDG ADJ List
std::vector<std::vector<int>> create_adj_list(std::vector<Module_node> mod_nodes){
    std::vector<std::vector<int>> adj_list;
    adj_list.reserve(mod_nodes.size());
    std::vector<int> adj_vector={};
    adj_vector.reserve(mod_nodes.size());

    for(int i = 0; i < mod_nodes.size(); i++){
        adj_vector.clear();
        for(int j = 0; j < mod_nodes.size(); j++){
            if(i==j){
                continue;
                }

            bool transition = false;


            //cdep act(mod_nodes[i]) setintersection act(mod_nodes[j]) != emptyset
                for(std::string acti : mod_nodes[i].act){
                    for(std::string actj : mod_nodes[j].act){
                        if(acti == actj){
                            adj_vector.push_back(j);
                            transition = true;
                            break;
                        }
                    }
                    if(transition) {break;}
                }

            //ddep ref(mod_nodes[i]) setintersection def(mod_nodes[j]) != emptyset
            if(!transition){
                for(Variable vari : mod_nodes[i].ref){
                    for(Variable varj : mod_nodes[j].def){
                        if(vari.getName() == varj.getName()){
                            adj_vector.push_back(j);
                            transition = true;
                            break;
                        }
                    }
                    if(transition) {break;}
                }
            }

            

            
        }
        adj_list.push_back(adj_vector);
    }

    return adj_list;
}

std::vector<Module_node> slice_mdg( std::vector<std::vector<int>> adj_list, 
                                    std::vector<Module_node> module_nodes, 
                                    std::vector<std::string> crits){
//return subseteq of module_nodes containing only the module_nodes relevant for module with name crit
    std::vector<Module_node> slice={};
    int nr_modules = module_nodes.size();

    std::vector<int> starting_indices={};
    for(std::string crit : crits){
        bool found;
        for(int index = 0; index < module_nodes.size();index++){
            if(module_nodes.at(index).module_name == crit){
                starting_indices.push_back(index);
                break;
            }
        }
    }

    bool *visited = new bool[nr_modules];
    for(int i = 0; i < nr_modules; i++){
        visited[i] = false;
    }
    std::list<int> queue;
 
    for(int s : starting_indices){
        visited[s] = true;
        //push all criteria
        queue.push_back(s);
    }
    // 'i' will be used to get all adjacent
    // vertices of a vertex
    std::vector<int>::iterator i;

    
    while(!queue.empty())
    {
        int s;
        s = queue.front();
        queue.pop_front();
 
        for (i = adj_list[s].begin(); i != adj_list[s].end(); ++i)
        {
            if (!visited[*i])
            {
                visited[*i] = true;
                queue.push_back(*i);
            }
        }
    }


    for(int j=0; j < nr_modules; j++){
        if(visited[j]){
            slice.push_back(module_nodes[j]);
        }
    }

    return slice;
}

std::vector<bool> slice_mdg_benchmark(std::vector<std::vector<int>> adj_list, 
                                        std::vector<Module_node> vertices, 
                                        std::string crit){
//return subseteq of module_nodes containing only the module_nodes relevant for module with name crit
    int nr_modules = vertices.size();

    int starting_index = 0;
    for(; starting_index < nr_modules; starting_index++){
        if(vertices.at(starting_index).module_name == crit){
            break;
        }
    }

    std::vector<bool> visited = {};
    for(int i = 0; i < nr_modules; i++){
        visited.push_back(false);
    }

    std::list<int> queue;
 
    visited.at(starting_index) = true;
    queue.push_back(starting_index);

    // 'i' will be used to get all adjacent
    // vertices of a vertex
    std::vector<int>::iterator i;

    
    while(!queue.empty())
    {
        int s;
        s = queue.front();
        queue.pop_front();
 
        for (i = adj_list[s].begin(); i != adj_list[s].end(); ++i)
        {
            if (!visited.at(*i))
            {
                visited.at(*i) = true;
                queue.push_back(*i);
            }
        }
    }

    return visited;
}

void mdg_benchmark(std::vector<Module_node> vertices,
                   std::vector<std::vector<int>> adj_list,
                   storm::prism::Program program){

    std::cout << "\n\nStarting MODULE Benchmark\n\n";

    int nr_nodes = vertices.size();
    int nr_edges = 0;
    for(std::vector<int> adj_vector : adj_list){
        nr_edges += adj_vector.size();
    }
    int nr_slices = 0;

    //vector of slice sizes to calculate avg slice size
    int slice_sizes;

    std::map<int, std::vector<std::vector<bool>>> size_by_slices;
    std::map<int, int> size_by_crits;


    for(int index = 0; index < vertices.size(); index++ ){
        std::string crit;
        crit = vertices.at(index).module_name;
        std::vector<bool> visited = slice_mdg_benchmark(adj_list, vertices, crit);
        int slice_size = std::count(visited.begin(), visited.end(), true);
        std::map<int, std::vector<std::vector<bool>>>::iterator map_it = size_by_slices.find(slice_size);
        if(map_it != size_by_slices.end()){
            size_by_crits[map_it->first] += 1;
            bool found = false;
            std::vector<std::vector<bool>> visits_with_same_size = size_by_slices[map_it->first];
            for(std::vector<bool> visits : visits_with_same_size){
                bool equal=true;
                for(int comp = 0; comp < visits.size(); comp++){
                    if(visits.at(comp) != visited.at(comp)){
                        equal = false;
                        break;
                    }
                }
                if(equal){
                    found=true;
                    break;
                }
            }
            if(!found){
                size_by_slices[map_it->first].push_back(visited);
            }
        } else {
            std::vector<std::vector<bool>> new_visits;
            new_visits.push_back(visited);
            size_by_slices.insert(std::make_pair(slice_size, new_visits));
            std::cout<< "new length " << slice_size << " for slice of module: " << vertices.at(index).module_name << std::endl;

            size_by_crits.insert(std::make_pair(slice_size, 1));
        }
    }

    int amount_unique_slices = 0;
    int avg_slice_size = 0;
    float size_by_unique_sum = 0;
    float size_by_crits_sum = 0;
    std::cout<< std::endl;
    for(std::pair<int, std::vector<std::vector<bool>>> x : size_by_slices) {
        size_by_unique_sum += x.first * x.second.size();
        size_by_crits_sum += x.first * size_by_crits[x.first];
        amount_unique_slices += x.second.size();
        avg_slice_size += (x.first * x.second.size());
        std::cout << "got " << x.second.size() << " unique slices with length: " << x.first;
        std::cout << " produced by " << size_by_crits[x.first] << "/" << vertices.size() << " = " <<static_cast<float>(size_by_crits[x.first])/static_cast<float>(vertices.size()) << " percent of all components" << std::endl;
    }
    

    std::cout << "Results: \n";
    std::cout << "      modules: " << nr_nodes << std::endl;
    std::cout << "      edges: " << nr_edges << std::endl;
    std::cout << "      slices: " << amount_unique_slices << std::endl;
    std::cout << "      avg_size_uw = " << size_by_unique_sum << "/" << static_cast<float>(amount_unique_slices)<< " = " <<  
        size_by_unique_sum / static_cast<float>(amount_unique_slices) << std::endl;
    std::cout << "      avg_size_w = " << size_by_crits_sum  << "/" <<  static_cast<float>(vertices.size()) << " = " <<
        size_by_crits_sum / static_cast<float>(vertices.size()) << std::endl;


    
    // print and test 
    // res.print();

}
                   

struct BetterNode {
    uint_fast64_t identifier;
    std::string type;
    std::string module_name;
    std::set<storm::expressions::Variable> def; //Names of the defined variables
    std::set<storm::expressions::Variable> ref; //Names of the referenced/declared variables
    std::string code_segment;
    void clear(){
        identifier=-1;
        type.clear();
        module_name.clear();
        def.clear();
        ref.clear();
        code_segment.clear();
    }
};

std::vector<BetterNode> build_vertices_for_program(storm::prism::Program program){
    std::vector<BetterNode> verts={};
    BetterNode ins_node;
    std::ostringstream code;

    for(auto boolvar : program.getGlobalBooleanVariables()){
        // Decl Node creation
        ins_node.clear();
        ins_node.identifier=boolvar.getExpressionVariable().getIndex(); //global identifier negative 1
        ins_node.type="decl gb"; //decl global boolean
        ins_node.module_name="global";
        boolvar.getExpression().gatherVariables(ins_node.ref);
        ins_node.ref.insert(boolvar.getExpressionVariable());
        ins_node.def.insert(boolvar.getExpressionVariable());

        code << "global " << boolvar.getExpressionVariable().getName() << " : bool";
        if(boolvar.hasInitialValue()){
            code << " init " << boolvar.getInitialValueExpression().toString();
            boolvar.getInitialValueExpression().gatherVariables(ins_node.ref);
        }
        ins_node.code_segment=  code.str();
        code.str("");;

        verts.push_back(ins_node);

    }

    for(auto intvar : program.getGlobalIntegerVariables()){
        // Decl Node creation
        ins_node.clear();
        ins_node.identifier=intvar.getExpressionVariable().getIndex(); //global identifier negative 1
        ins_node.type="decl gi"; //decl global int
        ins_node.module_name="global";
        intvar.getExpression().gatherVariables(ins_node.ref);
        ins_node.ref.insert(intvar.getExpressionVariable());
        ins_node.def.insert(intvar.getExpressionVariable());

        code << "global " << intvar.getExpressionVariable().getName() << " : ";
        storm::expressions::Expression rangeexpr = intvar.getRangeExpression();
        if(rangeexpr.isTrue()){
            code << "int";
        } else {
            code << "[" << intvar.getLowerBoundExpression() << ".." << intvar.getUpperBoundExpression() << "]";
        }
        if(intvar.hasInitialValue()){
            code << " init " << intvar.getInitialValueExpression().toString();
            intvar.getInitialValueExpression().gatherVariables(ins_node.ref);

        }
        ins_node.code_segment= code.str();
        code.str("");;
        verts.push_back(ins_node);
    }

    for(auto constant :program.getConstants()){
        // Decl Node creation
        ins_node.clear();
        ins_node.identifier=constant.getExpressionVariable().getIndex(); //global identifier negative 1
        ins_node.type="decl c"; //decl global constant
        ins_node.module_name="global";
        constant.getExpression().gatherVariables(ins_node.ref);
        ins_node.ref.insert(constant.getExpressionVariable());
        ins_node.def.insert(constant.getExpressionVariable());

        code << "const ";
        if(constant.getType().isRationalType()){
            code << "double"; // storm doesnt know double, it just knows 'rational' which is illegal type in prism
        } else {
            code << constant.getType().getStringRepresentation();
        }
        code << " " << constant.getExpressionVariable().getName() << " = "; 
        code << constant.getExpression().toString();
        ins_node.code_segment= code.str();
        code.str("");;
        verts.push_back(ins_node);
    }

    for(auto form : program.getFormulas()){
        // Decl Node creation
        ins_node.clear();
        ins_node.identifier=form.getExpressionVariable().getIndex(); //global identifier negative 1
        ins_node.type="decl f"; //decl global formula
        ins_node.module_name="global";
        form.getExpression().gatherVariables(ins_node.ref);
        ins_node.ref.insert(form.getExpressionVariable());
        ins_node.def.insert(form.getExpressionVariable());

        code << "formula " << form.getExpressionVariable().getName() << " = "; 
        code << form.getExpression().toString();
        ins_node.code_segment= code.str();
        code.str("");
        verts.push_back(ins_node);
    }


    for(auto module : program.getModules()){
        for(storm::prism::BooleanVariable boolvar : module.getBooleanVariables()){
            // Decl Node creation
            ins_node.clear();
            ins_node.identifier=boolvar.getExpressionVariable().getIndex(); //global identifier negative 1
            ins_node.type="decl"; //decl global boolean
            ins_node.module_name=module.getName();
            boolvar.getExpression().gatherVariables(ins_node.ref);
            ins_node.ref.insert(boolvar.getExpressionVariable());
            ins_node.def.insert(boolvar.getExpressionVariable());

            code << boolvar.getExpressionVariable().getName() << " : bool";
            if(boolvar.hasInitialValue()){
                code << " init " << boolvar.getInitialValueExpression().toString();
                boolvar.getInitialValueExpression().gatherVariables(ins_node.ref);
            }
            ins_node.code_segment=  code.str();
            code.str("");

            verts.push_back(ins_node);
            }

        for(storm::prism::IntegerVariable intvar : module.getIntegerVariables()){

            storm::expressions::Expression rangeexpr = intvar.getRangeExpression();

            // Decl Node creation
            ins_node.clear();
            ins_node.identifier=intvar.getExpressionVariable().getIndex(); //global identifier negative 1
            ins_node.type="decl"; //decl global boolean
            ins_node.module_name=module.getName();
            intvar.getExpression().gatherVariables(ins_node.ref);
            if(!rangeexpr.isTrue()){
                intvar.getLowerBoundExpression().gatherVariables(ins_node.ref);
                intvar.getUpperBoundExpression().gatherVariables(ins_node.ref);
            }

            ins_node.ref.insert(intvar.getExpressionVariable());
            ins_node.def.insert(intvar.getExpressionVariable());

            code << intvar.getExpressionVariable().getName() << " : ";
            if(rangeexpr.isTrue()){
                code << "int";
            } else {
                code << "[" << intvar.getLowerBoundExpression() << ".." << intvar.getUpperBoundExpression() << "]";
            }
            if(intvar.hasInitialValue()){
                code << " init " << intvar.getInitialValueExpression().toString();
                intvar.getInitialValueExpression().gatherVariables(ins_node.ref);

            }
            ins_node.code_segment= code.str();
            code.str("");
            verts.push_back(ins_node);
        }

        for(storm::prism::Command c : module.getCommands()){

            // create Guard Node 
            ins_node.clear();
            ins_node.identifier=c.getGlobalIndex(); //global identifier negative 1
            ins_node.type="guard"; //decl global boolean
            ins_node.module_name=module.getName();
            c.getGuardExpression().gatherVariables(ins_node.ref);
            // def = emptyset
            ins_node.code_segment=c.getGuardExpression().toString();

            verts.push_back(ins_node);

            for(storm::prism::Update u : c.getUpdates()){
                // create rate Node 
                ins_node.clear();
                ins_node.identifier=u.getGlobalIndex(); 
                ins_node.type="rate"; //decl global boolean
                ins_node.module_name=module.getName();
                u.getLikelihoodExpression().gatherVariables(ins_node.ref);
                // def = emptyset
                ins_node.code_segment=u.getLikelihoodExpression().toString();

                verts.push_back(ins_node);

                if(u.getAssignments().size() == 0){ // empty assignment -> assignment = 'true'
                    // create rate Node 
                    ins_node.clear();
                    ins_node.identifier=u.getGlobalIndex(); //global identifier negative 1
                    ins_node.type="assignment"; //decl global boolean
                    ins_node.module_name=module.getName();
                    // ref = emptyset
                    // def = emptyset
                    ins_node.code_segment="true";

                    verts.push_back(ins_node);

                } else {

                    for(storm::prism::Assignment ass : u.getAssignments()){
                        // create rate Node 
                        ins_node.clear();
                        ins_node.identifier=u.getGlobalIndex(); //global identifier negative 1
                        ins_node.type="assignment"; //decl global boolean
                        ins_node.module_name=module.getName();
                        ass.getExpression().gatherVariables(ins_node.ref);
                        ins_node.def.insert(ass.getVariable());
                        code.str("");
                        code << "(" << ass.getVariable().getExpression().toString() << "'=" << ass.getExpression().toString() << ")";
                        ins_node.code_segment=code.str();
                        code.str("");

                        verts.push_back(ins_node);
                    }
                }
                
                

            }

        }
        


    }
    if(program.hasInitialConstruct()){
            ins_node.clear();
            ins_node.identifier = -1;
            ins_node.type = "init";
            ins_node.module_name = "global";
            program.getInitialStatesExpression().gatherVariables(ins_node.ref);
            code.str("");
            code << "init " << program.getInitialStatesExpression().toString() << " endinit";
            ins_node.code_segment = code.str();
            verts.push_back(ins_node);
            code.str("");

        }

    //print and test 
    // for(BetterNode node : verts){
    //     std::cout << node.code_segment << ": ";
    //     std::cout << "{type:" << node.type << ", ID:" << node.identifier << ", Mod: " << node.module_name << ", ref:{";
    //     for(auto var : node.ref){
    //         std::cout << var.getName() << ", ";
    //     }
    //     std::cout << "}, def:{";
    //     for(auto var : node.def){
    //         std::cout << var.getName() << ", ";
    //     }
    //     std::cout << "}}" << std::endl;
    // }
    // std::cout<< "Amount of vertices = " << verts.size() << std::endl;

    return verts;
}

std::string get_action_of_guard_node(storm::prism::Program program, BetterNode guard){
    std::string action;
    std::unordered_map< uint_fast64_t, std::string> cid_to_action = program.buildCommandIndexToActionNameMap();
    action = cid_to_action[guard.identifier];
    return action;
}

std::vector<BetterNode> get_all_guard_nodes(std::vector<BetterNode> inputnodes){
    std::vector<BetterNode> guards;
    for(BetterNode node : inputnodes){
        if(node.type == "guard"){
            guards.push_back(node);
        }
    }
    return guards;
}

std::vector<BetterNode> get_assignment_nodes_for_guard(storm::prism::Program program, std::vector<BetterNode> vertices, BetterNode guard){
    if(!(guard.type=="guard")){
        throw std::invalid_argument( "given node is not of type guard" );
    }
    std::vector<BetterNode> assignments;
    storm::prism::Module mod = program.getModule(guard.module_name);
    storm::prism::Command com;
    for(auto command : mod.getCommands()){
        if(command.getGlobalIndex() == guard.identifier){ com = command;}
    }
    for(storm::prism::Update u : com.getUpdates()){
        for(auto node : vertices){
            if((node.identifier == u.getGlobalIndex()) && (node.type=="assignment")){
                assignments.push_back(node);
            }
        }
    }
    //print and check 
    // std::cout<< "guard " << guard.code_segment << " is related to assingments:";
    // for(auto assg : assignments){
    //     std::cout << assg.type << " " << assg.code_segment;
    // }
    // std::cout << " | " << std::endl;
    return assignments;
}

std::unordered_map<uint_fast64_t, uint_fast64_t> build_assgID_to_comID_map(std::vector<BetterNode> vertices, storm::prism::Program program){
    
    std::unordered_map<uint_fast64_t, uint_fast64_t> assgID_to_comID_map;

    std::vector<BetterNode> guards = get_all_guard_nodes(vertices);

    for(BetterNode guard : guards){
        storm::prism::Module mod = program.getModule(guard.module_name);                                                                                                            //but node ID is global command index 
        storm::prism::Command com;
        for(auto command : mod.getCommands()){
            if(command.getGlobalIndex() == guard.identifier){ com = command;}
        }

        for(storm::prism::Update u : com.getUpdates()){
            uint_fast64_t glob_index = u.getGlobalIndex();
            for(int i = 0; i < vertices.size(); i++){
                if((vertices.at(i).identifier == glob_index) && (vertices.at(i).type=="assignment")){
                    assgID_to_comID_map[vertices.at(i).identifier] = guard.identifier;
                }
            }
        }
    }
    return assgID_to_comID_map;
}


bool depgg(BetterNode v1, BetterNode v2, std::unordered_map< uint_fast64_t, std::string> cid_to_action){
    if(v1.type=="guard" && v2.type=="guard"){
        if(v1.module_name != v2.module_name){
            if(cid_to_action[v1.identifier].size() > 0){
                if(cid_to_action[v1.identifier] == cid_to_action[v2.identifier]){
                    return true;
                }
            }
        }

    }
    return false;
}

bool depag(BetterNode v1, BetterNode v2, std::unordered_map<uint_fast64_t, uint_fast64_t> aID_to_cID){
    if(v1.type == "assignment" || v1.type == "rate"){
        if(v2.type == "guard"){
            if(aID_to_cID[v1.identifier] == v2.identifier){
                return true;
            }
        }
    }
    return false;
}

bool depar(BetterNode v1, BetterNode v2){
    if(v1.identifier == v2.identifier){
        if(v1.type == "assignment"){
            if(v2.type == "rate"){
                return true;
            }
        }
    }
    return false;
    // return ((v1_assg && v2_rate) || (v1_rate && v2_assg)) && related;
}


bool depdi(BetterNode v1, BetterNode v2){
    if(v1.type.find("decl") != std::string::npos){//type contains 'decl'?
        if(v2.type == "init"){
            bool v1_adressed_in_v2 = false;
            for(storm::expressions::Variable decl_var : v1.def){
                for(storm::expressions::Variable init_var : v2.ref){
                    if(decl_var.getName() == init_var.getName()){
                        return true;
                    }
                }
            }
        }
    } 
    return false;
}

std::vector<std::vector<int>> build_comp_adj_list(std::vector<BetterNode> vertices, storm::prism::Program program){
    std::vector<std::vector<int>> comp_adj_list;
    comp_adj_list.reserve(vertices.size());

    std::unordered_map< uint_fast64_t, std::string> cid_to_action = program.buildCommandIndexToActionNameMap();
    std::unordered_map<uint_fast64_t, uint_fast64_t> aID_to_cID = build_assgID_to_comID_map(vertices, program);

    for(int i = 0; i < vertices.size(); i++){
        std::vector<int> adj_vector={};
        for(int j = 0; j < vertices.size(); j++){
            if(i==j) {continue;}
            // cdep 
            //      depar 
            if ( depar(vertices.at(i), vertices.at(j)) ){
                adj_vector.push_back(j);

                continue;
            }

            //      depgg
            if( depgg(vertices.at(i), vertices.at(j), cid_to_action) ){
                adj_vector.push_back(j);

                continue;
            }
            //      depag
            if( depag(vertices.at(i), vertices.at(j), aID_to_cID)){
                adj_vector.push_back(j);

                continue;
            }
            

            // ddep
            bool transition = false;

            //ddep ref(vertices[i]) setintersection def(vertices[j]) != emptyset
            for(Variable vari : vertices.at(i).ref){
                for(Variable varj : vertices.at(j).def){
                    if(vari.getName() == varj.getName()){
                        adj_vector.push_back(j);
                        // std::cout << "added ddep trans for: " << vertices.at(i).code_segment;
                        // std::cout << " and " << vertices.at(j).code_segment <<std::endl;
                        transition = true;
                        break;
                    }
                }
                if(transition) {break;}
            }
        }
        comp_adj_list.push_back(adj_vector);
        // std::cout<< "built adjacency vector for comp " << vertices.at(i).code_segment << std::endl;
    }
    return comp_adj_list;

}

void check_slice_for_useless_commands(std::vector<BetterNode> &vertices, storm::prism::Program program){ //checks if something can be sliced away after slicing
    for(storm::prism::Module module : program.getModules()){
            bool module_relevant = false;
            //check if this module is in vertices:
            for(auto node : vertices){
                if(node.module_name == module.getName()){
                    module_relevant=true;
                    break;
                }
            }
            if(!module_relevant) { continue;}

        for(storm::prism::Command c : module.getCommands()){
                // is command in slice and guard true?
                bool relevant_guard_is_true = false; //relevant if guard is inside nodes
                std::vector<BetterNode>::iterator nodeptr;
                for(nodeptr = vertices.begin(); nodeptr < vertices.end(); nodeptr++){
                    if( (nodeptr->type == "guard") && c.getGuardExpression().isTrue() && (nodeptr->identifier == c.getGlobalIndex()) ){
                        relevant_guard_is_true = true;
                        break;
                    }
                }
                if(!relevant_guard_is_true) {continue;}

                //if no updates and guard.getExpression.isTrue
                int update_counter=0;
                for(storm::prism::Update u : c.getUpdates()){
                    for(auto ratenode : vertices){
                        if( (ratenode.identifier==u.getGlobalIndex()) && (ratenode.type=="rate") ){
                            update_counter+=1;
                        }
                    }
                }

                if(update_counter==0){
                    vertices.erase(nodeptr);
                    continue;
                }
        }
    }
}

std::vector<BetterNode> slice_cdg_by_comp(  std::vector<BetterNode> vertices, 
                                            std::vector<std::vector<int>> adj_list, 
                                            std::vector<std::string> crits,
                                            storm::prism::Program program){
    std::vector<BetterNode> slice={};
    //find module with given name
    int nr_verts = vertices.size();
    // make s array for multiple starting points
    
    std::vector<int> starting_indices={};
    for(std::string crit : crits){
        int index = 0;
        for(; index < vertices.size();index++){
            if(vertices.at(index).code_segment == crit){
                starting_indices.push_back(index);
                break;
            }
        }
        if(index == vertices.size()){
            std::ostringstream error;
            error << "component " << crit << " not found";
            throw std::invalid_argument( error.str() );
        }
    }

    bool *visited = new bool[nr_verts];
    for(int i = 0; i < nr_verts; i++){
        visited[i] = false;
    }
    std::list<int> queue;
 
    for(int s : starting_indices){
        visited[s] = true;
        //push all criteria
        queue.push_back(s);
    }
    std::vector<int>::iterator i;
    int s;
    while(!queue.empty())
    {
        s = queue.front();
        queue.pop_front();
 
        for (i = adj_list[s].begin(); i != adj_list[s].end(); ++i)
        {
            if (!visited[*i])
            {
                visited[*i] = true;
                queue.push_back(*i);
            }
        }
    }


    for(int j=0; j < nr_verts; j++){
        if(visited[j]){
            slice.push_back(vertices.at(j));
        }
    }

    check_slice_for_useless_commands(slice,program);

    return slice;
}

std::vector<bool> slice_cdg_benchmark(  std::vector<BetterNode> vertices, 
                                            std::vector<std::vector<int>> adj_list, 
                                            std::vector<std::string> crits,
                                            storm::prism::Program program){
    std::vector<BetterNode> slice={};
    //find module with given name
    int nr_verts = vertices.size();
    // make s array for multiple starting points
    
    std::vector<int> starting_indices={};
    for(std::string crit : crits){
        int index = 0;
        for(; index < vertices.size();index++){
            if(vertices.at(index).code_segment == crit){
                starting_indices.push_back(index);
                break;
            }
        }
        if(index == vertices.size()){
            std::ostringstream error;
            error << "component " << crit << " not found";
            throw std::invalid_argument( error.str() );
        }
    }

    std::vector<bool> visited = {};
    for(int i = 0; i < nr_verts; i++){
        visited.push_back(false);
    }
    std::list<int> queue;
 
    for(int s : starting_indices){
        visited[s] = true;
        //push all criteria
        queue.push_back(s);
    }
    std::vector<int>::iterator i;
    int s;
    while(!queue.empty())
    {
        s = queue.front();
        queue.pop_front();
 
        for (i = adj_list[s].begin(); i != adj_list[s].end(); ++i)
        {
            if (!visited[*i])
            {
                visited[*i] = true;
                queue.push_back(*i);
            }
        }
    }

    for(int j=0; j < nr_verts; j++){
        if(visited[j]){
            slice.push_back(vertices.at(j));
        }
    }

    check_slice_for_useless_commands(slice,program);


    return visited;
}


void write_prism_from_vertices(std::vector<BetterNode> vertices, storm::prism::Program program, std::string path= "slice.prism"){
    std::ofstream prismfile;
    prismfile.open(path);
    if(prismfile.is_open()){
        //for globals
        switch (program.getModelType())
        {
            case storm::prism::Program::ModelType::DTMC:
                prismfile << "dtmc\n\n"; 
                break;
            case storm::prism::Program::ModelType::MDP:
                prismfile << "mdp\n\n"; 
                break;
            case storm::prism::Program::ModelType::CTMC:
                prismfile << "ctmc\n\n"; 
                break;
            case storm::prism::Program::ModelType::CTMDP :
                prismfile << "ctmdp\n\n"; 
                break;
            case storm::prism::Program::ModelType::MA :
                prismfile << "ma\n\n"; 
                break;
            case storm::prism::Program::ModelType::POMDP :
                prismfile << "pomdp\n\n"; 
                break;
            case storm::prism::Program::ModelType::PTA :
                prismfile << "pta\n\n"; 
                break;
            case storm::prism::Program::ModelType::SMG  :
                prismfile << "smg\n\n"; 
                break;
            default:
                prismfile << "mdp\n\n";
        }

        for(auto boolvar : program.getGlobalBooleanVariables()){
            for(BetterNode node : vertices){
                bool found = false;
                if(node.type=="decl gb"){
                    for(auto v : node.def){
                        if(v.getName() == boolvar.getName()){
                            prismfile << node.code_segment << ";\n";
                            found = true;
                            break;
                        }
                    }
                }
                if(found) { break;}
            }
        }
        for(auto intvar : program.getGlobalIntegerVariables()){
            for(BetterNode node : vertices){
                bool found = false;
                if(node.type=="decl gi"){
                    for(auto v : node.def){
                        if(v.getName() == intvar.getName()){
                            prismfile << node.code_segment << ";\n";
                            found = true;
                            break;
                        }
                    }
                }
                if(found) { break;}
            }
        }
        for(auto constant : program.getConstants()){
            for(BetterNode node : vertices){
                bool found = false;
                if(node.type=="decl c"){
                    for(auto v : node.def){
                        if(v.getName() == constant.getName()){
                            prismfile << node.code_segment << ";\n";
                            found = true;
                            break;
                        }
                    }
                }
                if(found) { break;}
            }
        }
        for(auto formula : program.getFormulas()){
            for(BetterNode node : vertices){
                bool found = false;
                if(node.type=="decl f"){
                    for(auto v : node.def){
                        if(v.getName() == formula.getName()){
                            prismfile << node.code_segment << ";\n";
                            found = true;
                            break;
                        }
                    }
                }
                if(found) { break;}
            }
        }
        prismfile << "\n";
        for(storm::prism::Module module : program.getModules()){
            bool module_relevant = false;
            //check if this module is in vertices:
            for(auto node : vertices){
                if(node.module_name == module.getName()){
                    module_relevant=true;
                    break;
                }
            }
            if(!module_relevant) { continue;}
            prismfile << "module " << module.getName() << "\n";

            for(storm::prism::BooleanVariable boolvar : module.getBooleanVariables()){
                for(BetterNode node : vertices){
                bool found = false;
                if( (node.type=="decl") && (node.module_name== module.getName()) ){
                    for(auto v : node.def){
                        if(v.getName() == boolvar.getName()){
                            prismfile << "  " << node.code_segment << ";\n";
                            found = true;
                            break;
                        }
                    }
                }
                if(found) { break;}
            }
            }

            for(storm::prism::IntegerVariable intvar : module.getIntegerVariables()){
                for(BetterNode node : vertices){
                    bool found = false;
                    if( (node.type=="decl") && (node.module_name== module.getName()) ){
                        for(auto v : node.def){
                            if(v.getName() == intvar.getName()){
                                prismfile << "  " << node.code_segment << ";\n";
                                found = true;
                                break;
                            }
                        }
                    }
                    if(found) { break;}
                }
            }

            for(storm::prism::Command c : module.getCommands()){
                // is command relevant?
                bool command_relevant = false; //relevant if guard is inside nodes
                for(auto node : vertices){
                    if( (node.type == "guard") && (node.identifier == c.getGlobalIndex()) ){
                        prismfile << "  [" << get_action_of_guard_node(program, node) << "] " << node.code_segment << " -> ";
                        command_relevant = true;
                        break;
                    }
                }
                if(!command_relevant) {continue;}

                //are the this commands updates empty in slice? -> updatecounter==0
                //we need the amount of updates to know if update is followed by '+' or by ';'
                int update_counter=0;
                for(storm::prism::Update u : c.getUpdates()){
                    for(auto ratenode : vertices){
                        if( (ratenode.identifier==u.getGlobalIndex()) && (ratenode.type=="rate") ){
                            update_counter+=1;
                        }
                    }
                }

                if(update_counter==0){
                    prismfile << "true;\n";
                    continue;
                }

                // if we are here, then there are some updates of c contained in the slice 
                // now we need to take all updates of the original command 
                update_counter = c.getNumberOfUpdates();
                
                // and check if an update is in the slice
                    //if update in slice: write down rate and the assignments contained in the slice
                    //if update not in slice: write down rate and assignment "true"

                for(storm::prism::Update u : c.getUpdates()){
                    bool update_in_slice = false;
                    for(auto ratenode : vertices){
                        if( (ratenode.identifier==u.getGlobalIndex()) && (ratenode.type=="rate") ){
                            update_counter -=1;
                            update_in_slice = true;
                            prismfile << ratenode.code_segment << ":";
                            int assgs_left = 0; // we need to know the amount of assignments coming to know which one is the last (is not followed by '&')
                            for(auto assgnode : vertices){
                                if( (assgnode.identifier==u.getGlobalIndex()) && (assgnode.type=="assignment") ){
                                    assgs_left += 1;
                                }
                            }
                            for(auto assgnode : vertices){
                                if( (assgnode.identifier==u.getGlobalIndex()) && (assgnode.type=="assignment") ){
                                    if(assgs_left > 1){
                                        prismfile << assgnode.code_segment << "&";
                                        assgs_left -=1;
                                    } else if(assgs_left == 1) {
                                        prismfile << assgnode.code_segment;
                                    }
                                }
                            }
                            
                        }
                    }
                    if(!update_in_slice){
                        prismfile << u.getLikelihoodExpression().toString() <<": true";
                        update_counter -=1;
                    }
                    // add plus or ;?
                    if(update_counter == 0){
                        prismfile << ";\n"; //end of command
                    } else {
                        prismfile << " + ";
                    }

                }

            }
            prismfile << "endmodule\n\n";

            
        }
        if(program.hasInitialConstruct()){
            for (unsigned k = vertices.size(); k-- != 0; ) { 
                if(vertices.at(k).type == "init"){
                    prismfile << vertices.at(k).code_segment << "\n";
                }
            }
        }
        
        prismfile.close();

    } else {
        std::cout << "Unable to open file" <<std::endl;
        return;
    }
    

}

struct Result {
    int nodes;
    int edges;
    int slices;
    float avg_size_w;
    float avg_size_uw;

    void print(){
        std::cout << "Results:\n";
        std::cout << "      nodes: " << nodes << "\n";
        std::cout << "      edges: " << edges << "\n";
        std::cout << "      slices: " << slices << "\n";
        std::cout << "      avg_size unweighted: " << avg_size_uw << "\n";
        std::cout << "      avg_size weighted: " << avg_size_w << "\n";

    }
};

Result benchmark(std::vector<BetterNode> vertices,
                 std::vector<std::vector<int>> adj_list,
                  storm::prism::Program program){
    Result res;
    std::cout << "\n\nStarting COMPONENTS Benchmark\n\n";
    res.nodes = vertices.size();
    res.edges = 0;

    for(std::vector<int> adj_vector : adj_list){
        res.edges += adj_vector.size();
    }
    res.slices = 0;

    //vector of slice sizes to calculate avg slice size
    int slice_sizes;


    std::map<int, std::vector<std::vector<bool>>> size_by_slices;
    std::map<int, int> size_by_crits;


    for(int index = 0; index < vertices.size(); index++ ){
        std::vector<std::string> crit;
        crit.push_back(vertices.at(index).code_segment);
        std::vector<bool> visited = slice_cdg_benchmark(vertices, adj_list, crit, program);
        int slice_size = std::count(visited.begin(), visited.end(), true);
        std::map<int, std::vector<std::vector<bool>>>::iterator map_it = size_by_slices.find(slice_size);
        if(map_it != size_by_slices.end()){
            size_by_crits[map_it->first] += 1;
            bool found = false;
            std::vector<std::vector<bool>> visits_with_same_size = size_by_slices[map_it->first];
            for(std::vector<bool> visits : visits_with_same_size){
                bool equal=true;
                for(int comp = 0; comp < visits.size(); comp++){
                    if(visits.at(comp) != visited.at(comp)){
                        equal = false;
                        break;
                    }
                }
                if(equal){
                    found=true;
                    break;
                }
            }
            if(!found){
                size_by_slices[map_it->first].push_back(visited);
            }
        } else {
            std::vector<std::vector<bool>> new_visits;
            new_visits.push_back(visited);
            size_by_slices.insert(std::make_pair(slice_size, new_visits));
            std::cout<< "new length " << slice_size << " for slice of component: " << vertices.at(index).code_segment << std::endl;
            size_by_crits.insert(std::make_pair(slice_size, 1));
        }
    }

    int amount_unique_slices = 0;
    int avg_slice_size = 0;
    float size_by_unique_sum = 0;
    float size_by_crits_sum = 0;
    std::cout << std::endl;
    for(std::pair<int, std::vector<std::vector<bool>>> x : size_by_slices) {
        size_by_unique_sum += x.first * x.second.size();
        size_by_crits_sum += x.first * size_by_crits[x.first];
        amount_unique_slices += x.second.size();
        avg_slice_size += (x.first * x.second.size());
        std::cout << "got " << x.second.size() << " unique slices with length: " << x.first;
        std::cout << " produced by " << size_by_crits[x.first] << "/" << vertices.size() << " = " <<static_cast<float>(size_by_crits[x.first])/static_cast<float>(vertices.size()) << " percent of all components" << std::endl;

 
    }


    res.slices = amount_unique_slices;
    if(amount_unique_slices != 0){
        res.avg_size_uw = (size_by_unique_sum/static_cast<float>(amount_unique_slices));
        res.avg_size_w = size_by_crits_sum / static_cast<float>(vertices.size());
    }

    
    // print and test 
    res.print();

    return res;
}

int main (int argc, char *argv[]) {

    // Init loggers
    storm::utility::setUp();
    // Set some settings objects.
    storm::settings::initializeAll("prisl", "prisl");

    // Call function
    if(argc == 3 && std::string(argv[2]) == "b" ){

    // unsync the I/O of C and C++.
    std::ios_base::sync_with_stdio(false);
 
    // Calculating total time taken by the program.


        //CDG BENCHMARK

        auto start = std::chrono::high_resolution_clock::now();
        storm::prism::Program program = storm::parser::PrismParser::parse(argv[1]);
        std::vector<BetterNode> vertices = build_vertices_for_program(program);
        std::vector<std::vector<int>> adj_list = build_comp_adj_list(vertices, program);\
        double time_taken_building = std::chrono::duration_cast<std::chrono::nanoseconds>(std::chrono::high_resolution_clock::now() - start).count();
        double building_in_seconds = time_taken_building * 1e-9;
        time_taken_building *= 1e-6;
        start = std::chrono::high_resolution_clock::now();
        benchmark(vertices, adj_list, program);
        auto end = std::chrono::high_resolution_clock::now();
        double time_taken = std::chrono::duration_cast<std::chrono::nanoseconds>(end - start).count();
        double slicing_in_seconds = time_taken * 1e-9;
        time_taken *= 1e-3;
        std::cout << "building cdg took: " << building_in_seconds << std::setprecision(9) << "seconds \n";
        std::cout << "slicing took avg time of " 
            << std::fixed << slicing_in_seconds/static_cast<float>(vertices.size()) << std::setprecision(9) << " seconds\n";


        //MDG BENCHMARK
    
        start = std::chrono::high_resolution_clock::now();
        program = storm::parser::PrismParser::parse(argv[1]);
        std::vector<Module_node> module_vertices = get_module_nodes(program);
        std::vector<std::vector<int>> mdg_adj_list = create_adj_list(module_vertices);
        time_taken_building = std::chrono::duration_cast<std::chrono::nanoseconds>(std::chrono::high_resolution_clock::now() - start).count();
        time_taken_building *=1e-9;

        start = std::chrono::high_resolution_clock::now();
        mdg_benchmark(module_vertices, mdg_adj_list, program);
        end = std::chrono::high_resolution_clock::now();
        time_taken = std::chrono::duration_cast<std::chrono::nanoseconds>(end - start).count();;
        time_taken *= 1e-9;
        std::cout << "building mdg took: " << time_taken_building << "seconds \n";
        std::cout << "slicing took avg time of " 
            << std::fixed << time_taken/static_cast<float>(module_vertices.size()) << std::setprecision(9) << " seconds per slice \n";
    }
    else if(argc == 3 && std::string(argv[2]) == "parse"){
        storm::prism::Program program = storm::parser::PrismParser::parse(argv[1], true);
        std::vector<BetterNode> vertices = build_vertices_for_program(program);
        write_prism_from_vertices(vertices, program);
    }
    else if(argc > 3){
        storm::prism::Program program = storm::parser::PrismParser::parse(argv[1], true);

        std::vector<BetterNode> vertices = build_vertices_for_program(program);

        // crit must be the code snippet of some vertex\in vertices OR Variable OR Module
        std::string mode = std::string(argv[2]);
        if(mode=="v" || mode=="variable" || mode=="var"){

            std::vector<std::string> crits={};

            bool legal_crit = true;

            for(int i = 3; i < argc; i++){
                bool found = false;
                for(int index = 0; index < vertices.size(); index++){
                    //if node.type contains string decl
                    if(vertices.at(index).type.find("decl") != std::string::npos){ 
                        for(storm::expressions::Variable var : vertices.at(index).def){
                            if(var.getName() == argv[i]){
                                crits.push_back(vertices.at(index).code_segment);
                                found = true;
                                break;
                            }
                        }
                    }
                    if(found) {break;}
                }
                legal_crit = legal_crit && found;
            }

            if(legal_crit){
                std::vector<std::vector<int>> adj_list = build_comp_adj_list(vertices, program);
                std::vector<BetterNode> sliced_cdg = slice_cdg_by_comp(vertices, adj_list, crits, program);
                write_prism_from_vertices(sliced_cdg, program);
            } else {
                throw std::invalid_argument( "given variable criterion is not in given program" );
            }

        } else if(mode =="c" || mode=="component") {

            std::vector<std::string> crits;

            bool legal_crit = true;
            for(int i = 3; i < argc; i++){
                bool found = false;
                for(int index = 0;index < vertices.size(); index++){
                    if(vertices.at(index).code_segment == argv[i]){
                        crits.push_back(argv[i]);
                        found = true;
                    }
                }
                legal_crit = legal_crit && found;
            }

            if(legal_crit){
                std::vector<std::vector<int>> adj_list = build_comp_adj_list(vertices, program);
                std::vector<BetterNode> sliced_cdg = slice_cdg_by_comp(vertices, adj_list, crits, program);
                write_prism_from_vertices(sliced_cdg, program);
            } else {
                throw std::invalid_argument( "There was atleast 1 component we couldnt find" );
            }
        } else if(mode=="m" || mode=="module"){
            std::vector<std::string> crits = {};
            bool legal_crit = true;

            std::vector<Module_node> module_vertices = get_module_nodes(program);
            for(int i = 3; i < argc; i++){
                bool found = false;
                for(Module_node mod : module_vertices){
                    if(mod.module_name == argv[i]){
                        crits.push_back(argv[i]);
                        found = true;
                        break;
                    }
                }
                legal_crit = legal_crit && found;
            }
            
            if(legal_crit){
                std::vector<std::vector<int>> adj_list = create_adj_list(module_vertices);
                std::vector<Module_node> slice = slice_mdg(adj_list, module_vertices, crits);
                std::vector<BetterNode> cdg_slice={};

                for(Module_node module : slice){
                    for(BetterNode comp : vertices){
                        if(module.module_name == comp.module_name){
                            cdg_slice.push_back(comp);
                        }
                    }
                }
                write_prism_from_vertices(cdg_slice, program);
            } else {
                throw std::invalid_argument( "given modulename is not in given program" );
            }
        } else {
            std::cout << "expected either v|c|m; but got: " << argv[2] <<std::endl;
            throw std::invalid_argument( "Wrong combination of argumentcount and arguments" );
        }


    } else {
        throw std::invalid_argument( "wrong amount of arguments" );
    }
}
