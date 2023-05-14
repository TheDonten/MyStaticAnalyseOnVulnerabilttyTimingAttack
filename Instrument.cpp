// Check_two.cpp : Этот файл содержит функцию "main". Здесь начинается и заканчивается выполнение программы.
//

#include <iostream>
#include <string>
#include <set>
#include <vector>
#include <unordered_set>
#include <unordered_map>
#include <stack>
#include <algorithm>
#include <deque>
#include <numeric>
#include <algorithm>
#include <iterator>
#include <regex>
#include<fstream>

#include <llvm/Support/MemoryBuffer.h>
#include <llvm/Support/ErrorOr.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/LLVMContext.h>
#include <llvm/Bitcode/BitcodeReader.h>
#include <llvm/Bitcode/BitcodeWriter.h>
#include <llvm/Support/raw_ostream.h>
#include "llvm/Support/SourceMgr.h"
#include <llvm/IRReader/IRReader.h>
#include <llvm/IR/Constants.h>
#include <llvm/IR/DebugInfo.h>
#include <llvm/IR/IntrinsicInst.h>
#include <llvm/Pass.h>
#include <llvm/IR/InstIterator.h> //To use the instructions iterator
#include <llvm/Analysis/MemoryLocation.h>
#include <llvm/Analysis/AliasAnalysis.h>
#include <llvm/Transforms/Utils/BasicBlockUtils.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/DataLayout.h>
#include <llvm/IR/Type.h>
#include <llvm/Analysis/DDG.h>
#include "llvm/Analysis/CallGraph.h"
#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/DenseSet.h"
#include "llvm/ADT/PostOrderIterator.h"
#include "llvm/ADT/STLExtras.h"
#include "llvm/IR/CFG.h"
#include "llvm/IR/Function.h"
#include <llvm/IR/InstIterator.h>
#include <llvm/IR/AbstractCallSite.h>
#include "llvm/ADT/Statistic.h"
#include "llvm/Support/raw_ostream.h"


using namespace llvm;


static std::set<std::string> Abstract_all_object, Temp_values, AllocValues;
static std::set<std::string> Func_name = { "mgm_128_ctx_create_init","main","mgm_128_encrypt","mgm_128_generate_next_mac_block","multiplication_gf_128",
"mgm_128_prepare","mgm_128_deploy_key","mgm_128_encrypt_block","func_F","func_X","func_LS"};
static std::set<std::string> Out;

static std::string out_txt = "";

class Node_inst {

    std::string type_instruction;
    std::string Object_name;
    std::set<std::pair<int, std::string>> edge_indexs;
    std::vector<std::string> pointValue_to_object;
    std::string Type;
    int index_v;
    bool element_array;
    std::string element_indes;
    bool have_secret;
    //bool have_index_non_consnant;
    //int max_size;
    Value* val;
public:
    
    Node_inst() {

    }

    Node_inst(std::string type_inst, std::string object_name, std::pair<int, std::string> edge_indexs, int index_v, Value* val,std::string type, bool secret) {
        this->type_instruction = type_inst;
        this->Object_name = object_name;
        if(edge_indexs != std::pair<int,std::string>{})
            this->edge_indexs.insert(edge_indexs);
        this->index_v = index_v;
        this->val = val;
        this->Type = type;
        this->have_secret = secret;
    }
    bool have_index_non_consnant = false;
    bool secret_index = false;
    bool malloc = false;
    bool bitcast = false;
    bool math_struct = false;
    std::set<std::string> Parent;
    std::vector < std::string> Dependecy;
    std::string Graph = "";
    void set_element_array(bool fl, std::string num) {
        this->element_array = fl;
        this->element_indes = num;
    }

    void add_edges_set(Node_inst* obj, std::vector<Node_inst*>* nodes) { //переопределяет множество
        if (obj->get_edges()->size() == 0) {
            this->edge_indexs.clear();
            this->edge_indexs.insert({obj->get_index(),""});
            if (obj->is_secret())
                this->have_secret = true;
            return;
        }
        const std::set<std::pair<int, std::string>> *prom = obj->get_edges();
        this->edge_indexs.clear();
        for (auto i = prom->begin(); i != prom->end(); i++) {
            if (obj->get_object_name() == nodes->at(i->first)->get_object_name())
                continue;
            //std::cout << i->first << "  " << i->second << std::endl;
            if (nodes->at(i->first)->is_secret())
                this->have_secret = true;
            
              
            this->edge_indexs.insert(*i);
        }
    }

    void add_edges(Node_inst* obj, std::string str, std::vector<Node_inst*> * nodes) {//добавляет элементы в множество
        //std::cout << obj->get_object_name() << std::endl;
        const std::set<std::pair<int, std::string>>* prom = obj->get_edges();
        for (auto i = prom->begin(); i != prom->end(); i++) {
            //std::cout << i->first << "  " << i->second << std::endl;
            if (obj->get_object_name() == nodes->at(i->first)->get_object_name())
                continue;
            if (obj->is_secret())
                nodes->at(i->first)->set_secret(true);
            if (nodes->at(i->first)->is_secret()) {
                this->secret_index = true;
                /*if (this->Type == "Object" || this->Type == "ObjectStruct" || this->Type == "ObjectArray")
                    this->have_secret = true;*/
            }
            if (str != "")
                this->edge_indexs.insert({ i->first,str });
            else
                this->edge_indexs.insert(*i);
        }
    }

    std::pair<int,std::string> find_edge(std::string str) {
        auto it = find_if(this->edge_indexs.begin(), this->edge_indexs.end(),
            [&](const std::pair<int, std::string>& val) -> bool {
                return val.second == str;
            });
        if (it == this->edge_indexs.end())
            return { -1, "meh" };
        return *it;
    }

    void set_secret(bool secret) {
        this->have_secret = secret;
    }

    void set_edge (std::pair<int,std::string> temp) { //добавляет элементы множества
        this->edge_indexs.insert(temp);
    } 
    /*void add_edges_set(Node_inst* obj) {
        this->edge_indexs = *obj->get_edges();
    }*/
 

    void print_all_edges() {
        std::cout << '--------------------------------------' << std::endl;
        for (auto i = edge_indexs.begin(); i != edge_indexs.end(); i++) {
            
            std::cout << i->first << "  " << i->second << std::endl;
            
        }
        std::cout << '--------------------------------------' << std::endl;
    }

    void rewrite_edges_set(Node_inst* obj) {

    }

    const bool is_secret() {
        return this->have_secret;
    }

    const std::string get_object_name() {
        return this->Object_name;
    }

    const int get_index() {
        return this->index_v;
    }

    const std::string get_type_instruction() {
        return this->type_instruction;
    }

    const Value* get_value() {
        return this->val;
    }

    std::set<std::pair<int, std::string>>* get_edges() { //ubral const
        return &this->edge_indexs;
    }

    const std::string get_type() {
        return this->Type;
    }
    const std::string get_element_indx() {
        return this->element_indes;
    }
    const bool is_element_array() {
        return this->element_array;
    }

};

static std::set<Node_inst*> Secret_variable;
static std::set<Node_inst*> Find_leaking;

class Graph {

    std::vector<std::vector<int>> matrix_graph;

public:

    void add_v() {
        if (matrix_graph.size() == 0) {
            this->matrix_graph.resize(1);
            this->matrix_graph[0].push_back(0);
            return;
        }
        std::vector<int> prom_vec;
        for (int i = 0; i < matrix_graph.size(); i++) {

            matrix_graph[i].push_back(0);
            prom_vec.push_back(0);

        }
        prom_vec.push_back(0);
        matrix_graph.push_back(prom_vec);
        return;
    }

    void add_reb(int a, int b) {
        this->matrix_graph[a][b] = 1;
    }

    void print() {
        for (int i = 0; i < matrix_graph.size(); i++) {
            for (int j = 0; j < matrix_graph[i].size(); j++) {
                std::cout << matrix_graph[i][j] << " ";
            }
            std::cout << std::endl;
        }
    }

};

std::pair<bool, StructType*> isStructType(Type* type) {
    if (PointerType* pointerType = dyn_cast<PointerType>(type)) {
        return isStructType(pointerType->getPointerElementType());
    }
    else if (type->isStructTy()) {
        StructType* check = cast<StructType>(type);
        return { true, check };
    }
    return { false, nullptr };
}

std::pair<bool, PointerType*> isPointerType(Type* type) {
    if (PointerType* pointerType = dyn_cast<PointerType>(type)) {
        return isPointerType(pointerType->getPointerElementType());
    }
    else if (type->isPointerTy()) {
        PointerType* check = cast<PointerType>(type);
        return { true, check };
    }
    return { false, nullptr };
}

std::pair<bool, ArrayType*> isArrayType(Type* type) {
    if (PointerType* pointerType = dyn_cast<PointerType>(type)) {
        return isArrayType(pointerType->getPointerElementType());
    }
    else if (type->isArrayTy()) {
        ArrayType* check = cast<ArrayType>(type);
        return { true, check };
    }
    return { false, nullptr };
}


void interface_with_data(std::vector<Node_inst*> nodes) {
    std::string str;
    while (std::getline(std::cin, str) && str != "q") {
        if (str == "help") {
            std::cout << "nothing" << std::endl;
        }
        if (str == "all") {
            for (int i = 0; i < nodes.size(); i++) {
                std::cout << "Name node: " << nodes[i]->get_object_name()  << "  Indexs: " << nodes[i]->get_index()<<" Value: " << nodes[i]->get_value() << std::endl;
            }
        }
        if (str == "pnd") {
            int a = 0;
            std::cout << "Write Number" << std::endl;
            std::cin >> a;

            std::cout << "Name node: " << nodes[a]->get_object_name() << std::endl;
            std::cout << "Secret?" << (nodes[a]->is_secret() ? "Yes" : "No") << std::endl;
            std::cout << "Have Secret node?" << (nodes[a]->secret_index ? "Yes" : "No") << std::endl;
            std::cout << "Malloc?" << (nodes[a]->malloc ? "Yes" : "No") << std::endl;
            std::cout << "Object have index non constant" << std::to_string(nodes[a]->have_index_non_consnant) << std::endl;
            //std::cout << "Parent: " << nodes[a]->Parent.first << std::endl;
            std::cout << "Graph: "<<std::endl << nodes[a]->Graph << std::endl;
       
            std::cout << "-----all edge nodes-----" << std::endl;
     
            for (auto i = nodes[a]->get_edges()->begin(); i != nodes[a]->get_edges()->end(); i++) {
                std::cout << "Name edge node: " << nodes[i->first]->get_object_name() << std::endl;
                std::cout << "Index edge node: " << i->first << std::endl;
                std::cout << "Marking edge node: " << i->second << std::endl;
                std::cout << "has not constant index" << std::to_string(nodes[i->first]->have_index_non_consnant) << std::endl;
                std::cout << "Secret?" << (nodes[i->first]->is_secret() ? "Yes" : "No") << std::endl;
                std::cout << "Malloc?" << (nodes[i->first]->malloc ? "Yes" : "No") << std::endl;

            }
            std::cout << "End " << std::endl;
        }
        if (str == "s") {
            /*for (int i = 0; i < Secret_variable.size(); i++) {
                std::cout << Secret_variable[i]->get_object_name() << std::endl;
            }*/
        }

    }

}

bool have_secret_index(std::vector<Node_inst*>* Graph, int u, std::set<int>* visited) {
    auto it = visited->find(u);
    if (it != visited->end())
        return false;

    Node_inst* ver = Graph->at(u);
    visited->insert(ver->get_index());
    if (ver->is_secret())
        return true;

    for (auto i = ver->get_edges()->begin(); i != ver->get_edges()->end(); i++) {
        //visited->insert(i->first);
        if (have_secret_index(Graph, i->first, visited))
            return true;
    }
    return false;
}

bool have_secret_index_DFS(std::vector<Node_inst*>* Graph, Node_inst* ver) {
    std::set<int> visited;
    return have_secret_index(Graph, ver->get_index(), &visited);
}

void dfs(std::vector<Node_inst*>* Graph, int u, std::set<int>* visited) {
    auto it = visited->find(u);
    if (it != visited->end())
        return;

    Node_inst* ver = Graph->at(u);
    visited->insert(ver->get_index());
    ver->set_secret(true);
    if (ver->get_edges()->size() > 0)
        ver->secret_index = true;

    for (auto i = ver->get_edges()->begin(); i != ver->get_edges()->end(); i++) {
        //visited->insert(i->first);
        Graph->at(i->first)->set_secret(true);
        if (Graph->at(i->first)->get_edges()->size() > 0)
            Graph->at(i->first)->secret_index = true;
        dfs(Graph, i->first, visited);
    }
}

void doDFS(std::vector<Node_inst*>* Graph, Node_inst* ver) {
    std::set<int> visited;
    dfs(Graph, ver->get_index(), &visited);

}
/*void parse_structure(Graph* matrix_graph, std::vector<Node_inst*>* nodes, StructType* strct, int index) {
    
    
    //std::cout << *nodes[index].get_object_name() << std::endl;
    //std::cout << nodes->at(index)->get_object_name() << std::endl;
    for (auto i = 0; i < strct->getNumElements(); i++) {
        Abstract_all_object.insert(nodes->at(index)->get_object_name() + "." + std::to_string(index));
        int new_node = nodes->size();

        if (strct->getElementType(i)->isStructTy()) {
            std::cout << "This, Field" << std::endl;
            StructType* check = cast<StructType>(strct->getElementType(i));
            nodes->at(index)->set_edge({ new_node, "[" + std::to_string(i) + "]" });
            nodes->push_back(new Node_inst("Fields", nodes->at(index)->get_object_name() + "." + std::to_string(i), {}, new_node, NULL, "StructType"));
            matrix_graph->add_v();
            matrix_graph->add_reb(index, new_node);
            parse_structure(matrix_graph, nodes, check, new_node);
        }
        else if (strct->getElementType(i)->isPointerTy()) {
            std::cout << "Is pointer" << std::endl;
            std::pair<bool, StructType*> flag_next = isStructType(strct->getElementType(i));
            if (flag_next.first) {
                std::cout << "Is pointer to struct" << std::endl;
                //StructType* check = cast<StructType>(strct->getElementType(i));
                nodes->at(index)->set_edge({ new_node, "[" + std::to_string(i) + "]" });
                nodes->push_back(new Node_inst("Fields", nodes->at(index)->get_object_name() + "." + std::to_string(i), {}, new_node, NULL, "StructType"));
                matrix_graph->add_v();
                matrix_graph->add_reb(index, new_node);
                parse_structure(matrix_graph, nodes, flag_next.second, new_node);
            }
        }
        else {
            nodes->at(index)->set_edge({new_node, "[" + std::to_string(i) + "]"});
            nodes->push_back(new Node_inst("Fields", nodes->at(index)->get_object_name() + "." + std::to_string(i), {}, new_node, NULL, "VariableType"));
            matrix_graph->add_v();
            matrix_graph->add_reb(index, new_node);

        }
    }
}*/



int CreateNodes(std::vector<Node_inst*>* nodes, std::string Type_inst, std::string Type_create, Value* val, std::string name_out) {
    std::string name;
    if (Type_create == "Object") {
        name = "O" + std::to_string(Abstract_all_object.size() + 1);
        Abstract_all_object.insert(name);
    }
    else if (Type_create == "Value") {
        name = val->getName().str();
        AllocValues.insert(name);
    }
    else if (Type_create == "TempValue") {
        name = std::to_string(Temp_values.size());
        Temp_values.insert(std::to_string(Temp_values.size()));
    }
    else if (Type_create == "ObjectArray") {
        name = name_out;
    }
    else if (Type_create == "ObjectStruct") {
        name = name_out;
    }
    else if (Type_create == "BinaryOperator") {
        name = name_out;
    }
    int node_indexs = nodes->size();
    //nodes->push_back(new Node_inst(Type_inst, name, {}, node_indexs, val == NULL ? NULL : val, Type_create));
    //matrix_graph->add_v();
    std::size_t pos = name.find("_secret");
    if (pos != std::string::npos) {
        nodes->push_back(new Node_inst(Type_inst, name, {}, node_indexs, val == NULL ? NULL : val, Type_create, true));
        Secret_variable.insert(nodes->at(node_indexs));
    }
    else {
        nodes->push_back(new Node_inst(Type_inst, name, {}, node_indexs, val == NULL ? NULL : val, Type_create, false));
    }



    return node_indexs;
}


void add_under_nodes( Node_inst* first, Node_inst* second, std::vector<Node_inst*>* nodes) {
    if (second->get_edges()->size() == 0) {
        first->set_edge({ second->get_index(), "" });
        /*if (first->is_secret())
            second->set_secret(true);*/
        if (second->is_secret())
            first->set_secret(true);
            //first->secret_index = true;
       
        return;
    }
    if (second->is_secret())
        first->set_secret(true);

    for (auto iter = second->get_edges()->begin(); iter != second->get_edges()->end(); iter++) {
        if (first->get_object_name() == nodes->at(iter->first)->get_object_name())
            continue;
        first->set_edge({ iter->first,iter->second });
        if (nodes->at(iter->first)->is_secret()) {
            first->set_secret(true);
            first->secret_index = true;
        }

        if (first->is_secret())
            nodes->at(iter->first)->set_secret(true);
       
    }
}

/*void check_parent(Node_inst* prom1, Node_inst* prom2, std::vector<Node_inst*>* nodes) {
    if (prom1->Parent != "" && prom2->Parent != "") {
        prom2->Graph += '\"' + prom2->Parent + '\"' + " -> " + '\"' + prom1->Parent + '\"' + ";\n";
        nodes->at(prom2->ind_Parent)->Graph += prom2->Graph;
    }
    else if (prom1->Parent == "" && prom1->get_type_instruction() == "AllocaInst" && prom2->Parent != "") {
        prom2->Graph += '\"' + prom2->Parent + '\"' + " -> " + '\"' + prom1->get_object_name() + '\"' + ";\n";
        nodes->at(prom2->ind_Parent)->Graph += prom2->Graph;
    }
    else if (prom1->Parent != "" && prom2->Parent == "" && prom2->get_type_instruction() == "AllocaInst") {
        prom2->Graph += '\"' + prom2->get_object_name() + '\"' + " -> " + '\"' + prom1->Parent + '\"' + ";\n";
    }
    else if (prom1->Parent == "" && prom2->Parent == "" && prom1->get_type_instruction() == "AllocaInst" && prom2->get_type_instruction() == "AllocaInst") {
        prom2->Graph += '\"' + prom2->get_object_name() + '\"' + " -> " + '\"' + prom1->get_object_name() + '\"' + ";\n";
    }
}*/



void AllocaInstParser(Value* val, std::vector<Node_inst*>* nodes) {
    auto n1 = std::find_if(nodes->begin(), nodes->end(), [=](Node_inst* e) {return e->get_value() == val; });
    if (n1 != nodes->end())
        return;
    int parent_index = CreateNodes(nodes, "AllocaInst","Value",val,"");
    int son_index = CreateNodes(nodes, "AllocaInst", "Object", NULL,"");
    //nodes->at(son_index)->Parent.first = nodes->at(parent_index)->get_object_name();
    nodes->at(son_index)->Parent.insert(nodes->at(parent_index)->get_object_name());

    nodes->at(parent_index)->Graph = "";
    if (nodes->at(parent_index)->is_secret())
        nodes->at(son_index)->set_secret(true);
    nodes->at(parent_index)->set_edge({ son_index, "" });
  
    
}

void LoadInstParser(Instruction& inst, std::vector<Node_inst*>* nodes, std::string path) {
    Value* val = cast<Value>(&inst); //p
    Value* arg1 = inst.getOperand(0); // q
    auto n1 = std::find_if(nodes->begin(), nodes->end(), [=](Node_inst* e) {return e->get_value() == arg1; });
    if (n1 != nodes->end()) {
          Node_inst* prom1 = *n1; // q
          Node_inst* prom2 = nodes->at(CreateNodes(nodes,  "Load", "TempValue", val,"")); //p
          if (prom1->is_secret())
              prom2->set_secret(true);
          if ((isStructType(val->getType()).first || isArrayType(val->getType()).first) || nodes->at(prom1->get_edges()->begin()->first)->get_type_instruction()
              == "Create_memory_Inst") { 
              prom2->add_edges(prom1, "", nodes);
              if (prom1->secret_index)
                  prom2->secret_index = true;
              for (auto iter = prom1->get_edges()->begin(); iter != prom1->get_edges()->end(); iter++) {
                  if (prom2->is_secret())
                      nodes->at(iter->first)->set_secret(true);
              }
              return;
          }
          for (auto iter = prom1->get_edges()->begin(); iter != prom1->get_edges()->end(); iter++) {
              add_under_nodes( prom2, nodes->at(iter->first),nodes);
          }
    }
}

void StoreInstParser(Instruction& inst, std::vector<Node_inst*>* nodes, std::map<Value*, Value*> func_arg, std::string path) {
    
    Value* arg1, *arg2;
    
    auto it1 = func_arg.find(inst.getOperand(0));
    auto it2 = func_arg.find(inst.getOperand(1));


    if (it1 != func_arg.end())
        arg1 = func_arg[inst.getOperand(0)];
    else
        arg1 = inst.getOperand(0); //q
   
    if (it2 != func_arg.end())
        arg2 = func_arg[inst.getOperand(1)];
    else
        arg2 = inst.getOperand(1);//p



    auto n1 = std::find_if(nodes->begin(), nodes->end(), [=](Node_inst* e) {return e->get_value() == arg1; });
    auto n2 = std::find_if(nodes->begin(), nodes->end(), [=](Node_inst* e) {return e->get_value() == arg2; });
    

    
    if (n1 != nodes->end() && n2 != nodes->end()) {
        Node_inst* prom1 = *n1; //q /array
        Node_inst* prom2 = *n2; //p /i
        
        /*if (prom1->get_object_name() == "%186") {
            Value* check = inst.getOperand(1);
            auto n3 = std::find_if(nodes->begin(), nodes->end(), [=](Node_inst* e) {return e->get_value() == check; });
            Node_inst* deb = *n3;
            std::cout << deb->get_index() << " " << deb->get_object_name() << std::endl;
            std::cout << std::endl;

        }*/
        
        /*if (prom1->get_type_instruction() == "AllocaInst") {
            prom2->Parent.insert(prom1->get_object_name());
        }
        else if (prom2->Parent.size() > 0) {
            prom2->Parent.merge(prom1->Parent);
        }*/

         if (prom1->is_secret()) {
            prom2->set_secret(true);
     
        }
          
      
      

        if (prom1->malloc)
            prom2->malloc = true;

        if (it1 != func_arg.end()) {
            if (prom1->Parent.size() > 0)
                prom2->Parent.merge(prom1->Parent);
            prom2->add_edges_set(prom1,nodes);
           
            //nodes->at(prom2->ind_Parent)->Graph = prom2->Graph;
            return;
        }

   

       
        if (prom1->bitcast) {
            prom2->add_edges_set(prom1, nodes);
            return;
        }

        for (auto iter = prom2->get_edges()->begin(); iter != prom2->get_edges()->end(); iter++) {
            add_under_nodes( nodes->at(iter->first), prom1,nodes);
        }
    }
    
}

std::string find_name(std::string in_find, std::string a, std::string Type) {
    std::smatch color_match;
    const std::regex r(R"([O](.)*)");
    std::string name;
    if (std::regex_search(in_find, color_match, r)) {
        if(Type == "StructType")
            name = std::string(color_match[0]) + "." + a;
        if (Type == "ArrayType")
            name = "[" + a + "]" + std::string(color_match[0]);
    }
    else {
        if (Type == "StructType")
            name = in_find + "." + a;
        if(Type == "ArrayType")
            name = "[" + a + "]" + in_find;
    }
    //std::cout << name << std::endl;
    return name;
}

/*bool have_secret_index(std::vector<Node_inst*>* nodes, Node_inst* val) {
    if (val->is_secret())
        return true;
    for (auto iter = val->get_edges()->begin(); iter != val->get_edges()->end(); iter++) {
        if (have_secret_index(nodes, nodes->at(iter->first)))
            return true;
    }
    return false;
}*/

bool equal_obj(Node_inst* obj1, Node_inst* obj2_finding, std::vector<Node_inst*>* nodes) {

    if (obj1 == obj2_finding)
        return true;
    for (auto iter = obj1->get_edges()->begin(); iter != obj1->get_edges()->end(); iter++) {
        if (equal_obj(nodes->at(iter->first), obj2_finding, nodes))
            return true;
    }
    return false;
}

/*bool find_origin_secret_variable(Node_inst* obj, std::vector<Node_inst*>* nodes) {
    for (int i = 0; i < Secret_variable.size(); i++) {
        if (equal_obj(Secret_variable[i], obj, nodes)) {
            std::cout << Secret_variable[i]->get_object_name() << std::endl;
            return true;
        }
    }
    return false;
}*/

void GetElementParser(Instruction& inst, std::vector<Node_inst*>* nodes, std::string This_Func, std::pair<Function*,int> f_parent, std::string path) {
    Value* pointer_start = inst.getOperand(0);
    Value* val = cast<Value>(&inst);

    auto n1 = std::find_if(nodes->begin(), nodes->end(), [=](Node_inst* e) {return e->get_value() == pointer_start; });
    if (n1 != nodes->end()) {
        Node_inst* prom = *n1;
        Node_inst* object = nodes->at(prom->get_edges()->begin()->first);
        Node_inst* prom1 = nodes->at(CreateNodes(nodes, "GetElementPtr", "Value", val, ""));
        if (prom->get_type_instruction() == "AllocaInst")
            prom1->Parent.insert(prom->get_object_name());
        else if (prom->Parent.size() > 0)
            prom1->Parent.merge(prom->Parent);
        //prom1->Parent = prom->get_object_name();
        Node_inst* leak = nullptr;

        std::string index = "";
        int a = 0;

        for (int i = 1; i < inst.getNumOperands(); i++) {
            if (ConstantInt* k = dyn_cast<ConstantInt>(inst.getOperand(i))) {
                a += k->getZExtValue();
                //str += "[" + std::to_string(a) + "]";
            }
            else {
                index = "[*]";
                Value* val = inst.getOperand(i);
                auto n1 = std::find_if(nodes->begin(), nodes->end(), [=](Node_inst* e) {return e->get_value() == val; });
                if (n1 != nodes->end()) {
                    leak = *n1;
                    //std::cout << leak->get_object_name() << std::endl;
                }
                break;
            }

        }


        if (index != "[*]") {
            index = "[" + std::to_string(a) + "]";
        }
       
        
        //Structuru and Array можно обьединить
        
        if (isStructType(pointer_start->getType()).first) {
            if (object->find_edge(index).first == -1) {
                std::string name = find_name(object->get_object_name(), std::to_string(a), "StructType");

                int temp_node_size = CreateNodes(nodes, "GetElementPtr", "ObjectStruct", NULL,name);
                if (object->is_secret()) {
                    nodes->at(temp_node_size)->set_secret(true);
                    prom1->secret_index = true;
                    prom1->set_secret(true);
                }

                object->set_edge({ temp_node_size, index }); //добавляем для объекта ребро для нового обхекта
                //matrix_graph->add_reb(object->get_index(), temp_node_size); //тоже самое для матрицы смежности

                prom1->set_edge({ temp_node_size , index }); // для ново регистра создаем ребро между новым объектом
                //matrix_graph->add_reb(prom1->get_index(), temp_node_size);//тоже самое для матрицы смежности
            }
            else {
                prom1->set_edge(object->find_edge(index));
            }
        }
        else if (isArrayType(pointer_start->getType()).first || pointer_start->getType()->isPointerTy()) {
            if (object->find_edge(index).first == -1) {
                std::string name = find_name(object->get_object_name(), index == "[*]" ? "*" : std::to_string(a), "ArrayType");
                int temp_node_size = CreateNodes(nodes,  "GetElementPtr", "ObjectArray", NULL,name);
                if (index == "[*]") {
                    object->have_index_non_consnant = true;
                }
                //interface_with_data(*nodes);
                if (object->is_secret()) {
                    nodes->at(temp_node_size)->set_secret(true);
                    prom1->secret_index = true;
                    prom1->set_secret(true);
                }
                object->set_edge({ temp_node_size, index }); //добавляем для объекта ребро для нового обхекта
                //matrix_graph->add_reb(object->get_index(), temp_node_size); //тоже самое для матрицы смежности

                prom1->set_edge({ temp_node_size , index }); // для ново регистра создаем ребро между новым объектом
                //matrix_graph->add_reb(prom1->get_index(), temp_node_size);//тоже самое для матрицы смежности
            }
            else {
                //std::cout << nodes->at(object->find_edge(index).first)->get_object_name() << std::endl;
                //interface_with_data(*nodes);
                if (nodes->at(object->find_edge(index).first)->is_secret() ) {
                   
                    prom1->secret_index = true;
                    prom1->set_secret(true);
                }
                prom1->set_edge(object->find_edge(index));
            }
        }

        if (object->have_index_non_consnant) {
            Node_inst* temp_node = nodes->at(object->find_edge("[*]").first);
            
            for (auto iter = object->get_edges()->begin(); iter != object->get_edges()->end(); iter++) {
                if (iter->second == "[*]")
                    continue;
                std::pair<int, std::string> finded_node = temp_node->find_edge("[*]");
                if (finded_node.first == -1)
                    break;
                if (temp_node->is_secret())
                    nodes->at(iter->first)->set_secret(true);
                if (nodes->at(iter->first)->is_secret())
                    temp_node->set_secret(true);
                nodes->at(iter->first)->set_edge({finded_node.first, "[*]"});
                //matrix_graph->add_reb(iter->first, finded_node.first);

            }
            for (auto iter = object->get_edges()->begin(); iter != object->get_edges()->end(); iter++) {
                if (iter->second == "[*]")
                    continue;
                if (nodes->at(iter->first)->is_secret())
                    temp_node->set_secret(true);
                temp_node->add_edges(nodes->at(iter->first), "", nodes);
                
            }
        }
        const llvm::DebugLoc& debugInfo = inst.getDebugLoc();
        
        if (index == "[*]") {
            if (leak != nullptr && (leak->secret_index || leak->is_secret() || have_secret_index_DFS(nodes,leak))) {
                std::string out = "Leakeage memory from func " + This_Func + " Line: "+ std::to_string(debugInfo->getLine()) + " Called func from " + f_parent.first->getName().str() + " " + "Line: " + std::to_string(f_parent.second)  + "\n";
                Out.insert(out);
                Find_leaking.insert(leak);
                //Secret_variable.push_back(leak);
                //std::cout << "Leakeage memory from func " << This_Func << " Called func from "<<Parent_Func << "  |" << leak->get_object_name() << "|" << debugInfo->getLine() << std::endl;
                //errs() << inst << "\n";
      
            }
        }

    }
}


void output_in_file(std::ofstream *fout) {
    //std::ofstream fout(out_txt);
    *fout << std::endl;
    for (auto i = Out.begin(); i != Out.end(); i++) {
        *fout << *i;
    }
    fout->close();
}
void output_in_consolee(std::ostream* fout) {
    //std::ofstream fout(out_txt);
    *fout << std::endl;
    for (auto i = Out.begin(); i != Out.end(); i++) {
        *fout << *i;
    }
}

void Binary_Operator_parser(Instruction& inst, std::vector<Node_inst*>* nodes, std::map<Value*, Value*> func_arg, std::string path) {
    Value* val = cast<Value>(&inst);
    Value* arg1 = inst.getOperand(0);//q 
    Value* arg2 = inst.getOperand(1);//p 

    Node_inst* new_node = nodes->at(CreateNodes(nodes, "BinaryOperator", "BinaryOperator", val, ""));

    auto n1 = std::find_if(nodes->begin(), nodes->end(), [=](Node_inst* e) {return e->get_value() == arg1; });
    auto n2 = std::find_if(nodes->begin(), nodes->end(), [=](Node_inst* e) {return e->get_value() == arg2; });

    if (n1 != nodes->end() && n2 != nodes->end()) {
        //interface_with_data(nodes_temp, *matrix_graph);
        Node_inst* prom1 = *n1;
        Node_inst* prom2 = *n2;
        if (prom1->get_type_instruction() == "AllocaInst" && prom2->get_type_instruction() == "AllocaInst") {
            new_node->Parent.insert(prom1->get_object_name());
            new_node->Parent.insert(prom2->get_object_name());
        }

        else if (prom1->get_type_instruction() == "AllocaInst") {
            new_node->Parent.insert(prom1->get_object_name());
            new_node->Parent.merge(prom2->Parent);
        }
        else if (prom2->get_type_instruction() == "AllocaInst") {
            new_node->Parent.insert(prom2->get_object_name());
            new_node->Parent.merge(prom1->Parent);
        }

        if (prom1->is_secret() || prom2->is_secret()) {
            new_node->set_secret(true);
            prom1->set_secret(true);
            prom2->set_secret(true);
        }
        new_node->add_edges(prom1, "", nodes);
        new_node->add_edges(prom2, "", nodes);
    }
    else if (n1 != nodes->end()) {
        Node_inst* prom1 = *n1;
        if (prom1->is_secret())
            new_node->set_secret(true);
        new_node->add_edges(prom1, "", nodes);
        for (auto iter = prom1->get_edges()->begin(); iter != prom1->get_edges()->end(); iter++) {
            // matrix_graph->add_reb(new_node->get_index(), iter->first);
        }
    }
    else if (n2 != nodes->end()) {
        Node_inst* prom2 = *n2;
        if (prom2->is_secret())
            new_node->set_secret(true);

        new_node->add_edges(prom2, "", nodes);
        for (auto iter = prom2->get_edges()->begin(); iter != prom2->get_edges()->end(); iter++) {
            // matrix_graph->add_reb(new_node->get_index(), iter->first);
        }
    }
}

void CallInst_operator(Instruction& inst, std::vector<Node_inst*>* nodes, std::map<Value*, Value*> func_arg, std::string path, Function* f) {
    CallInst* k = dyn_cast<CallInst>(&inst);
    Value* val = cast<Value>(&inst);

    if (!k->getCalledFunction())
        return;

    if (k->getCalledFunction()->getName().str() == f->getName().str())
        return;
    if (k->getCalledFunction()->getName().str() == "malloc" || k->getCalledFunction()->getName().str() == "calloc") {

        int prom_size1 = nodes->size();
        Abstract_all_object.insert("O" + std::to_string(Abstract_all_object.size() + 1));
        nodes->push_back(new Node_inst("Create_memory_Inst", val->getName().str(), { nodes->size() + 1, "" }, nodes->size(), val, "", false));

        nodes->at(prom_size1)->malloc = true;

        int prom_size2 = nodes->size();
        nodes->push_back(new Node_inst("Create_memory_Inst", "O" + std::to_string(Abstract_all_object.size()), {}, nodes->size(), NULL, "", false));
        nodes->at(prom_size2)->malloc = true;
    }

    std::size_t pos = k->getCalledFunction()->getName().str().find("memcpy");
    if (pos != std::string::npos) {
        Value* arg1 = inst.getOperand(0);
        Value* arg2 = inst.getOperand(1);

        GetElementPtrInst* deb1 = cast<GetElementPtrInst>(arg1);
        GetElementPtrInst* deb2 = cast<GetElementPtrInst>(arg2);


        auto n1 = std::find_if(nodes->begin(), nodes->end(), [=](Node_inst* e) {return e->get_value() == arg1; });
        auto n2 = std::find_if(nodes->begin(), nodes->end(), [=](Node_inst* e) {return e->get_value() == arg2; });

        if (deb1 != nullptr && n1 == nodes->end()) {
            arg1 = deb1->getOperand(0);
            n1 = std::find_if(nodes->begin(), nodes->end(), [=](Node_inst* e) {return e->get_value() == arg1; });
        }
        if (deb2 != nullptr && n2 == nodes->end()) {
            arg2 = deb2->getOperand(0);
            n2 = std::find_if(nodes->begin(), nodes->end(), [=](Node_inst* e) {return e->get_value() == arg2; });
        }

        if (n1 != nodes->end() && n2 != nodes->end()) {
            Node_inst* prom1 = *n1;
            Node_inst* prom2 = *n2;

            if (prom2->is_secret()) {
                prom1->set_secret(true);
            }



            //prom1->add_edges(prom2,"", & nodes_temp);
            for (auto iter = prom1->get_edges()->begin(); iter != prom1->get_edges()->end(); iter++) {
                if (prom2->is_secret())
                    nodes->at(iter->first)->set_secret(true);
                nodes->at(iter->first)->add_edges(prom2, "", nodes);
            }

        }
    }

    auto it = Func_name.find(k->getCalledFunction()->getName().str());
    if (it != Func_name.end()) {

        int prom_size1 = nodes->size();
        Abstract_all_object.insert("O" + std::to_string(Abstract_all_object.size() + 1));
        nodes->push_back(new Node_inst("CallInst", val->getName().str(), {}, nodes->size(), val, "", false));
        // matrix_graph->add_v();

        std::vector<Value*> val_this;
        for (auto iter = k->arg_begin(); iter != k->arg_end(); iter++) {

            Value* check = cast<Value>(iter);
            GetElementPtrInst* deb = cast<GetElementPtrInst>(check);
            auto n1 = std::find_if(nodes->begin(), nodes->end(), [=](Node_inst* e) {return e->get_value() == check; });
            if (n1 != nodes->end()) {
                val_this.push_back(cast<Value>(iter));
            }
            else if (deb != nullptr) {
                // std::cout << deb->getName().str() << std::endl;
                val_this.push_back(cast<GetElementPtrInst>(check)->getOperand(0));
            }
        }
        const llvm::DebugLoc& debugInfo = inst.getDebugLoc();
        Node_inst* res = get_analyse_func(k->getCalledFunction(), nodes, val_this, { f,debugInfo->getLine() }, path);

        if (res == nullptr)
            return;

        if (res->malloc)
            nodes->at(prom_size1)->malloc = true;
        if (res->is_secret())
            nodes->at(prom_size1)->set_secret(true);
        if (res->secret_index)
            nodes->at(prom_size1)->secret_index = true;

        nodes->at(prom_size1)->add_edges(nodes->at(res->get_edges()->begin()->first), "", nodes);
        nodes->at(prom_size1)->bitcast = true;
    }
}

Node_inst* get_analyse_func(Function* f, std::vector<Node_inst*> *nodes,std::vector<Value*> values, std::pair<Function*, int> f_parent, std::string path) {

    std::stack<CallInst*> stack_func;
   // std::vector<Node_inst*> nodes;
    std::map<Value*, Value*> func_arg;
    int i = 0;
    for (auto iter = f->arg_begin(); iter != f->arg_end(); iter++) {
        //func_arg.insert(cast<Value>(iter));
        func_arg.insert({ cast<Value>(iter), values[i] });
        i++;
    }

    //НА БУДУЩЕЕ,если что то пойдет не так!!! Если лоад будет бесить со своими кривыми добавлениям вершин, то сделать проверку на структуру и массив.
    //То есть, если структура/массив то присваивать не q->po and po->o, then p->o, а просто q->o, then p->o

    //Graph matrix_graph;
    //add_argument_f(f, set_Variable, matrx_graph, marks_args, index_marks_variable);


    for (auto iter2 = f->getBasicBlockList().begin(); iter2 != f->getBasicBlockList().end(); iter2++) {
        BasicBlock& bb = *iter2;
        std::vector<Node_inst*> nodes_temp = *nodes;
        //std::cout << "  BasicBlock: " << bb.getName().str() << std::endl;
        for (auto iter3 = bb.begin(); iter3 != bb.end(); iter3++) {
            Instruction& inst = *iter3;
            
            //alloca parser
            if (isa<AllocaInst>(&inst)) {
                AllocaInstParser(cast<Value>(&inst), &nodes_temp);
            }
            //IcmpCast если один из аргументов является чувствительным, то помечаем новую переменную как чувсвтительную
            else if (isa<ICmpInst>(&inst)) {
                Value* arg1 = inst.getOperand(0);
                Value* arg2 = inst.getOperand(1);

                auto n1 = std::find_if(nodes_temp.begin(), nodes_temp.end(), [=](Node_inst* e) {return e->get_value() == arg1; });
                auto n2 = std::find_if(nodes_temp.begin(), nodes_temp.end(), [=](Node_inst* e) {return e->get_value() == arg2; });

                if (n1 != nodes_temp.end()) {
                    Node_inst* temp = *n1;

                    if (temp->is_secret() || (have_secret_index_DFS(&nodes_temp,temp) && !isa<ConstantPointerNull>(arg2))) {
                        const llvm::DebugLoc& debugInfo = inst.getDebugLoc();
                        std::string out = "Leakeage condition from line: " + f->getName().str() + " " + std::to_string(debugInfo->getLine()) + "\n";
                        Out.insert(out);
                    }
                }
                if (n2 != nodes_temp.end()) {
                    Node_inst* temp = *n2;
                        if (temp->is_secret() || (have_secret_index_DFS(&nodes_temp, temp) && !isa<ConstantPointerNull>(arg1))) {
                        const llvm::DebugLoc& debugInfo = inst.getDebugLoc();
                        std::string out = "Leakeage condition from line: " + f->getName().str() + " " + std::to_string(debugInfo->getLine()) + "\n";
                        Out.insert(out);
                    }

                }
            }
            else if (isa<CastInst>(&inst)) {
                Value* val = cast<Value>(&inst);
                Value* arg1 = inst.getOperand(0);

                auto n1 = std::find_if(nodes_temp.begin(), nodes_temp.end(), [=](Node_inst* e) {return e->get_value() == arg1; });

                if (n1 != nodes_temp.end()) {

                    if (f->getName().str() == "main")
                        std::cout << std::endl;
                    Node_inst* prom2 = *n1;
                    
                    Node_inst* prom1 = new Node_inst("Cast", "%" + std::to_string(Temp_values.size()), {}, nodes_temp.size(), val, prom2->get_type(), false);

                    if (prom2->get_type_instruction() == "AllocaInst")
                        prom1->Parent.insert(prom2->get_object_name());
                    else if (prom2->Parent.size() > 0)
                        prom1->Parent.merge(prom2->Parent);
    
                    //if(val->hasName())
                        //prom1 = new Node_inst("Cast", val->getName().str(), {}, nodes_temp.size(), val, prom2->get_type(), false);
                   
                    Temp_values.insert(std::to_string(Temp_values.size()));
                    nodes_temp.push_back(prom1);
                    //matrix_graph->add_v();

                    if (prom2->malloc)
                        prom1->malloc = true;

                    prom1->add_edges_set(prom2,&nodes_temp);
                    prom1->bitcast = true;
                    //add_under_nodes(matrix_graph, prom1, prom2, &nodes_temp);

                    
                }
                else {
                    continue;

                }


            }
            else if (isa<StoreInst>(&inst)) {
                
                StoreInstParser(inst, &nodes_temp,func_arg,path);
            }
            else if (isa<LoadInst>(&inst)) {
                LoadInstParser(inst, &nodes_temp,path);
            }
        
            else if (isa<GetElementPtrInst>(&inst)) {
             
                GetElementParser(inst, &nodes_temp, f->getName().str(), f_parent,path);
            }
            else if (isa<BinaryOperator>(&inst)) {
               Binary_Operator_parser(inst, &nodes_temp, func_arg, path);
            }

            else if (CallInst* k = dyn_cast<CallInst>(&inst)) {
                CallInst_operator(inst, &nodes_temp, func_arg, path, f);
            }
            else if (BranchInst* k = dyn_cast<BranchInst>(&inst)) {
                    //interface_with_data(nodes_temp, matrix_graph);
                    //std::cout << nodes_temp[0]->get_index() << std::endl;
                    if (nodes->size() == 0) {
                        *nodes = nodes_temp;
                        continue;
                    }
                    else {
                        if (nodes->size() != nodes_temp.size())
                            nodes->resize(nodes_temp.size());
                        for (int i = 0; i < nodes->size(); i++) {
                            if (nodes->at(i) == nullptr) {
                                nodes->at(i) = nodes_temp[i];
                                continue;
                            }
                            nodes->at(i)->add_edges(nodes_temp[i], "", &nodes_temp);
                        }
                    }
                }

            if (++iter3 == bb.end() && nodes->size() == 0) {
                 *nodes = nodes_temp;
                 break;
            }
            else {
                --iter3;
            }
            //interface_with_data(nodes_temp);
        }
        *nodes = nodes_temp;

    }
    //std::cout << nodes->at(0)->get_index() << std::endl;
    if (f->getName().str() == "main") {
        if (out_txt != "") {
            std::ofstream fout(out_txt);
            output_in_file(&fout);
        }
        else {
            output_in_consolee(&std::cout);
        }
 
        interface_with_data(*nodes);
        
    }
    //matrix_graph.print();
    return nullptr;
}

std::string find_original_var(Instruction* inst) {
    if (inst->hasName())
        return inst->getName().str();
    if (isa<LoadInst>(inst))
        return find_original_var(cast<Instruction>(inst->getOperand(0)));
    else if (isa<GetElementPtrInst>(inst))
        return find_original_var(cast<Instruction>(inst->getOperand(0)));
    else if (isa<BinaryOperator>(inst)) {
        std::cout << "Lol" << std::endl;
    }
    else if (isa<AllocaInst>(inst)) {
        return inst->getName().str();
    }
   


        return "";
}

void find_repeat(std::set<std::string> *out, std::string s) {
    auto find = out->find(s);
    if (find != out->end()) {
        out->erase(find);
    }
    return;
}

int main(int argc, char* argv[])
{
        std::vector<std::vector<int>> matrx_graph;
        std::map<Value*, int> set_Variable;
        std::unordered_map<Value*, Instruction*> pointers_value_inst;
        std::string path = "";
        //std::vector<std::vector<Instruction*>> vectors_ptr;
        //std::vector<ptr_array_mark> vectors_ptr;
        std::vector<std::string> mark_variable = { "a" };
        //std::set<Instruction> pointer_set;s
       // std::set<Instruction> set_pointers;

        StringRef filename = argv[argc-1];
        std::string get_name_func = "";

        LLVMContext context;
        SMDiagnostic Err;

        std::cout << "Start" << std::endl;

        for (auto i = 1; i < argc - 1; ++i) {
            if (std::string(argv[i]) == "-start_function") {
                get_name_func = argv[i + 1];
                i++;
                std::cout << "Find function: Success" << std::endl;
                continue;
            }
            else if (std::string(argv[i]) == "-out_put") {
                out_txt = argv[i + 1];
                i++;
                std::cout << "Create out.txt: Success" << std::endl;
                continue;
            }
            std::cout << argv[i] << std::endl;
        }

        std::unique_ptr< Module > Mod = parseIRFile(filename, Err, context);

        Module* m = Mod.get();

        DataLayout* TD = new DataLayout(m);

        Module::GlobalListType& global_list = m->getGlobalList();


        std::string out_graph;

        Function* f = m->getFunction(get_name_func);
        std::vector<Node_inst*> nodes;
        //Graph matrix_graph;
        std::vector<Value*> val;

        for (auto iter = global_list.begin(); iter != global_list.end(); iter++) {
            Value* val = cast<Value>(iter);
            AllocaInstParser(val, &nodes);
        }

        for (auto iter = f->arg_begin(); iter != f->arg_end(); iter++) {
            val.push_back(cast<Value>(iter));
        }
        get_analyse_func(f, &nodes, val, { f,-1 }, path);
        std::queue<Value*> que_val;
        //Find_Path(m->getFunction("F"), nodes);
}
