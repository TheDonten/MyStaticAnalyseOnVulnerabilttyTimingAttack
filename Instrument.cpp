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

class Analyse_func {
private:
    std::vector<std::vector<int>> matrx_graph;
    std::unordered_map <Value*, int> map_Variable;

    std::unordered_set<Value*> set_args;

    std::vector<int> index_marks_variable;
    std::vector<bool> send_marks_args;

    std::string type_argument;



    std::vector<std::vector<Instruction*>> vectors_ptr;
    std::vector<std::vector<std::pair<Instruction*,bool>>> output_marks_ptr;



    void add_v() {

        if (matrx_graph.size() == 0) {
            matrx_graph.resize(1);
            matrx_graph[0].push_back(0);
            return;
        }
        std::vector<int> prom_vec;
        for (int i = 0; i < matrx_graph.size(); i++) {

            matrx_graph[i].push_back(0);
            prom_vec.push_back(0);

        }
        prom_vec.push_back(0);
        matrx_graph.push_back(prom_vec);
        return;
    }

   

    

    void add_reb(int a, int b) {
        this->matrx_graph[a][b] = 1;
    }

    Value* find_by_index(int index, std::unordered_map<Value*, int> map_Variable) {
        for (auto& [key, value] : map_Variable) {
            if (value == index)
                return key;
        }
    }

public:
    Analyse_func() {};

    Analyse_func(std::vector<std::vector<int>> matrx_graph,
        std::unordered_map<Value*, int > map_Variable,
        std::vector<int> index_marks_variable,
        std::vector<bool> send_marks_args) {
        this->matrx_graph = matrx_graph;
        this->map_Variable = map_Variable;
        this->index_marks_variable = index_marks_variable;
        this->send_marks_args = send_marks_args;
    };


    Value* find_start_value(Value* val) {

        if (isa<AllocaInst>(val)) {
            return val;
        }

        else if (LoadInst* temp = dyn_cast<LoadInst>(val)) {
            Value* arg = temp->getOperand(0);
            std::cout << arg->getName().str() << std::endl;
            return find_start_value(arg);
        }
        else if (StoreInst* temp = dyn_cast<StoreInst>(val)) {
            Value* arg = temp->getOperand(0);
            return find_start_value(arg);
        }
    }

    std::pair<Instruction*, Value*> get_start_address(Instruction* inst) {
        Value* temp = inst->getOperand(0); // пока что так, но надо доходить рекурсивно до инструкции alloca
        std::cout << inst->getName().str() << std::endl;
        std::cout << temp->getName().str();
        if (isa<AllocaInst>(temp)) {
            return { inst, temp };
        }
        else {
            return { inst, find_start_value(temp) };
        }

        /*if (LoadInst* prom = dyn_cast<LoadInst>(temp)) {
            //std::cout << prom->getOperand(0)->getName().str();
            return { inst,prom->getOperand(0) };
        }
        if (StoreInst* prom = dyn_cast<StoreInst>(temp)) {
            //std::cout << prom->getOperand(0)->getName().str();
            return { inst,prom->getOperand(0) };
        }*/

        //std::cout << temp->getName().str() << std::endl;
        //return { inst, temp };
    }
    
    void print_graph() {
        for (int i = 0; i < matrx_graph.size(); i++) {
            Value* arg1 = find_by_index(i, map_Variable);
            std::cout << "Index row =" << i << " Name Variable =" << arg1->getName().str() << "(" << arg1 << ")" << std::endl;
            // std::cout << "This variable has dependent with:" <<std::endl;
            for (int j = 0; j < matrx_graph[i].size(); j++) {
                std::cout << matrx_graph[i][j];
                if (matrx_graph[i][j]) {
                    //Value* arg2 = find_name(j, set_Variable);
                    //std::cout << "Index columns =" << j << " Name Variable =" << arg2->getName().str() << "(" << arg2 << ")";

                }
            }
            std::cout << std::endl;

        }
    }

    void get_analyze_ptr(std::vector<Instruction*>& ptr) {
        if (this->vectors_ptr.size() > 0) {
            for (auto& arr : this->vectors_ptr) {
                if (arr.size() == ptr.size() && arr.size() > 0 && ptr.size() > 0) {
                    if (arr[0]->getType()->getPointerElementType() != ptr[0]->getType()->getPointerElementType()) //Если типы не совпадают, то берем следующий указатель
                        continue;
                    std::pair<Instruction*, Value*> Start_address_arr = get_start_address(arr[0]);
                    std::pair<Instruction*, Value*> Start_address_ptr = get_start_address(ptr[0]);

                    if (Start_address_arr.second != Start_address_ptr.second) {
                        continue;
                    }
                    bool flag_check_operand = true;
                    for (size_t i = 1; i < arr[0]->getNumOperands(); i++) {
                        Value* op1 = arr[0]->getOperand(i);
                        Value* op2 = ptr[0]->getOperand(i);
                        if (op1 != op2) {
                            flag_check_operand = false;
                            break;
                        }
                    }
                    if (!flag_check_operand)
                        continue;
                    auto ptr1 = this->map_Variable.find(cast<Value>(arr[0]));
                    auto ptr2 = this->map_Variable.find(cast<Value>(ptr[0]));
                    add_reb(ptr1->second, ptr2->second);
                    for (size_t i = 1; i < arr.size(); i++) {
                        if (Start_address_arr.second != Start_address_ptr.second
                            && ptr[i]->getOperand(0) == cast<Value>(Start_address_ptr.first)
                            && arr[i]->getOperand(0) == cast<Value>(Start_address_arr.first)) {
                            continue;
                        }
                        bool flag_check_operand = true;
                        for (size_t j = 1; j < arr[i]->getNumOperands(); j++) {
                            Value* op1 = arr[i]->getOperand(j);
                            Value* op2 = ptr[i]->getOperand(j);
                            if (op1 != op2) {
                                flag_check_operand = false;
                                break;
                            }
                        }
                        if (!flag_check_operand)
                            continue;
                        auto ptr1 = this->map_Variable.find(cast<Value>(arr[i]));
                        auto ptr2 = this->map_Variable.find(cast<Value>(ptr[i]));
                        add_reb(ptr1->second, ptr2->second);
                        Start_address_arr.first = arr[i];
                        Start_address_ptr.first = ptr[i];
                    }
                }
            }
        }
        return;
    }
    bool find_secret_leakeage(int indexs) { //DILocation* Loc
        std::vector<bool> bl;
        bl.resize(this->matrx_graph.size());
        for (int i = 0; i < index_marks_variable.size(); i++) {
            if (find_path(this->index_marks_variable[i], indexs, bl)) {
                return true;
            }
        }
        return false;
    }
	
	

    bool find_path(int v1, int v2, std::vector<bool> visited) {
        if (v1 == v2) {
            return true;
        }
        visited[v1] = true;
        for (int i = 0; i < this->matrx_graph.size(); i++) {
            if (matrx_graph[v1][i]) {
                if (!visited[i]) {
                    if (find_path(i, v2,visited))
                        return true;
                }
            }
        }
        return false;
    }
	
	void get_memory_leakege(Instruction* inst){
		for (int i = 1; i < inst->getNumOperands(); i++) {
            auto arg = map_Variable.find(inst->getOperand(i));
            if (arg != map_Variable.end()) {
                if (find_secret_leakeage(arg->second)) {
                    std::cout << "------------------------------------------------" << std::endl;
                    std::cout << "Secret access memory Leakeage " << " Line: " << Loc->getLine() << std::endl;
                    std::cout << "------------------------------------------------" << std::endl;
                }
            }
        }
	}
	
	void find_secret_leakeage_branch(Instruction* inst) {
        MDNode* MD = inst->getMetadata("dbg");
        DILocation* Loc = dyn_cast<DILocation>(MD);
        Value* cond = inst->getOperand(0);
        auto it = map_Variable.find(cond);
        if (it != map_Variable.end() && this->find_secret_leakeage(it->second)) {
                std::cout << "----------------------------------------------------" << std::endl;
                std::cout << it->first->getName().str() << std::endl;
                std::cout << " Leakage condition branch!!!" << " Line: " << Loc->getLine() << std::endl;
                std::cout << "----------------------------------------------------" << std::endl;
        }
    }
	
    void add_arguments(Function* f, std::vector<bool>& marks_args) {
        size_t i = 0;
        for (auto iter = f->arg_begin(); iter != f->arg_end(); iter++) {
            if (!marks_args.empty() && marks_args[i]) {
                index_marks_variable.push_back(map_Variable.size());
            }
            set_args.insert(cast<Value>(iter));
            map_Variable.insert({ cast<Value>(iter),map_Variable.size() });
            add_v();
        }
    }

    void alloca_parser(Instruction* inst) {
        Value* prom = cast<Value>(inst);
        size_t n_pos = prom->getName().str().find("_secret");
        if (n_pos != std::string::npos)
            this->index_marks_variable.push_back(this->map_Variable.size());
        this->map_Variable.insert({ prom, map_Variable.size() });
        this->add_v();
    }
    void parser_binary_operator(Instruction* inst) {
        int v = map_Variable.size();
        map_Variable.insert({ cast<Value>(inst), v });
        
        Value* arg1 = inst->getOperand(0);
        Value* arg2 = inst->getOperand(1);

        auto it = map_Variable.find(arg1);
        add_reb(it->second, v);
        it = map_Variable.find(arg2);
        add_reb(it->second, v);
    }

    void parser_getelementptr(Instruction* inst, llvm::BasicBlock::iterator &iter) {
        int v = map_Variable.size();
        map_Variable.insert({ cast<Value>(inst), v });
        add_v();
        std::vector<Instruction*> ptr;
        ptr.push_back(inst);

        if (!isa<GetElementPtrInst>(*(iter->getNextNode()))) {
            auto arg0 = map_Variable.find(inst->getOperand(0));
            add_reb(arg0->second, v);
            this->vectors_ptr.push_back(ptr);
        }
        while (isa<GetElementPtrInst>(*(iter->getNextNode()))) {
            ++iter;
            Instruction& getPtr = *iter;
            //std::cout << getPtr.getName().str() << std::endl;
            auto arg0 = map_Variable.find(getPtr.getOperand(0));
            map_Variable.insert({ cast<Value>(&getPtr), map_Variable.size() });
            add_v();
            add_reb(arg0->second, map_Variable.size() - 1);

            ptr.push_back(&getPtr);
        }
        get_analyze_ptr(ptr);
        this->vectors_ptr.push_back(ptr);
    }
    void parser_load(Instruction* inst) {
        int v = map_Variable.size();
        map_Variable.insert({ cast<Value>(inst), v});
        add_v();
        Value* arg = inst->getOperand(0);
        auto it = map_Variable.find(arg);
        add_reb(it->second, v);
    }

    void parser_store(Instruction* inst) {
        Value* arg1 = inst->getOperand(0);
        auto it1 = map_Variable.find(arg1);
        if (it1 == map_Variable.end())
            return;

        Value* arg2 = inst->getOperand(1);
        auto it2 = map_Variable.find(arg2);
        if (it2 == map_Variable.end())
            return;

        add_reb(it1->second, it2->second);

    }
    void parser_Icmp(Instruction* inst) {
        int v = map_Variable.size();
        map_Variable.insert({ cast<Value>(inst), v});
        add_v();
        Value* arg1 = inst->getOperand(0);
        Value* arg2 = inst->getOperand(1);

        auto it1 = map_Variable.find(arg1);
        auto it2 = map_Variable.find(arg2);

        if (it1 != map_Variable.end()) {
            add_reb( it1->second, v);
        }
        if (it2 != map_Variable.end()) {
            add_reb( it2->second, v);
        }
    }

    void parser_sext(Instruction* inst) {
        int v = map_Variable.size();
        map_Variable.insert({ cast<Value>(inst), v });
        add_v();
        Value* arg = inst->getOperand(0);
        auto it = map_Variable.find(arg);
        add_reb(it->second, v);
    }
    
    void parser_branch(Instruction* inst) {
        MDNode* MD = inst->getMetadata("dbg");
        DILocation* Loc = dyn_cast<DILocation>(MD);
        Value* cond = inst->getOperand(0);
        auto it = map_Variable.find(cond);
        if (it != map_Variable.end() && this->find_secret_leakeage(it->second)) {
                std::cout << "----------------------------------------------------" << std::endl;
                std::cout << it->first->getName().str() << std::endl;
                std::cout << " Leakage condition branch!!!" << " Line: " << Loc->getLine() << std::endl;
                std::cout << "----------------------------------------------------" << std::endl;
        }
    }
    //std::vector<std::vector<std::pair<Instruction*, bool>>> output_marks_ptr;
    void output_marks_ptrs() {
        std::vector<std::pair<Instruction*, bool>> prom;
        for (auto& arg : this->set_args) {
            for (auto& it : this->vectors_ptr) {
                Value* val = cast<Value>(it[0]);
                std::pair<Instruction*, Value*> Start_address = get_start_address(it[0]);
                size_t pos = Start_address.second->getName().str().find(".addr");
                if (pos != std::string::npos) {
                    std::string OldName = Start_address.second->getName().str().erase
					(pos, Start_address.second->getName().str().size());
                    if (OldName == arg->getName().str()) {
                        for (int i = 0; i < it.size(); i++) {
                            auto temp = map_Variable.find(cast<Value>(it[i]));
                            if (this->find_secret_leakeage(temp->second)) {
                                prom.push_back({ it[i],true });
                            }
                            else {
                                prom.push_back({ it[i],false });
                            }
                        }
                        output_marks_ptr.push_back(prom);
                    }
                }
            }
        }
    }

    bool find_ptr_with_start(Value* val, std::vector<std::vector<std::pair<Instruction*, bool>>> ptr_another_func) {
        if (vectors_ptr.empty())
            return false;
        bool flag_success = false;
        for (auto& x : vectors_ptr) {
            if (val == get_start_address(x[0]).second) {
                for (auto& another : ptr_another_func) {
                    if (x.size() == another.size()) {
                        for (int i = 0; i < x.size(); i++) {
                            bool flag_check_operand = true;
                            for (int j = 0; j < x[i]->getNumOperands(); j++) {
                                Value* op1 = x[i]->getOperand(j);
                                Value* op2 = another[i].first->getOperand(j);
                                if (op1 != op2) {
                                    flag_check_operand = false;
                                    break;
                                }
                            }
                            auto arg1 = map_Variable.find(x[i]);
                            std::cout << arg1->first->getName().str() << std::endl;
                            if (another[i].second) {
                                index_marks_variable.push_back(arg1->second);
                                std::cout << index_marks_variable[0] << std::endl;
                                std::cout << arg1->second << std::endl;
                                flag_success = true;
                            }
                            else {
                                std::cout << "Nothing" << std::endl;
                                flag_success = true;
                            }
                        }
                    }
                }
            }
        }
        return flag_success;
    }
    /*void output_marks_ptrs() {
        for (auto& arg : this->set_args) {
            std::cout << arg->getName().str() << std::endl;
            for (auto& it : this->vectors_ptr) {
                Value* val = cast<Value>(it[0]);
                std::cout << val->getName().str() << std::endl;
                //size_t n_pos = prom->getName().str().find("_secret");
                std::pair<Instruction*, Value*> Start_address = get_start_address(it[0]);
                std::cout << Start_address.second->getName().str() << std::endl;
                size_t pos = Start_address.second->getName().str().find(".addr");
                if (pos != std::string::npos) {
                    std::string OldName = Start_address.second->getName().str().erase(pos, Start_address.second->getName().str().size());
                    std::cout << OldName << std::endl;
                    if (OldName == arg->getName().str()) {
                        for (int i = 0; i < it.size(); i++) {
                            auto temp = map_Variable.find(cast<Value>(it[i]));
                            if (this->find_secret_leakeage(temp->second)) {
                                output_marks_ptr.push_back(true);//Gavno
                            }
                            else {
                                output_marks_ptr.push_back(false);
                            }
                        }
                    }
                }
            }
        }
    }*/

    void combining_pointers() {

    }

    std::vector<std::vector<int>> get_graph() {
        return this->matrx_graph;
    }

    std::unordered_map<Value*, int > get_Variable() {
        return this->map_Variable;
    }

    std::vector<int> get_index_marks_variable() {
        return this->index_marks_variable;
    }

    std::vector<bool> get_send_marks() {
        return this->send_marks_args;
    }

    std::unordered_set<Value*> get_args_variable() {
        return this->set_args;
    }
    /*std::vector<bool> get_output_marks_ptr() {
        return this->output_marks_ptr;
    }*/
    std::vector<std::vector<std::pair<Instruction*, bool>>> get_output_marks_ptr() {
        return this->output_marks_ptr;
    }
    std::vector<std::vector<Instruction*>> get_ptrs() {
        return this->vectors_ptr;
    }

    ~Analyse_func() {};
};

static std::set<std::string> kek = { "sprintf", "vsprintf","_snprintf",  "_vsnprintf","llvm.var.annotation","llvm.va_start","_vsprintf_l","llvm.va_end","_vsnprintf_l","__stdio_common_vsprintf",
            "__local_stdio_printf_options", "llvm.dbg.declare", "malloc", "free" };


std::pair<Instruction*, Value*> get_equality_address(Instruction* inst, Value* adrs) {
    Value* temp = inst->getOperand(0);

    while (!isa<AllocaInst>(temp)) {
        if (isa<LoadInst>(temp)) {

        }
        else if (isa<StoreInst>(temp)) {

        }
    }
}




Analyse_func get_analyse_func(Function* f, std::vector<bool> marks_args) {

    Analyse_func Block;
    Analyse_func Next_func;
    std::stack<CallInst*> stack_func;
    //add_argument_f(f, set_Variable, matrx_graph, marks_args, index_marks_variable);
    Block.add_arguments(f, marks_args);
   
    for (auto iter2 = f->getBasicBlockList().begin(); iter2 != f->getBasicBlockList().end(); iter2++) {
        BasicBlock& bb = *iter2;
        std::cout << "  BasicBlock: " << bb.getName().str() << std::endl;
        for (auto iter3 = bb.begin(); iter3 != bb.end(); iter3++) {
            Instruction& inst = *iter3;

            //Value* temp = cast<Value>(&inst);
            
            if (isa<AllocaInst>(&inst)) {
                std::cout << "Alloc memory ";
                Block.alloca_parser(&inst);
            }
            else if (isa<BinaryOperator>(&inst)) {
                std::cout << "Binary Operator ";
                Block.parser_binary_operator(&inst);
            }
            else if (isa<GetElementPtrInst>(&inst)) {
                //Надо все аргументы смотреть и обрабатывать на !!! утечку по кешу в будущем
                std::cout << "Start create ptr" << std::endl;
                Block.parser_getelementptr(&inst, iter3);
            }

            else if (isa<LoadInst>(&inst)) {
                std::cout << "Load data ";
                Block.parser_load(&inst);

            }
            else if (isa<StoreInst>(&inst)) {
                std::cout << "Copy data ";
                Block.parser_store(&inst);

            }
            else if (isa<ICmpInst>(&inst)) {
                std::cout << "Icminst" << std::endl;
                // причем тут целоисленное сравнение идет, да.
                //MDNode* MD = dyn_cast<Instruction>(NewVal)->getMetadata("dbg");
                //DILocation* Loc = dyn_cast<DILocation>(MD);
                Block.parser_Icmp(&inst);

            }
            else if (isa<BranchInst>(&inst)) {
                std::cout << "Condition branch " << std::endl;    
                if (!stack_func.empty() && Block.find_ptr_with_start(Block.find_start_value(stack_func.top()->getOperand(0)), Next_func.get_output_marks_ptr())) {
                    std::cout << "WOOOOOW" << std::endl;
                    stack_func.pop();
                }
                Block.parser_branch(&inst);

            }
            else if (isa<SExtInst>(&inst)) {
                std::cout << "sext" << std::endl;
                Block.parser_sext(&inst);
            }
            else if (CallInst* k = dyn_cast<CallInst>(&inst)) {
                auto check = kek.find(k->getCalledFunction()->getName().str());
                if (check != kek.end())
                    continue;

                Next_func = get_analyse_func(k->getCalledFunction(), marks_args);
                stack_func.push(k);
               // std::cout << temp.get_output_marks_ptr().size() << std::endl;
                for (int i = 0; i < k->getNumOperands() - 1; i++) {
                   //std::cout << k->getOperand(i)->getName().str() << std::endl;
                   Value* check =  Block.find_start_value(k->getOperand(i));
                   Block.find_ptr_with_start(check, Next_func.get_output_marks_ptr());
                   //std::cout << check->getName().str() << std::endl;
                   //std::vector<std::vector<Instruction*>> array = Block.get_ptrs();

                }

            }


        }
        std::cout << Next_func.get_output_marks_ptr().size() << std::endl;
        
    }
    //Block.print_graph();
    Block.output_marks_ptrs();
    Block.print_graph();
    for (int i = 0; i < Block.get_index_marks_variable().size(); i++) {
        std::cout << Block.get_index_marks_variable().size() << " ";
    }
    std::cout << std::endl;
    return Block;
}

int main(int argc, char* argv[])
{
   

        std::vector<std::vector<int>> matrx_graph;
        std::map<Value*, int> set_Variable;
        std::unordered_map<Value*, Instruction*> pointers_value_inst;
        //std::vector<std::vector<Instruction*>> vectors_ptr;
        //std::vector<ptr_array_mark> vectors_ptr;
        std::vector<std::string> mark_variable = { "a" };
        //std::set<Instruction> pointer_set;s
       // std::set<Instruction> set_pointers;

        StringRef filename = argv[1];
        LLVMContext context;
        SMDiagnostic Err;

        std::unique_ptr< Module > Mod = parseIRFile(argv[1], Err, context);

        Module* m = Mod.get();

    

        DataLayout* TD = new DataLayout(m);

    

    


        Module::GlobalListType& global_list = m->getGlobalList();

 

        Function* f = m->getFunction("main");
        std::vector<bool> marks;
        get_analyse_func(f, marks);
}
