// Check_two.cpp : Этот файл содержит функцию "main". Здесь начинается и заканчивается выполнение программы.
//

#include <iostream>
#include <string>
#include <set>
#include <vector>


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

using namespace llvm;


void handleDbgVariableIntrinsic(DbgVariableIntrinsic* DVI, Instruction& inst) {
    DILocalVariable* Var = DVI->getVariable();
    if (DVI->isAddressOfVariable()) {
        Value* Address = dyn_cast<DbgDeclareInst>(DVI)->getAddress();
        std::cout << Address << std::endl;
        errs() << "Describing an address of a variable in the stack " << Var->getName() << "\n";
        errs() << "Address in the IR: ";
        Address->print(dbgs(),true);
        MDNode* MD = DVI->getMetadata("dbg");
        DILocation* Loc = dyn_cast<DILocation>(MD);
        errs() << "At line " << Loc->getLine() << " of function " << DVI->getFunction()->getName() << "\n\n";
        /*Value* Address = dyn_cast<DbgDeclareInst>(DVI)->getAddress();
        errs() << "Describing an address of a variable in the stack " << Var->getName() << "\n";
        errs() << "Address in the IR: "; Address->dump();
        MDNode* MD = DVI->getMetadata("dbg");
        DILocation* Loc = dyn_cast<DILocation>(MD);
        errs() << "At line " << Loc->getLine() << " of function " << DVI->getFunction()->getName() << "\n\n";*/
    }
    else {
        Value* NewVal = dyn_cast<DbgValueInst>(DVI)->getValue();

        //We don't deal with Phi functions because they don't have a straight correspondent at the source code.
        if (isa<PHINode>(NewVal))
            return;

        errs() << "Variable " << Var->getName() << " assigned to a new value. \n";
        if (LoadInst* k = dyn_cast<LoadInst>(&inst)) {
            std::cout << "YEEEEEEEEEEEEEEEEEEEEEEEEEEEEES" << std::endl;
        }
        /*for (int i = 0; i < inst.getNumOperands(); i++) {
            Value* valchik = inst.getOperand(i);
            if (valchik->hasName()) {
                std::cout << std::string(valchik->getName());
            }
            else
                std::cout << valchik << std::endl;
        }*/
        if (Constant* C = dyn_cast<Constant>(NewVal)) {
            errs() << "It is a constant value.\n\n";
            if (C->isNullValue())
                errs() << "And it is null.\n\n";
        }
        else if (isa<UndefValue>(NewVal))
            errs() << "It is an undefined value\n\n";

        else if (isa<AllocaInst>(NewVal))
            errs() << "It is an address of a variable\n\n";

        else {
            if (Instruction* ValAsInst = dyn_cast<Instruction>(NewVal)) {
                if (ValAsInst->hasMetadata("dbg")) {
                    MDNode* MD = dyn_cast<Instruction>(NewVal)->getMetadata("dbg");
                    DILocation* Loc = dyn_cast<DILocation>(MD);
                    errs() << "At line " << Loc->getLine() << " of function " << DVI->getFunction()->getName() << "\n\n";
                }
            }
        }
    }
}


Value* find_by_index(int index, std::map<Value*, int> map_Variable) {
    for (auto& [key,value]: map_Variable) {
        if (value == index)
            return key;
    }
}

std::vector<std::vector<int>> add_v(std::vector<std::vector<int>>& vec, int size) {
    std::vector<std::vector<int>> new_vec;
    if (size == 0) {
        vec.resize(1);
        vec[0].push_back(0);
        return vec;
    }
    std::vector<int> prom_vec;
    for (int i = 0; i < size; i++) {
        
        vec[i].push_back(0);
        prom_vec.push_back(0);
        
    }
    prom_vec.push_back(0);
    vec.push_back(prom_vec);
    return vec;
}

bool find_path(const std::vector<std::vector<int>>& vec, int v1, int v2,std::vector<bool> visited) {
    if (v1 == v2){
        return true;
    }
    visited[v1] = true;
    for (int i = 0; i < vec.size(); i++) {
        if (vec[v1][i]) {
            if (!visited[i]) {
                if (find_path(vec,i, v2, visited))
                    return true;
            }
        }
    }
    return false;
}

void add_reb(std::vector<std::vector<int>>& vec, int a, int b) {
    vec[a][b] = 1;
    vec[b][a] = 1;
}

int main(int argc, char* argv[])
{   
    std::vector<std::vector<int>> matrx_graph;
    std::map<Value*, int> set_Variable;

    std::set<std::string> kek = {"sprintf", "vsprintf","_snprintf",  "_vsnprintf","llvm.var.annotation","llvm.va_start","_vsprintf_l","llvm.va_end","_vsnprintf_l","__stdio_common_vsprintf",
        "__local_stdio_printf_options"};

    if (argc != 2) {
        std::cerr << "Usage: " << argv[0] << " bitcode_filename" << std::endl;
        return 1;
    }
    //LLVMContext &context = getGlobalContext();
    StringRef filename = argv[1];
    LLVMContext context;
    SMDiagnostic Err;

    std::unique_ptr< Module > Mod = parseIRFile(argv[1], Err, context);

    Module* m = Mod.get();

    //for (auto iter1 = m->getFunction().begin(); )

    std::cout << argc << std::endl;
    std::cout << "Successfully read Module:" << std::endl;
    std::cout << " Name: " << m->getName().str() << std::endl;
    std::cout << " Target triple: " << m->getTargetTriple() << std::endl;


    Module::GlobalListType& global_list = m->getGlobalList();

    for (auto iter = m->getGlobalList().begin(); iter != m->getGlobalList().end(); iter++) {
        GlobalValue& G = *iter;
        std::cout << "GlobalVariable " << G.getName().str() << std::endl;
        std::cout << "GlobalValue " << G.getValueName() << std::endl;
        std::cout << "GlobalValueID" << G.getValueID() << std::endl;
   }


    for (auto iter1 = m->getFunctionList().begin(); iter1 != m->getFunctionList().end(); iter1++) {
        Function& f = *iter1;
        
        auto search = kek.find(f.getName().str());
        std::cout << " Function: " << f.getName().str() << std::endl;
        if (search != kek.end()) {
            std::cout << "Ne to" << std::endl;
            continue;
        }
        
        Argument* arg = f.getArg(0);
        std::cout << arg << std::endl;
        
        
        for (auto iter2 = f.getBasicBlockList().begin(); iter2 != f.getBasicBlockList().end(); iter2++) {
            BasicBlock& bb = *iter2;
            std::cout << "  BasicBlock: " << bb.getName().str() << std::endl;
            for (auto iter3 = bb.begin(); iter3 != bb.end(); iter3++) {
                Instruction& inst = *iter3;
                std::cout << "Type instruction" << inst.getOpcodeName() << std::endl;
                std::cout << "   Instruction " << inst.getName().str()<<"("<< &inst<<")" << " : " << inst.getOpcodeName() << std::endl;
                Value* temp = cast<Value>(&inst);

                if (AllocaInst* k = dyn_cast<AllocaInst>(&inst)) {
                    std::cout << "Alloc memory ";
                    //set_Variable.insert({ temp, set_Variable.size() });
                    //set_Variable[set_Variable.size()] = temp;
                    int v = set_Variable.size();
                    set_Variable.insert({ temp, v});
                    matrx_graph = add_v(matrx_graph,matrx_graph.size());
                    std::cout << temp->getName().str() << "(" << temp << ")";
                    //set_Variable.insert()
                    
                }
                else if (BinaryOperator* k = dyn_cast<BinaryOperator>(&inst)) {
                    std::cout << "Binary Operator ";
                    int v = set_Variable.size();
                    set_Variable.insert({ temp, v});
                    matrx_graph = add_v(matrx_graph, matrx_graph.size());


                    Value* arg1 = inst.getOperand(0);
                    Value* arg2 = inst.getOperand(1);

                    auto it = set_Variable.find(arg1);
                    if(it != set_Variable.end())
                        add_reb(matrx_graph, v, it->second);

                    it = set_Variable.find(arg2);
                    if (it != set_Variable.end())
                        add_reb(matrx_graph, v, it->second);


                    std::cout << arg1->getName().str() << "(" << arg1 << ") " << std::endl;
                    std::cout << arg2->getName().str() << "(" << arg2 << ") " << std::endl;
                    
                    
                }
                else if (GetElementPtrInst* k = dyn_cast<GetElementPtrInst>(&inst)) {
                    std::cout << "Get element ptr";
                    int v = set_Variable.size();
                    set_Variable.insert({ temp, v });
                    matrx_graph = add_v(matrx_graph, matrx_graph.size());
                    Value* arg = inst.getOperand(0);
                    auto it = set_Variable.find(arg);
                    ConstantInt* CI = cast< ConstantInt>(inst.getOperand(1));

                    std::cout << inst.getNumOperands();

                    std::cout << it->first->getName().str() << std::endl;
                    std::cout << it->second << std::endl;

                    std::cout << CI->getZExtValue() << std::endl;
                    
                    add_reb(matrx_graph, v, it->second);
                }

                else if (LoadInst* k = dyn_cast<LoadInst>(&inst)) {
                    std::cout << "Load data ";
                    
                    int v = set_Variable.size();
                    //set_Variable[temp] = v - 1;
                    set_Variable.insert({ temp, v });
                    matrx_graph = add_v(matrx_graph, matrx_graph.size());
                    Value* arg = inst.getOperand(0);
                    auto it =set_Variable.find(arg);
                    std::cout << it->first->getName().str() << std::endl;
                    std::cout << it->second << std::endl;
                    add_reb(matrx_graph, v, it->second);
                    //std::cout << temp << std::endl;
                    //std::cout << arg->getName().str() << "(" << arg << ")" << std::endl;;
                   


                }
                else if (StoreInst* k = dyn_cast<StoreInst>(&inst)) {
                    std::cout << "Copy data ";
                    Value* arg1 = inst.getOperand(0);
                    auto it = set_Variable.find(arg1);
                    if (it == set_Variable.end())
                        continue;
                    Value* arg2 = inst.getOperand(1);

                    int v = set_Variable.size();
                    auto it1 = set_Variable.find(arg1);
                    auto it2 = set_Variable.find(arg2);
  

                    add_reb(matrx_graph, it1->second, it2->second);

                    std::cout << arg1->getName().str() << "(" << arg1 << ") " << std::endl;
                    std::cout << arg2->getName().str() << "(" << arg2 << ") " << std::endl;

                    //std::cout << k->getName().str();
                }
                else if (ICmpInst* k = dyn_cast<ICmpInst>(&inst)) {
                    //Типо ИФФ, тут уже работа будет с утечками, причем тут целоисленное сравнение идет, да.
                    //MDNode* MD = dyn_cast<Instruction>(NewVal)->getMetadata("dbg");
                    //DILocation* Loc = dyn_cast<DILocation>(MD);
                    bool flag_leak = false;
            
                    MDNode* MD = inst.getMetadata("dbg");
                    DILocation* Loc = dyn_cast<DILocation>(MD);
                    std::cout << "Condition data" << std::endl;
                    Value* arg1 = inst.getOperand(0);
                    auto it = set_Variable.find(arg1);
                    std::cout << " ------------------------------------------------------ " << std::endl;
                    if (it != set_Variable.end()) {
                        std::vector<bool> bl;
                        bl.resize(matrx_graph.size());
                        if (find_path(matrx_graph, it->second, 1, bl)) {
                            std::cout << "Karaul, utechka zopi!!!" << " po stroke nomer " << Loc->getLine();
                        }
                    }
                    Value* arg2 = inst.getOperand(1);
                    it = set_Variable.find(arg2);
                    if (it != set_Variable.end()) {
                        std::vector<bool> bl;
                        bl.resize(matrx_graph.size());
                        if (find_path(matrx_graph, it->second, 1, bl)) {
                            std::cout << " Karaul, utechka zopi!!!" << " po stroke nomer " << Loc->getLine();
                        }
                    }



                    
                    std::cout << arg1->getName().str() << "(" << arg1 << ") " << std::endl;
                    std::cout << arg2->getName().str() << "(" << arg2<< ") " << std::endl;
                   
                    std::cout << " ------------------------------------------------------ " << std::endl;



                }
                else {
                    std::cout << std::endl;
                    continue;
                } 
                
            }
        }


    }
    std::cout << std::endl;
    for (int i = 0; i < matrx_graph.size(); i++) {
        Value* arg1 = find_by_index(i, set_Variable);
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
    std::vector<bool> visited;
    visited.resize(matrx_graph.size());
    if (find_path(matrx_graph, 0, 5, visited)) {
        std::cout << "URAAAAA";
    }
    else {
        std::cout << "meh";
    }
}
