for(Module::iterator mi = _module->begin(); mi!=_module->end(); mi++){
    getAllMDNFunc(*mi);
}

void getAllMDNFunc(Function& F){
    SmallVector<pair<unsigned, MDNode*>, 4> MDForInst;
    for(Function::iterator BB = F.begin(),
                E = F.end(); BB!=E; ++BB){

        for(BasicBlock::iterator I = BB->begin(),
                E = BB->end(); I != E; ++I){
            //get the Metadata declared in the llvm intrinsic functions such as llvm.dbg.declare()
            if(CallInst* CI = dyn_cast<CallInst>(I)){
                if(Function *F = CI->getCalledFunction()){
                    if(F->getName().startswith("llvm.")){
                        for(unsigned i = 0, e = I->getNumOperands(); i!=e; ++i){
                            if(MDNode *N = dyn_cast_or_null<MDNode>(I->getOperand(i))){
                                createMetadataSlot(N);
                            }
                        }
                    }
                }
            }

            //Get all the mdnodes attached to each instruction
            I->getAllMetadata(MDForInst);
            for(unsigned i = 0, e = MDForInst.size(); i!=e; ++i){
                createMetadataSlot(MDForInst[i].second);
            }
            MDForInst.clear();
       }
    }
}//end getAllMDNFunc()

DenseMap<MDNode*, unsigned> _mdnMap; //Map for MDNodes.

void createMetadataSlot(MDNode *N){
    if(!N->isFunctionLocal()){
        mdn_iterator I = _mdnMap.find(N);
        if(I!=_mdnMap.end()){
            return;
        }
        //the map also stores the number of each metadata node. It is the same order as in the dumped bc file.
        unsigned DestSlot = _mdnNext++;
        _mdnMap[N] = DestSlot;
    }

    for (unsigned i = 0, e = N->getNumOperands(); i!=e; ++i){
        if(MDNode *Op = dyn_cast_or_null<MDNode>(N->getOperand(i))){
            createMetadataSlot(Op);
        }
    }
}
