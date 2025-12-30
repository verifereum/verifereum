Theory vfmTestDefs0840[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stCreateTest/CREATE_EContractCreateNEContractInInitOOG_Tr.json";
val defs = mapi (define_test "0840") tests;
