Theory vfmTestDefs1036[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stHomesteadSpecific/contractCreationOOGdontLeaveEmptyContractViaTransaction.json";
val defs = mapi (define_test "1036") tests;
