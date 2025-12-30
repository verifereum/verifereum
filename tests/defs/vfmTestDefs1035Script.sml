Theory vfmTestDefs1035[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stHomesteadSpecific/contractCreationOOGdontLeaveEmptyContract.json";
val defs = mapi (define_test "1035") tests;
