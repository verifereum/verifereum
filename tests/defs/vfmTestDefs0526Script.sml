Theory vfmTestDefs0526[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stAttackTest/ContractCreationSpam.json";
val defs = mapi (define_test "0526") tests;
