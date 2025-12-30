Theory vfmTestDefs2061[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stSpecialTest/JUMPDEST_AttackwithJump.json";
val defs = mapi (define_test "2061") tests;
