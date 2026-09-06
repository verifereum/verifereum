Theory vfmTestDefs1747[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stSolidityTest/recursive_create_contracts_create4_contracts/recursive_create_contracts_create4_contracts.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stSolidityTest/recursive_create_contracts_create4_contracts/recursive_create_contracts_create4_contracts.json");
val defs = mapi (define_test "1747") tests;
