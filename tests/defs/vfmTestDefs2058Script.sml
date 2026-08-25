Theory vfmTestDefs2058[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/static/state_tests/stSolidityTest/TestStructuresAndVariabless.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/static/state_tests/stSolidityTest/TestStructuresAndVariabless.json");
val defs = mapi (define_test "2058") tests;
