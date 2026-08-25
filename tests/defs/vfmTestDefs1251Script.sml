Theory vfmTestDefs1251[no_sig_docs]
Libs vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/static/state_tests/stPreCompiledContracts2/CALLCODEEcrecover0_Gas2999.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/static/state_tests/stPreCompiledContracts2/CALLCODEEcrecover0_Gas2999.json");
val defs = mapi (define_test "1251") tests;
