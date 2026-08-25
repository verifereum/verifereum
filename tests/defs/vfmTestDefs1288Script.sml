Theory vfmTestDefs1288[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/static/state_tests/stPreCompiledContracts2/CallEcrecover0_completeReturnValue.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/static/state_tests/stPreCompiledContracts2/CallEcrecover0_completeReturnValue.json");
val defs = mapi (define_test "1288") tests;
