Theory vfmTestDefs1286[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/static/state_tests/stPreCompiledContracts2/CallEcrecover0_Gas2999.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/static/state_tests/stPreCompiledContracts2/CallEcrecover0_Gas2999.json");
val defs = mapi (define_test "1286") tests;
