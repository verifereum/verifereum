Theory vfmTestDefs1718[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/ported_static/stPreCompiledContracts2/call_ecrecover0_gas2999/call_ecrecover0_gas2999.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/ported_static/stPreCompiledContracts2/call_ecrecover0_gas2999/call_ecrecover0_gas2999.json");
val defs = mapi (define_test "1718") tests;
