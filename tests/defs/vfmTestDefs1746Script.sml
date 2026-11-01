Theory vfmTestDefs1746[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/ported_static/stPreCompiledContracts2/callcode_ecrecover0_gas3000/callcode_ecrecover0_gas3000.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/ported_static/stPreCompiledContracts2/callcode_ecrecover0_gas3000/callcode_ecrecover0_gas3000.json");
val defs = mapi (define_test "1746") tests;
