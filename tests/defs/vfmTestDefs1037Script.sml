Theory vfmTestDefs1037[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stPreCompiledContracts2/callcode_ripemd160_2/callcode_ripemd160_2.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stPreCompiledContracts2/callcode_ripemd160_2/callcode_ripemd160_2.json");
val defs = mapi (define_test "1037") tests;
