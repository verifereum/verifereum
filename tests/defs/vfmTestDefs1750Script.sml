Theory vfmTestDefs1750[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/ported_static/stPreCompiledContracts2/callcode_ripemd160_0/callcode_ripemd160_0.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/ported_static/stPreCompiledContracts2/callcode_ripemd160_0/callcode_ripemd160_0.json");
val defs = mapi (define_test "1750") tests;
