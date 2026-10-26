Theory vfmTestDefs1487[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/ported_static/stEIP2930/coinbase_t2/coinbase_t2.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/ported_static/stEIP2930/coinbase_t2/coinbase_t2.json");
val defs = mapi (define_test "1487") tests;
