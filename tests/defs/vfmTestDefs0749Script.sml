Theory vfmTestDefs0749[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stEIP2930/coinbase_t01/coinbase_t01.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stEIP2930/coinbase_t01/coinbase_t01.json");
val defs = mapi (define_test "0749") tests;
