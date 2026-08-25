Theory vfmTestDefs0917[no_sig_docs]
Libs vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/static/state_tests/stEIP150Specific/Transaction64Rule_integerBoundaries.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/static/state_tests/stEIP150Specific/Transaction64Rule_integerBoundaries.json");
val defs = mapi (define_test "0917") tests;
