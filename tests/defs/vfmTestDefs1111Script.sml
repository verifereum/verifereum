Theory vfmTestDefs1111[no_sig_docs]
Libs vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/static/state_tests/stMemExpandingEIP150Calls/OOGinReturn.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/static/state_tests/stMemExpandingEIP150Calls/OOGinReturn.json");
val defs = mapi (define_test "1111") tests;
