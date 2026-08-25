Theory vfmTestDefs0629[no_sig_docs]
Libs vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/static/state_tests/stCallCreateCallCodeTest/callOutput3partialFail.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/static/state_tests/stCallCreateCallCodeTest/callOutput3partialFail.json");
val defs = mapi (define_test "0629") tests;
