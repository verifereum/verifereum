Theory vfmTestDefs0778[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/static/state_tests/stCodeCopyTest/ExtCodeCopyTestsParis.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/static/state_tests/stCodeCopyTest/ExtCodeCopyTestsParis.json");
val defs = mapi (define_test "0778") tests;
