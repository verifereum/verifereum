Theory vfmTestDefs2357[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/static/state_tests/stStaticCall/static_log0_nonEmptyMem.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/static/state_tests/stStaticCall/static_log0_nonEmptyMem.json");
val defs = mapi (define_test "2357") tests;
