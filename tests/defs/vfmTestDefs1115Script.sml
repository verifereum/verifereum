Theory vfmTestDefs1115[no_sig_docs]
Libs vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/static/state_tests/stMemoryStressTest/CALLCODE_Bounds4.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/static/state_tests/stMemoryStressTest/CALLCODE_Bounds4.json");
val defs = mapi (define_test "1115") tests;
