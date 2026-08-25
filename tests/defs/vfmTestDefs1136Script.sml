Theory vfmTestDefs1136[no_sig_docs]
Libs vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/static/state_tests/stMemoryStressTest/MSTORE_Bounds2a.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/static/state_tests/stMemoryStressTest/MSTORE_Bounds2a.json");
val defs = mapi (define_test "1136") tests;
