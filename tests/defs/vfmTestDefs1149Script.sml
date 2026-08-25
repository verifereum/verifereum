Theory vfmTestDefs1149[no_sig_docs]
Libs vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/static/state_tests/stMemoryStressTest/static_CALL_Bounds3.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/static/state_tests/stMemoryStressTest/static_CALL_Bounds3.json");
val defs = mapi (define_test "1149") tests;
