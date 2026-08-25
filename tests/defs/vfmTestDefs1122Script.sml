Theory vfmTestDefs1122[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/static/state_tests/stMemoryStressTest/CREATE_Bounds3.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/static/state_tests/stMemoryStressTest/CREATE_Bounds3.json");
val defs = mapi (define_test "1122") tests;
