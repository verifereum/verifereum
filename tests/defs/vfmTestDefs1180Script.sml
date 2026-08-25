Theory vfmTestDefs1180[no_sig_docs]
Libs vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/static/state_tests/stMemoryTest/mem32kb_singleByte-31.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/static/state_tests/stMemoryTest/mem32kb_singleByte-31.json");
val defs = mapi (define_test "1180") tests;
