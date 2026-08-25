Theory vfmTestDefs1166[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/static/state_tests/stMemoryTest/mem32kb+1.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/static/state_tests/stMemoryTest/mem32kb+1.json");
val defs = mapi (define_test "1166") tests;
