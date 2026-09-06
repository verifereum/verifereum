Theory vfmTestDefs0918[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stMemoryTest/mem32kb_single_byte/mem32kb_single_byte.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stMemoryTest/mem32kb_single_byte/mem32kb_single_byte.json");
val defs = mapi (define_test "0918") tests;
