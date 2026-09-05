Theory vfmTestDefs0922[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stMemoryTest/mem32kb_single_byte_minus_33/mem32kb_single_byte_minus_33.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stMemoryTest/mem32kb_single_byte_minus_33/mem32kb_single_byte_minus_33.json");
val defs = mapi (define_test "0922") tests;
