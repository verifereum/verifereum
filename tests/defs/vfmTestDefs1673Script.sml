Theory vfmTestDefs1673[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/ported_static/stMemoryTest/mem64kb_single_byte_minus_32/mem64kb_single_byte_minus_32.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/ported_static/stMemoryTest/mem64kb_single_byte_minus_32/mem64kb_single_byte_minus_32.json");
val defs = mapi (define_test "1673") tests;
