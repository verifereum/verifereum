Theory vfmTestDefs0895[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stMemoryTest/buffer_src_offset/buffer_src_offset.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stMemoryTest/buffer_src_offset/buffer_src_offset.json");
val defs = mapi (define_test "0895") tests;
