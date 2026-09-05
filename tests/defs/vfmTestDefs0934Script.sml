Theory vfmTestDefs0934[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stMemoryTest/mem64kb_plus_31/mem64kb_plus_31.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stMemoryTest/mem64kb_plus_31/mem64kb_plus_31.json");
val defs = mapi (define_test "0934") tests;
