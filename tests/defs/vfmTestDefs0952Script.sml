Theory vfmTestDefs0952[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stMemoryTest/mstroe8_dejavu/mstroe8_dejavu.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stMemoryTest/mstroe8_dejavu/mstroe8_dejavu.json");
val defs = mapi (define_test "0952") tests;
