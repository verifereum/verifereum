Theory vfmTestDefs1689[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/ported_static/stMemoryTest/sha3_dejavu/sha3_dejavu.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/ported_static/stMemoryTest/sha3_dejavu/sha3_dejavu.json");
val defs = mapi (define_test "1689") tests;
