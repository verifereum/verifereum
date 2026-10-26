Theory vfmTestDefs1681[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/ported_static/stMemoryTest/mload16bit_bound/mload16bit_bound.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/ported_static/stMemoryTest/mload16bit_bound/mload16bit_bound.json");
val defs = mapi (define_test "1681") tests;
