Theory vfmTestDefs1682[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/ported_static/stMemoryTest/mload8bit_bound/mload8bit_bound.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/ported_static/stMemoryTest/mload8bit_bound/mload8bit_bound.json");
val defs = mapi (define_test "1682") tests;
