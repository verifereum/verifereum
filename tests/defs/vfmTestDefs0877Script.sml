Theory vfmTestDefs0877[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stMemoryStressTest/mload32bit_bound/mload32bit_bound.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stMemoryStressTest/mload32bit_bound/mload32bit_bound.json");
val defs = mapi (define_test "0877") tests;
