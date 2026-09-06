Theory vfmTestDefs0881[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stMemoryStressTest/mload32bit_bound_return2/mload32bit_bound_return2.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stMemoryStressTest/mload32bit_bound_return2/mload32bit_bound_return2.json");
val defs = mapi (define_test "0881") tests;
