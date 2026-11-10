Theory vfmTestDefs1613[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/ported_static/stMemoryStressTest/mload32bit_bound_return/mload32bit_bound_return.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/ported_static/stMemoryStressTest/mload32bit_bound_return/mload32bit_bound_return.json");
val defs = mapi (define_test "1613") tests;
