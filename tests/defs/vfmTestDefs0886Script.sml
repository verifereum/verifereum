Theory vfmTestDefs0886[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stMemoryStressTest/mload_bounds2/mload_bounds2.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stMemoryStressTest/mload_bounds2/mload_bounds2.json");
val defs = mapi (define_test "0886") tests;
