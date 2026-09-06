Theory vfmTestDefs0896[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stMemoryTest/calldatacopy_dejavu/calldatacopy_dejavu.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stMemoryTest/calldatacopy_dejavu/calldatacopy_dejavu.json");
val defs = mapi (define_test "0896") tests;
