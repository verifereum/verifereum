Theory vfmTestDefs0199[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/frontier/opcodes/calldatasize/calldatasize.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/frontier/opcodes/calldatasize/calldatasize.json");
val defs = mapi (define_test "0199") tests;
