Theory vfmTestDefs0194[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/frontier/opcodes/call/call_large_offset_mstore.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/frontier/opcodes/call/call_large_offset_mstore.json");
val defs = mapi (define_test "0194") tests;
