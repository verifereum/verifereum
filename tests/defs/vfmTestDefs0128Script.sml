Theory vfmTestDefs0128[no_sig_docs]
Libs vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/frontier/opcodes/test_call_large_offset_mstore.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/frontier/opcodes/test_call_large_offset_mstore.json");
val defs = mapi (define_test "0128") tests;
