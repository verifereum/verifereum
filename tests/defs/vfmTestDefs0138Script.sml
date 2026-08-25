Theory vfmTestDefs0138[no_sig_docs]
Libs vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/frontier/opcodes/test_genesis_hash_available.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/frontier/opcodes/test_genesis_hash_available.json");
val defs = mapi (define_test "0138") tests;
