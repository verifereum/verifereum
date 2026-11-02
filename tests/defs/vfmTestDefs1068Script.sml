Theory vfmTestDefs1068[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/frontier/opcodes/blockhash/genesis_hash_available.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/frontier/opcodes/blockhash/genesis_hash_available.json");
val defs = mapi (define_test "1068") tests;
