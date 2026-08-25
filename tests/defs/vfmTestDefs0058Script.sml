Theory vfmTestDefs0058[no_sig_docs]
Libs vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/cancun/eip4844_blobs/test_fork_transition_excess_blob_gas_at_blob_genesis.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/cancun/eip4844_blobs/test_fork_transition_excess_blob_gas_at_blob_genesis.json");
val defs = mapi (define_test "0058") tests;
