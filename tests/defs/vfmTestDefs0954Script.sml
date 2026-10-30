Theory vfmTestDefs0954[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/cancun/eip4844_blobs/blobhash_opcode/blobhash_gas_cost.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/cancun/eip4844_blobs/blobhash_opcode/blobhash_gas_cost.json");
val defs = mapi (define_test "0954") tests;
