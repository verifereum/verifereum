Theory vfmTestDefs0771[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stEIP4844_blobtransactions/opcode_blobhash_out_of_range/opcode_blobhash_out_of_range.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stEIP4844_blobtransactions/opcode_blobhash_out_of_range/opcode_blobhash_out_of_range.json");
val defs = mapi (define_test "0771") tests;
