Theory vfmTestDefs0137[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/cancun/eip7516_blobgasfee/blobgasfee_opcode/blobbasefee_out_of_gas.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/cancun/eip7516_blobgasfee/blobgasfee_opcode/blobbasefee_out_of_gas.json");
val defs = mapi (define_test "0137") tests;
