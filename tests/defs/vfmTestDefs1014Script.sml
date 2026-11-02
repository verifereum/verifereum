Theory vfmTestDefs1014[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/cancun/eip7516_blobgasfee/blobgasfee_opcode/blobbasefee_stack_overflow.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/cancun/eip7516_blobgasfee/blobgasfee_opcode/blobbasefee_stack_overflow.json");
val defs = mapi (define_test "1014") tests;
