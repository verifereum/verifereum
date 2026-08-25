Theory vfmTestDefs0111[no_sig_docs]
Libs vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/cancun/eip7516_blobgasfee/test_blobbasefee_before_fork.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/cancun/eip7516_blobgasfee/test_blobbasefee_before_fork.json");
val defs = mapi (define_test "0111") tests;
