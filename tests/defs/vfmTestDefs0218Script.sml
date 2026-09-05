Theory vfmTestDefs0218[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/frontier/validation/transaction/bad_v_r_s.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/frontier/validation/transaction/bad_v_r_s.json");
val defs = mapi (define_test "0218") tests;
