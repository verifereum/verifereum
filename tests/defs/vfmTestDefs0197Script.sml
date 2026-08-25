Theory vfmTestDefs0197[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/osaka/eip7918_blob_reserve_price/test_blob_base_fee_with_bpo_transition.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/osaka/eip7918_blob_reserve_price/test_blob_base_fee_with_bpo_transition.json");
val defs = mapi (define_test "0197") tests;
