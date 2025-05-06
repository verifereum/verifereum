open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0107";
val tests = json_path_to_tests "../fixtures/blockchain_tests/constantinople/eip1014_create2/create_returndata/create2_return_data.json";
val defs = mapi (define_test "0107") tests;
val () = export_theory_no_docs ();
