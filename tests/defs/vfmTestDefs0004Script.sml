open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0004";
val tests = json_path_to_tests "../fixtures/blockchain_tests/berlin/eip2930_access_list/test_repeated_address_acl.json";
val defs = mapi (define_test "0004") tests;
val () = export_theory_no_docs ();
