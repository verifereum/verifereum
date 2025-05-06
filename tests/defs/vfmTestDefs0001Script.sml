open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0001";
val tests = json_path_to_tests "../fixtures/blockchain_tests/berlin/eip2930_access_list/acl/access_list.json";
val defs = mapi (define_test "0001") tests;
val () = export_theory_no_docs ();
