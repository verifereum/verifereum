open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0561";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stBugs/staticcall_createfails.json";
val defs = mapi (define_test "0561") tests;
val () = export_theory_no_docs ();
