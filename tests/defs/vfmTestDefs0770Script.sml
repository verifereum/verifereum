open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0770";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stCreateTest/CREATE_empty000CreateinInitCode_Transaction.json";
val defs = mapi (define_test "0770") tests;
val () = export_theory_no_docs ();
