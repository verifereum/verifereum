open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0755";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stCreateTest/CREATE_ContractSuicideDuringInit_WithValueToItself.json";
val defs = mapi (define_test "0755") tests;
val () = export_theory_no_docs ();
