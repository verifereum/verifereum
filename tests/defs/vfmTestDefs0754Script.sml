open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0754";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stCreateTest/CREATE_ContractSuicideDuringInit_WithValue.json";
val defs = mapi (define_test "0754") tests;
val () = export_theory_no_docs ();
