open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0837";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stCreateTest/CREATE_ContractRETURNBigOffset.json";
val defs = mapi (define_test "0837") tests;
val () = export_theory_no_docs ();
