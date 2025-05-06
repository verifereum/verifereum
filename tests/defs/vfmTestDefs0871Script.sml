open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0871";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stCreateTest/CREATE_EContractCreateNEContractInInit_Tr.json";
val defs = mapi (define_test "0871") tests;
val () = export_theory_no_docs ();
