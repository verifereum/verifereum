open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0757";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stCreateTest/CREATE_EContractCreateNEContractInInitOOG_Tr.json";
val defs = mapi (define_test "0757") tests;
val () = export_theory_no_docs ();
