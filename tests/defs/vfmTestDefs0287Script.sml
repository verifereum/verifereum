open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0287";
val tests = json_path_to_tests "../fixtures/blockchain_tests/prague/eip7251_consolidations/test_system_contract_errors.json";
val defs = mapi (define_test "0287") tests;
val () = export_theory_no_docs ();
