open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0039";
val tests = json_path_to_tests "../fixtures/blockchain_tests/cancun/eip4788_beacon_root/test_no_beacon_root_contract_at_transition.json";
val defs = mapi (define_test "0039") tests;
val () = export_theory_no_docs ();
