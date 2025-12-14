open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0030";
val tests = json_path_to_tests "../fixtures/blockchain_tests/cancun/eip4788_beacon_root/test_beacon_root_contract_calls.json";
val defs = mapi (define_test "0030") tests;
val () = export_theory_no_docs ();
