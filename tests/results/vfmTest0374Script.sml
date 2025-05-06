open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0374Theory;
val () = new_theory "vfmTest0374";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0374") $ get_result_defs "vfmTestDefs0374";
val () = export_theory_no_docs ();
