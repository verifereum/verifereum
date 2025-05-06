open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1035Theory;
val () = new_theory "vfmTest1035";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1035") $ get_result_defs "vfmTestDefs1035";
val () = export_theory_no_docs ();
