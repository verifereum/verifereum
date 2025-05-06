open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0035Theory;
val () = new_theory "vfmTest0035";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0035") $ get_result_defs "vfmTestDefs0035";
val () = export_theory_no_docs ();
