open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0718Theory;
val () = new_theory "vfmTest0718";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0718") $ get_result_defs "vfmTestDefs0718";
val () = export_theory_no_docs ();
