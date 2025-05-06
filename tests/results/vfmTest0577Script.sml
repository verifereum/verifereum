open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0577Theory;
val () = new_theory "vfmTest0577";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0577") $ get_result_defs "vfmTestDefs0577";
val () = export_theory_no_docs ();
