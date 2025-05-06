open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0051Theory;
val () = new_theory "vfmTest0051";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0051") $ get_result_defs "vfmTestDefs0051";
val () = export_theory_no_docs ();
