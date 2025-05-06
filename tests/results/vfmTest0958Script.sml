open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0958Theory;
val () = new_theory "vfmTest0958";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0958") $ get_result_defs "vfmTestDefs0958";
val () = export_theory_no_docs ();
