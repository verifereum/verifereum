open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1955Theory;
val () = new_theory "vfmTest1955";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1955") $ get_result_defs "vfmTestDefs1955";
val () = export_theory_no_docs ();
