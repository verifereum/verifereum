open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0955Theory;
val () = new_theory "vfmTest0955";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0955") $ get_result_defs "vfmTestDefs0955";
val () = export_theory_no_docs ();
