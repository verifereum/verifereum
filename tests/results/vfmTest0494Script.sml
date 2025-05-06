open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0494Theory;
val () = new_theory "vfmTest0494";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0494") $ get_result_defs "vfmTestDefs0494";
val () = export_theory_no_docs ();
