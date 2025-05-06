open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0817Theory;
val () = new_theory "vfmTest0817";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0817") $ get_result_defs "vfmTestDefs0817";
val () = export_theory_no_docs ();
