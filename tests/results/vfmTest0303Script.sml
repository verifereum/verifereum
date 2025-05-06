open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0303Theory;
val () = new_theory "vfmTest0303";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0303") $ get_result_defs "vfmTestDefs0303";
val () = export_theory_no_docs ();
