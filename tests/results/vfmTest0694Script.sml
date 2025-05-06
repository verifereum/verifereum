open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0694Theory;
val () = new_theory "vfmTest0694";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0694") $ get_result_defs "vfmTestDefs0694";
val () = export_theory_no_docs ();
