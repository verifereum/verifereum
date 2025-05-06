open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0796Theory;
val () = new_theory "vfmTest0796";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0796") $ get_result_defs "vfmTestDefs0796";
val () = export_theory_no_docs ();
