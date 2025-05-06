open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0905Theory;
val () = new_theory "vfmTest0905";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0905") $ get_result_defs "vfmTestDefs0905";
val () = export_theory_no_docs ();
