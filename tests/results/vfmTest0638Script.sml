open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0638Theory;
val () = new_theory "vfmTest0638";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0638") $ get_result_defs "vfmTestDefs0638";
val () = export_theory_no_docs ();
