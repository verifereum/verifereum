open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0610Theory;
val () = new_theory "vfmTest0610";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0610") $ get_result_defs "vfmTestDefs0610";
val () = export_theory_no_docs ();
