open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0298Theory;
val () = new_theory "vfmTest0298";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0298") $ get_result_defs "vfmTestDefs0298";
val () = export_theory_no_docs ();
