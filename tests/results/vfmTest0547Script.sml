open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0547Theory;
val () = new_theory "vfmTest0547";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0547") $ get_result_defs "vfmTestDefs0547";
val () = export_theory_no_docs ();
