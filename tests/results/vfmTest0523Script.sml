open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0523Theory;
val () = new_theory "vfmTest0523";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0523") $ get_result_defs "vfmTestDefs0523";
val () = export_theory_no_docs ();
