open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1701Theory;
val () = new_theory "vfmTest1701";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1701") $ get_result_defs "vfmTestDefs1701";
val () = export_theory_no_docs ();
