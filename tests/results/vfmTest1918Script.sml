open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1918Theory;
val () = new_theory "vfmTest1918";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1918") $ get_result_defs "vfmTestDefs1918";
val () = export_theory_no_docs ();
