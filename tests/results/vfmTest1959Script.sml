open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1959Theory;
val () = new_theory "vfmTest1959";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1959") $ get_result_defs "vfmTestDefs1959";
val () = export_theory_no_docs ();
