open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1936Theory;
val () = new_theory "vfmTest1936";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1936") $ get_result_defs "vfmTestDefs1936";
val () = export_theory_no_docs ();
