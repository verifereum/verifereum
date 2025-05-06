open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0216Theory;
val () = new_theory "vfmTest0216";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0216") $ get_result_defs "vfmTestDefs0216";
val () = export_theory_no_docs ();
