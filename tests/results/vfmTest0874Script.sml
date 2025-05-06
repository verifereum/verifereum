open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0874Theory;
val () = new_theory "vfmTest0874";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0874") $ get_result_defs "vfmTestDefs0874";
val () = export_theory_no_docs ();
