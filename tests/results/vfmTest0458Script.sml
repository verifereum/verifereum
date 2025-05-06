open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0458Theory;
val () = new_theory "vfmTest0458";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0458") $ get_result_defs "vfmTestDefs0458";
val () = export_theory_no_docs ();
