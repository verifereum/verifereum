open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0225Theory;
val () = new_theory "vfmTest0225";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0225") $ get_result_defs "vfmTestDefs0225";
val () = export_theory_no_docs ();
