open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0658Theory;
val () = new_theory "vfmTest0658";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0658") $ get_result_defs "vfmTestDefs0658";
val () = export_theory_no_docs ();
