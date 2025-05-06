open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0436Theory;
val () = new_theory "vfmTest0436";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0436") $ get_result_defs "vfmTestDefs0436";
val () = export_theory_no_docs ();
