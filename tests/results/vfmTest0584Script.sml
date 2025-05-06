open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0584Theory;
val () = new_theory "vfmTest0584";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0584") $ get_result_defs "vfmTestDefs0584";
val () = export_theory_no_docs ();
