open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0764Theory;
val () = new_theory "vfmTest0764";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0764") $ get_result_defs "vfmTestDefs0764";
val () = export_theory_no_docs ();
