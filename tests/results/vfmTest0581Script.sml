open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0581Theory;
val () = new_theory "vfmTest0581";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0581") $ get_result_defs "vfmTestDefs0581";
val () = export_theory_no_docs ();
