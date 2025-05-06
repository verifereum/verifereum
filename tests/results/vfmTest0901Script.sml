open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0901Theory;
val () = new_theory "vfmTest0901";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0901") $ get_result_defs "vfmTestDefs0901";
val () = export_theory_no_docs ();
