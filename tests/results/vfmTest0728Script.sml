open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0728Theory;
val () = new_theory "vfmTest0728";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0728") $ get_result_defs "vfmTestDefs0728";
val () = export_theory_no_docs ();
