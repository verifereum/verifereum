open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0315Theory;
val () = new_theory "vfmTest0315";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0315") $ get_result_defs "vfmTestDefs0315";
val () = export_theory_no_docs ();
