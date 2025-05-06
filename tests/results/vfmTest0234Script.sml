open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0234Theory;
val () = new_theory "vfmTest0234";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0234") $ get_result_defs "vfmTestDefs0234";
val () = export_theory_no_docs ();
