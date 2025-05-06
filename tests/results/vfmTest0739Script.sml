open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0739Theory;
val () = new_theory "vfmTest0739";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0739") $ get_result_defs "vfmTestDefs0739";
val () = export_theory_no_docs ();
