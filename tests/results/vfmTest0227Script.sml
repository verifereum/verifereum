open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0227Theory;
val () = new_theory "vfmTest0227";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0227") $ get_result_defs "vfmTestDefs0227";
val () = export_theory_no_docs ();
