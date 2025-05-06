open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0125Theory;
val () = new_theory "vfmTest0125";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0125") $ get_result_defs "vfmTestDefs0125";
val () = export_theory_no_docs ();
