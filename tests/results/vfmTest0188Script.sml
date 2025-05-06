open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0188Theory;
val () = new_theory "vfmTest0188";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0188") $ get_result_defs "vfmTestDefs0188";
val () = export_theory_no_docs ();
