open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0459Theory;
val () = new_theory "vfmTest0459";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0459") $ get_result_defs "vfmTestDefs0459";
val () = export_theory_no_docs ();
