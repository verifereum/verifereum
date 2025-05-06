open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0864Theory;
val () = new_theory "vfmTest0864";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0864") $ get_result_defs "vfmTestDefs0864";
val () = export_theory_no_docs ();
