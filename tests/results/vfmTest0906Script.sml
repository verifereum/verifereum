open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0906Theory;
val () = new_theory "vfmTest0906";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0906") $ get_result_defs "vfmTestDefs0906";
val () = export_theory_no_docs ();
