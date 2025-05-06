open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0409Theory;
val () = new_theory "vfmTest0409";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0409") $ get_result_defs "vfmTestDefs0409";
val () = export_theory_no_docs ();
