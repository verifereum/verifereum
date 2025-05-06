open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0855Theory;
val () = new_theory "vfmTest0855";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0855") $ get_result_defs "vfmTestDefs0855";
val () = export_theory_no_docs ();
