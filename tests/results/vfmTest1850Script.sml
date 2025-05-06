open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1850Theory;
val () = new_theory "vfmTest1850";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1850") $ get_result_defs "vfmTestDefs1850";
val () = export_theory_no_docs ();
