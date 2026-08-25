Theory vfmTest1500[no_sig_docs]
Ancestors vfmTestDefs1500
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1500_0.nsv"];
val thyn = "vfmTestDefs1500";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
