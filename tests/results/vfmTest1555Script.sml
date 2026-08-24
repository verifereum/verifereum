Theory vfmTest1555[no_sig_docs]
Ancestors vfmTestDefs1555
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1555_0.nsv"];
val thyn = "vfmTestDefs1555";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
