Theory vfmTest1684[no_sig_docs]
Ancestors vfmTestDefs1684
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1684_0.nsv"];
val thyn = "vfmTestDefs1684";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
