Theory vfmTest1120[no_sig_docs]
Ancestors vfmTestDefs1120
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1120_0.nsv", "result1120_1.nsv"];
val thyn = "vfmTestDefs1120";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
