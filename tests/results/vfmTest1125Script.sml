Theory vfmTest1125[no_sig_docs]
Ancestors vfmTestDefs1125
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1125_0.nsv", "result1125_1.nsv", "result1125_2.nsv"];
val thyn = "vfmTestDefs1125";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
