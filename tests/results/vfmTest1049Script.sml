Theory vfmTest1049[no_sig_docs]
Ancestors vfmTestDefs1049
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1049_0.nsv", "result1049_1.nsv", "result1049_2.nsv"];
val thyn = "vfmTestDefs1049";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
