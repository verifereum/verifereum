Theory vfmTest2823[no_sig_docs]
Ancestors vfmTestDefs2823
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2823_0.nsv", "result2823_1.nsv", "result2823_2.nsv", "result2823_3.nsv"];
val thyn = "vfmTestDefs2823";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
