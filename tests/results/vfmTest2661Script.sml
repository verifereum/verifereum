Theory vfmTest2661[no_sig_docs]
Ancestors vfmTestDefs2661
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2661_0.nsv", "result2661_1.nsv", "result2661_2.nsv", "result2661_3.nsv"];
val thyn = "vfmTestDefs2661";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
