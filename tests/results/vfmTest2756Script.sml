Theory vfmTest2756[no_sig_docs]
Ancestors vfmTestDefs2756
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2756_0.nsv", "result2756_1.nsv", "result2756_2.nsv", "result2756_3.nsv"];
val thyn = "vfmTestDefs2756";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
