Theory vfmTest2816[no_sig_docs]
Ancestors vfmTestDefs2816
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2816_0.nsv", "result2816_1.nsv", "result2816_2.nsv", "result2816_3.nsv"];
val thyn = "vfmTestDefs2816";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
